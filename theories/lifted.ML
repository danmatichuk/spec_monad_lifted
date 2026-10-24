(*  Lifted expressions and assignments for spec_monad programs.
    See docs/lifted_syntax_design.md.
*)

signature LIFTED =
sig
  val add_handle: string * string * string -> Context.generic -> Context.generic
  val field_attr: (string * string) -> attribute
  val handle_attr: (string * string) -> attribute
  val record_attr: typ -> attribute
  val index_attr: (string * string) -> attribute
  val region_tr: term list -> term
  val assign_tr: term list -> term
  val do_assign_ast_tr: Ast.ast list -> Ast.ast
  val do_assign_final_ast_tr: Ast.ast list -> Ast.ast
  val check: term list -> Proof.context -> (term list * Proof.context) option
  val uncheck: Proof.context -> term list -> term list
  val lift_handle_tr': term list -> term
  val lift_tr': term list -> term
  val assign_tr': term list -> term
end;

structure Lifted: LIFTED =
struct

(** registry of locations **)

(* fields: getter :: 's => 'v  |->  updater :: ('v => 'v) => 's => 's
   handles: handle type 'h  |->  (getter :: 'h => 's => 'v, updater :: 'h => ('v => 'v) => 's => 's)
   indexes: reader :: 'c => 'i => 'v  |->  updater :: 'c => 'i => 'v => 'c  (assignable "c ! i") *)
structure Locations = Generic_Data
(
  type T =
    {fields: string Symtab.table, handles: (string * string) Symtab.table, indexes: string Symtab.table};
  val empty = {fields = Symtab.empty, handles = Symtab.empty, indexes = Symtab.empty};
  fun merge ({fields = f1, handles = h1, indexes = i1}, {fields = f2, handles = h2, indexes = i2}) =
    {fields = Symtab.merge (K true) (f1, f2), handles = Symtab.merge (K true) (h1, h2),
     indexes = Symtab.merge (K true) (i1, i2)};
);

fun add_field (get, upd) = Locations.map (fn {fields, handles, indexes} =>
  {fields = Symtab.update (get, upd) fields, handles = handles, indexes = indexes});

fun add_handle (tyname, get, upd) = Locations.map (fn {fields, handles, indexes} =>
  {fields = fields, handles = Symtab.update (tyname, (get, upd)) handles, indexes = indexes});

fun add_index (rd, upd) = Locations.map (fn {fields, handles, indexes} =>
  {fields = fields, handles = handles, indexes = Symtab.update (rd, upd) indexes});

fun fields ctxt = #fields (Locations.get (Context.Proof ctxt));
fun handles ctxt = #handles (Locations.get (Context.Proof ctxt));
fun indexes ctxt = #indexes (Locations.get (Context.Proof ctxt));

fun index_updater ctxt rd = Symtab.lookup (indexes ctxt) rd;
fun index_reader ctxt u = Symtab.get_first (fn (r, u') => if u = u' then SOME r else NONE) (indexes ctxt);

fun field_updater ctxt c = Symtab.lookup (fields ctxt) c;
fun field_of_updater ctxt u =
  Symtab.get_first (fn (g, u') => if u = u' then SOME g else NONE) (fields ctxt);

fun lookup_handle ctxt (Type (n, [])) = Symtab.lookup (handles ctxt) n
  | lookup_handle _ _ = NONE;

fun find_handle ctxt pred =
  Symtab.get_first (fn (n, gu) => if pred gu then SOME (n, gu) else NONE) (handles ctxt);

fun is_getter ctxt c = is_some (find_handle ctxt (fn (g, _) => g = c));
fun is_updater ctxt c = is_some (find_handle ctxt (fn (_, u) => u = c));
fun updater_of_getter ctxt c = Option.map (snd o snd) (find_handle ctxt (fn (g, _) => g = c));


(* declaration attributes *)

fun reg_error msg = error ("Lifted: " ^ msg);

(* constant types may come with free or with schematic type variables *)
val varifyT = Term.map_atyps (fn TFree (a, S) => TVar ((a, 0), S) | T => T);

(* the constant's type unifies with T (T may contain schematic type variables) *)
fun check_type ctxt what c T =
  let
    val thy = Proof_Context.theory_of ctxt;
    val U = varifyT (Sign.the_const_type thy c);
    val T' = Logic.incr_tvar (maxidx_of_typ U + 1) T;
  in
    if can (Sign.typ_unify thy (U, T')) (Vartab.empty, maxidx_of_typ T')
    then () else reg_error (what ^ " " ^ quote c ^ " must have type " ^ Syntax.string_of_typ ctxt T)
  end;

fun checked_field context (get, upd) =
  let
    val ctxt = Context.proof_of context;
    val thy = Context.theory_of context;
    val (S, V) =
      (case varifyT (Sign.the_const_type thy get) of
        Type ("fun", [S, V]) => (S, V)
      | _ => reg_error ("field getter " ^ quote get ^ " must have type 's \<Rightarrow> 'v"));
    val _ = check_type ctxt "field updater" upd ((V --> V) --> S --> S);
  in add_field (get, upd) context end;

fun checked_handle context (get, upd) =
  let
    val ctxt = Context.proof_of context;
    val thy = Context.theory_of context;
    val (H, S, V) =
      (case Sign.the_const_type thy get of
        Type ("fun", [H, Type ("fun", [S, V])]) => (H, S, V)
      | _ => reg_error ("handle getter " ^ quote get ^ " must have type 'h \<Rightarrow> 's \<Rightarrow> 'v"));
    val tyname =
      (case H of
        Type (n, []) => n
      | _ => reg_error ("the handle type " ^ Syntax.string_of_typ ctxt H ^ " must be a type constant"));
    val _ = check_type ctxt "handle updater" upd (varifyT (H --> (V --> V) --> S --> S));
  in add_handle (tyname, get, upd) context end;

(* all fields of a record (including parents), with the updaters the record package defines *)
fun checked_record context T =
  let
    val thy = Context.theory_of context;
    val ctxt = Context.proof_of context;
    val not_record = fn () => reg_error ("not a record type: " ^ Syntax.string_of_typ ctxt T);
    val (flds, _) = Record.get_recT_fields thy T handle TYPE _ => not_record ();
    fun lhs_head th =
      (case Thm.prop_of th of
        Const (@{const_name Pure.eq}, _) $ l $ _ => Term.head_of l
      | t => Term.head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop t))));
    val updaters =
      Record.dest_recTs T
      |> maps (fn (ext, _) =>
          (case Record.get_info thy (Long_Name.qualifier ext) of
            SOME info => #update_defs info
          | NONE => not_record ()))
      |> map_filter (try (fst o dest_Const o lhs_head));
    fun pair (sel, _) =
      let val upd = sel ^ Record.updateN in
        if member (op =) updaters upd then (sel, upd)
        else reg_error ("no record updater for " ^ quote sel)
      end;
  in fold (fn fld => fn context => checked_field context (pair fld)) flds context end;

fun checked_index context (rd, upd) =
  let
    val ctxt = Context.proof_of context;
    val thy = Context.theory_of context;
    val (C, I, V) =
      (case varifyT (Sign.the_const_type thy rd) of
        Type ("fun", [C, Type ("fun", [I, V])]) => (C, I, V)
      | _ => reg_error ("index reader " ^ quote rd ^ " must have type 'c \<Rightarrow> 'i \<Rightarrow> 'v"));
    val _ = check_type ctxt "index updater" upd (C --> I --> V --> C);
  in add_index (rd, upd) context end;

fun index_attr ru = Thm.declaration_attribute (fn _ => fn context => checked_index context ru);

fun field_attr gu = Thm.declaration_attribute (fn _ => fn context => checked_field context gu);
fun handle_attr gu = Thm.declaration_attribute (fn _ => fn context => checked_handle context gu);
fun record_attr T = Thm.declaration_attribute (fn _ => fn context => checked_record context T);

fun is_monadT (Type (@{type_name spec_monad}, [_, _, _])) = true
  | is_monadT _ = false;

fun monad_stateT (Type (@{type_name spec_monad}, [_, _, s])) = s
  | monad_stateT T = raise TYPE ("monad_stateT", [T], []);

val marker_names = [@{const_name LIFTQ}, @{const_name LREGION}, @{const_name LASSIGN}];


(** parsing: polymorphic markers only **)

fun liftq t = Const (@{const_syntax LIFTQ}, dummyT) $ t;

fun is_ident (Free _) = true
  | is_ident (Const (@{syntax_const "_constrain"}, _) $ Free _ $ _) = true
  | is_ident _ = false;

val constraint_consts = [@{syntax_const "_constrain"}, @{syntax_const "_constrainAbs"}, "_type_constraint_"];
fun is_constraint c = member (op =) constraint_consts c;

(* like strip_comb, but a constrained head "_constrain f pos" stays atomic *)
fun strip_app (t as Const (c, _) $ _ $ _) =
      if is_constraint c then (t, []) else let val (h, args) = strip_app (fst (dest_comb t)) in (h, args @ [snd (dest_comb t)]) end
  | strip_app (t1 $ t2) = let val (h, args) = strip_app t1 in (h, args @ [t2]) end
  | strip_app t = (t, []);

fun wrap t =
  if is_ident t then liftq t
  else
    (case t of
      Const (@{const_syntax LIFTQ}, _) $ _ => t
    | Const (c, T) $ u $ ty => if is_constraint c then Const (c, T) $ wrap u $ ty else wrap_app t
    | _ $ _ => wrap_app t
    | Abs (x, T, b) => Abs (x, T, wrap b)
    | _ => t)
and wrap_app t = let val (h, args) = strip_app t in list_comb (wrap_head h, map wrap args) end
and wrap_head (h as Abs _) = wrap h
  | wrap_head (h as Const (c, T) $ u $ ty) =
      if is_constraint c then Const (c, T) $ wrap_head u $ ty else h
  | wrap_head h = h;

fun region_tr [t] = Const (@{const_syntax LREGION}, dummyT) $ wrap t
  | region_tr ts = raise TERM ("region_tr", ts);

fun do_assign_ast_tr [l, e] =
      Ast.Appl [Ast.Constant @{syntax_const "_do_then"}, Ast.Appl [Ast.Constant @{syntax_const "_lassign"}, l, e]]
  | do_assign_ast_tr asts = raise Ast.AST ("do_assign_ast_tr", asts);

fun do_assign_final_ast_tr [l, e] =
      Ast.Appl [Ast.Constant @{syntax_const "_do_final"}, Ast.Appl [Ast.Constant @{syntax_const "_lassign"}, l, e]]
  | do_assign_final_ast_tr asts = raise Ast.AST ("do_assign_final_ast_tr", asts);

(* an lvalue: a location, or a reader applied to an lvalue (container argument first); only the
   location at the base is marked, indices are ordinary expressions *)
fun lvalue t =
  if is_ident t then liftq t
  else
    (case t of
      Const (c, T) $ u $ ty =>
        if is_constraint c then Const (c, T) $ lvalue u $ ty else lvalue_app t
    | _ $ _ => lvalue_app t
    | _ => t)
and lvalue_app t =
  (case strip_app t of
    (h, a :: args) => list_comb (h, lvalue a :: args)
  | _ => t);

fun assign_tr [l, e] = Const (@{const_syntax LASSIGN}, dummyT) $ lvalue l $ e
  | assign_tr ts = raise TERM ("assign_tr", ts);


(** check phase **)

fun has_markers t = Term.exists_Const (fn (c, _) => member (op =) marker_names c) t;

fun untyped t =
  Term.exists_subterm
    (fn Const (c, T) => member (op =) marker_names c andalso Term.exists_subtype (fn U => U = dummyT) T
      | _ => false) t;

fun err ctxt msg ts = error (cat_lines (msg :: map (Syntax.string_of_term ctxt) ts));

fun unif thy (T, U) env = SOME (Sign.typ_unify thy (T, U) env) handle Type.TUNIFY => NONE;

(* step 1: LIFTQ t  ~>  t  |  LIFT g *)
fun resolve_liftq ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun lift g S V = Const (@{const_name LIFT}, (S --> V) --> V) $ g;
    fun decide T x (env as (tyenv, _)) =
      let
        val Ta = Envir.norm_type tyenv (domain_type T);
        val Tb = Envir.norm_type tyenv (range_type T);
        fun identity () =
          (case unif thy (Ta, Tb) env of
            SOME env' => (x, env')
          | NONE => err ctxt ("Lifted expression: cannot use a value of type " ^
              Syntax.string_of_typ ctxt Ta ^ " as " ^ Syntax.string_of_typ ctxt Tb) [x]);
      in
        if Ta = Tb then (x, env)
        else
          (case lookup_handle ctxt Ta of
            SOME (get, _) =>
              let
                val getT = Sign.the_const_type thy get;
                val S = domain_type (range_type getT) and V = range_type (range_type getT);
              in
                (case unif thy (Tb, V) env of
                  SOME env' => (lift (Const (get, getT) $ x) S V, env')
                | NONE => identity ())
              end
          | NONE =>
              (case (x, Ta) of
                (Const (c, _), Type ("fun", [S, V])) =>
                  if is_some (field_updater ctxt c) then
                    (case unif thy (Tb, V) env of
                      SOME env' => (lift x S V, env')
                    | NONE => identity ())
                  else identity ()
              | _ => identity ()))
      end;
    fun go (Const (@{const_name LIFTQ}, T) $ x) env = decide T x env
      | go (t1 $ t2) env = let val (a, env) = go t1 env; val (b, env) = go t2 env in (a $ b, env) end
      | go (Abs (n, T, b)) env = let val (b, env) = go b env in (Abs (n, T, b), env) end
      | go t env = (t, env);
  in go end;

fun dest_lift (Const (@{const_name LIFT}, T) $ g) = SOME (g, domain_type (domain_type T), range_type T)
  | dest_lift _ = NONE;

(* updater of a getter: handle getter "get h" or record selector *)
fun updater ctxt g V S =
  let val thy = Proof_Context.theory_of ctxt in
    (case g of
      Const (get, _) $ h =>
        (case updater_of_getter ctxt get of
          SOME upd => Const (upd, Sign.the_const_type thy upd) $ h
        | NONE => err ctxt "Lifted: not a location" [g])
    | Const (c, _) =>
        (case field_updater ctxt c of
          SOME u => Const (u, (V --> V) --> S --> S)
        | NONE => err ctxt "Lifted: not a location" [g])
    | _ => err ctxt "Lifted: not a location" [g])
  end;

fun mk_modify ctxt MT g V S f env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val env = (case unif thy (monad_stateT MT, S) env of SOME env => env
      | NONE => err ctxt "Lifted: state type mismatch" [g]);
    val env = (case MT of Type (_, [_, R, _]) =>
        (case unif thy (R, HOLogic.unitT) env of SOME env => env
        | NONE => err ctxt "Lifted: an update returns unit" [g])
      | _ => env);
  in (Const (@{const_name modify}, (S --> S) --> MT) $ (updater ctxt g V S $ f), env) end;

(* steps 2 and 3: LASSIGN and LREGION *)
(* The new value of the base location for "lv := e": an assignment through a path of readers
   becomes nested updates, e.g. "L ! i ! j := e" ~> L := upd L i (upd (L ! i) j e).
   NONE if lv is not (yet) an lvalue, e.g. while an overloaded reader is unresolved. *)
fun dest_lvalue ctxt lv =
  (case dest_lift lv of
    SOME (g, S, V) => SOME (g, S, V, fn _ => fn x => x)
  | NONE =>
      (case lv of
        Const (rd, T) $ c $ i =>
          (case (index_updater ctxt rd, dest_lvalue ctxt c) of
            (SOME upd, SOME (g, S, V, assign_c)) =>
              let
                val (C, I, W) = (domain_type T, domain_type (range_type T), range_type (range_type T));
                (* current value of the path c, in terms of the base value b *)
                fun value_of b (Const (rd', T') $ c' $ i') = Const (rd', T') $ value_of b c' $ i'
                  | value_of b _ = b;
              in
                SOME (g, S, V, fn b => fn x =>
                  assign_c b (Const (upd, C --> I --> W --> C) $ value_of b c $ i $ x))
              end
          | _ => NONE)
      | _ => NONE));

(* steps 2 and 3: LASSIGN; LREGION *)
fun resolve_stmts ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun assign T l e env =
      (case dest_lvalue ctxt l of
        SOME (g, S, V, new_value) =>
          let val b = Free ("lifted_base__", V)
          in mk_modify ctxt (range_type (range_type T)) g V S
              (Abs ("v", V, Term.abstract_over (b, Term.incr_boundvars 1 (new_value b e)))) env
          end
      | NONE => (Const (@{const_name LASSIGN}, T) $ l $ e, env));   (* retried in a later round *)
    fun region T x (env as (tyenv, _)) =
      let
        val Ta = Envir.norm_type tyenv (domain_type T);
        val Tb = Envir.norm_type tyenv (range_type T);
      in
        if is_monadT Tb andalso not (is_monadT Ta) andalso not (is_TVar Ta) then
          err ctxt "Lifted: a pure \<langle>\<dots>\<rangle> is not a statement; assign with :=" [x]
        else
          (case unif thy (Ta, Tb) env of
            SOME env' => (x, env')
          | NONE => err ctxt "Lifted: ill-typed region" [x])
      end;
    fun go Ts (Const (@{const_name LASSIGN}, T) $ l $ e) env =
          let val (l, env) = go Ts l env; val (e, env) = go Ts e env in assign T l e env end
      | go Ts (Const (@{const_name LREGION}, T) $ x) env =
          let val (x, env) = go Ts x env in region T x env end
      | go Ts (t1 $ t2) env = let val (a, env) = go Ts t1 env; val (b, env) = go Ts t2 env in (a $ b, env) end
      | go Ts (Abs (n, T, b)) env = let val (b, env) = go (T :: Ts) b env in (Abs (n, T, b), env) end
      | go _ t env = (t, env);
  in go [] end;

(* step 4: place reads at the smallest enclosing monadic subterm *)
fun val_name (Const (_, _) $ Free (x, _)) = x ^ "_val"
  | val_name (Const (c, _)) = Long_Name.base_name c ^ "_val"
  | val_name _ = "val";

(* State threaded through placement: fresh names for the placeholder variables and the type
   environment (unification of a getter's state type with the placement point's). *)
fun place_reads ctxt t env =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun fresh (names, env) = let val (v, names') = Name.variant "lifted" names in (v, (names', env)) end;
    fun norm (_, (tyenv, _)) T = Envir.norm_type tyenv T;
    (* split the pending reads into those of state type S (unifying) and the others *)
    fun split_state S pend (names, env) =
      let
        val (here, rest, env) = fold (fn r as (g, _, _, _) => fn (here, rest, env) =>
            (case unif thy (domain_type (Envir.norm_type (fst env) (fastype_of g)), S) env of
              SOME env' => (here @ [r], rest, env')
            | NONE => (here, rest @ [r], env))) pend ([], [], env);
      in (here, rest, (names, env)) end;
    fun bind_reads T pend t st =
      let
        val (here, rest, st) = split_state (monad_stateT T) pend st;
        (* share one binding per getter *)
        val (uniq, t) = fold (fn (r as (g, v, V, _)) => fn (us, t) =>
            (case find_first (fn (g', _, _, _) => g' aconv g) us of
              SOME (_, v', _, _) => (us, Term.subst_free [(Free (v, V), Free (v', V))] t)
            | NONE => (us @ [r], t))) here ([], t);
        fun lgets (g, v, V, n) t =
          Const (@{const_name lgets}, fastype_of g --> (V --> T) --> T) $ g $
            Abs (n, V, Term.abstract_over (Free (v, V), Term.incr_boundvars 1 t));
      in ((fold_rev lgets uniq t, rest), st) end;
    fun maybe_place Ts ((t, pend), st) =
      if null pend then ((t, pend), st)
      else
        let val T = norm st (fastype_of1 (Ts, t))
        in if is_monadT T then bind_reads T pend t st else ((t, pend), st) end;
    fun go Ts t st =
      maybe_place Ts
        (case dest_lift t of
          SOME (g, _, V) =>
            let val (v, st) = fresh st
            in ((Free (v, V), [(g, v, V, val_name g)]), st) end
        | NONE =>
            (case t of
              t1 $ t2 =>
                let
                  val ((a, p1), st) = go Ts t1 st;
                  val ((b, p2), st) = go Ts t2 st;
                in ((a $ b, p1 @ p2), st) end
            | Abs (n, T, b) =>
                let
                  val ((b, p), st) = go (T :: Ts) b st;
                  fun shift (g, v, V, nm) =
                    if Term.loose_bvar1 (g, 0) then
                      err ctxt ("Lifted: the location depends on the variable " ^ quote n ^
                        " bound between the read and the enclosing computation; use gets explicitly") [g]
                    else (Term.incr_boundvars ~1 g, v, V, nm);
                in ((Abs (n, T, b), map shift p), st) end
            | _ => ((t, []), st)));
    val ((t, pend), (_, env)) = go [] t (Name.make_context (Term.add_free_names t []), env);
  in
    if null pend then (t, env)
    else err ctxt "Lifted: a read outside of a monadic computation" (map #1 pend)
  end;

fun pending_assigns t = Term.exists_Const (fn (c, _) => c = @{const_name LASSIGN}) t;

fun stuck_assigns t =
  let
    fun go (u as Const (@{const_name LASSIGN}, _) $ l $ _) acc = l :: go_sub u acc
      | go u acc = go_sub u acc
    and go_sub (t1 $ t2) acc = go t2 (go t1 acc)
      | go_sub (Abs (_, _, b)) acc = go b acc
      | go_sub _ acc = acc;
  in rev (go t []) end;

fun process ctxt t0 =
  let
    val env = (Vartab.empty, maxidx_of_term t0);
    val (t, env) = resolve_liftq ctxt t0 env;
    val t = Term.map_types (Envir.norm_type (fst env)) t;
    val (t, env) = resolve_stmts ctxt t env;
    val t = Term.map_types (Envir.norm_type (fst env)) t;
  in
    if pending_assigns t then
      (* an lvalue whose reader is not resolved yet (e.g. overloaded "@"): another round *)
      if t aconv t0 then
        err ctxt "Lifted: not an assignable location (a location, or a registered index reader applied to one)"
          (stuck_assigns t)
      else t
    else
      let val (t, env) = place_reads ctxt t env
      in Term.map_types (Envir.norm_type (fst env)) t end
  end;

(* Decisions need the types that type inference and adhoc overloading determine, which may take
   several rounds of the stage-0 loop (e.g. Monad_Syntax.bind is fully polymorphic until resolved).
   We therefore act only once the other checks have stopped changing the terms: the first visit
   records the terms (forcing another round), a visit with unchanged terms resolves the markers. *)
structure Last_Seen = Proof_Data
(
  type T = term list option;
  fun init _ = NONE;
);

fun check ts ctxt =
  if not (exists has_markers ts) orelse exists untyped ts then NONE
  else
    (case Last_Seen.get ctxt of
      SOME ts0 =>
        if eq_list (op aconv) (ts0, ts) then
          SOME (map (fn t => if has_markers t then process ctxt t else t) ts, Last_Seen.put NONE ctxt)
        else SOME (ts, Last_Seen.put (SOME ts) ctxt)
    | NONE => SOME (ts, Last_Seen.put (SOME ts) ctxt));


(** uncheck phase: fold lifted reads and recognise updates **)

fun contains_free v t = Term.exists_subterm (fn u => u = v) t;

(* v occurs in a proper monadic subterm of t? *)
fun nested_use Ts v t =
  let
    fun chk Ts u = contains_free v u andalso
      ((is_monadT (fastype_of1 (Ts, u)) handle TERM _ => false) orelse descend Ts u)
    and descend Ts (t1 $ t2) = chk Ts t1 orelse chk Ts t2
      | descend Ts (Abs (_, T, b)) = chk (T :: Ts) b
      | descend _ _ = false;
  in descend Ts t end;

(* types from the constants only: the handle may be a loose bound variable here *)
fun display_read ctxt g =
  (case g of
    Const (get, T) $ h =>
      if is_getter ctxt get then
        Const (@{const_name LIFT_HANDLE}, domain_type T --> range_type (range_type T)) $ h
      else Const (@{const_name LIFT}, range_type T --> range_type (range_type T)) $ g
  | Const (_, T) => Const (@{const_name LIFT}, T --> range_type T) $ g
  | _ => raise TERM ("display_read", [g]));

(* names: fresh names for the chain variables, threaded through the traversal *)
fun fold_reads ctxt t =
  let
    fun strip_chain t names =
      (case t of
        Const (@{const_name lgets}, T) $ g $ Abs (n, V, b) =>
          let
            val (x, names) = Name.variant n names;
            val v = Free (x, V);
            val ((rest, P), names) = strip_chain (Term.subst_bound (v, b)) names;
          in (((g, n, V, v, T) :: rest, P), names) end
      | _ => (([], t), names));
    fun go Ts t names =
      (case t of
        Const (@{const_name lgets}, _) $ _ $ Abs _ =>
          let
            val ((chain, P), names) = strip_chain t names;
            val (valid, invalid) = List.partition (fn (_, _, _, v, _) => not (nested_use Ts v P)) chain;
            val P = fold (fn (g, _, _, v, _) => Term.subst_free [(v, display_read ctxt g)]) valid P;
            val (P, names) = go Ts P names;
            fun rebuild (g, n, V, v, T) (P, names) =
              let val (g, names) = go Ts g names in
                (Const (@{const_name lgets}, T) $ g $
                  Abs (n, V, Term.abstract_over (v, Term.incr_boundvars 1 P)), names)
              end;
          in fold_rev rebuild invalid (P, names) end
      | t1 $ t2 =>
          let val (a, names) = go Ts t1 names; val (b, names) = go Ts t2 names
          in (a $ b, names) end
      | Abs (n, T, b) => let val (b, names) = go (T :: Ts) b names in (Abs (n, T, b), names) end
      | _ => (t, names));
  in fst (go [] t (Name.make_context (Term.add_free_names t []))) end;

(* modify (upd (\<lambda>v. F)) ~> LASSIGN lv e, with lv the location L or an index path into it:
   F = e (v unused):                      L := e
   F = upd v i e:                         L ! i := e        (registered index updater)
   F = upd v i (upd' (v ! i) j e):        L ! i ! j := e
   otherwise:                             L := F[v := \<langle>L\<rangle>] *)
fun fold_updates ctxt t =
  let
    fun location u =
      (case u of
        Const (upd, T) $ h =>
          if is_updater ctxt upd then
            let val V = domain_type (domain_type (range_type T))
            in SOME (Const (@{const_name LIFT_HANDLE}, domain_type T --> V) $ h, V) end
          else NONE
      | Const (c, T) =>
          (case field_of_updater ctxt c of
            SOME sel =>
              let val V = domain_type (domain_type T) and S = domain_type (range_type T)
              in SOME (Const (@{const_name LIFT}, (S --> V) --> V) $ Const (sel, S --> V), V) end
          | NONE => NONE)
      | _ => NONE);
    (* F is the new value of path P (both in terms of the base variable b) *)
    fun index_path b P F =
      (case strip_comb F of
        (Const (upd, UT), [c, i, x]) =>
          (case index_reader ctxt upd of
            SOME rd =>
              if c aconv P andalso not (contains_free b i) then
                let
                  val (C, I, W) = (case binder_types UT of C :: I :: W :: _ => (C, I, W) | _ => raise Match);
                  val P' = Const (rd, C --> I --> W) $ P $ i;
                in if contains_free b x then index_path b P' x else SOME (P', x, W) end
              else NONE
          | NONE => NONE)
      | _ => NONE);
    fun go (t as Const (@{const_name modify}, MT) $ (u $ Abs (_, _, e))) =
          (case location u of
            SOME (L, V) =>
              let
                val RT = range_type MT;
                fun assign W lv x = Const (@{const_name LASSIGN}, W --> W --> RT) $ lv $ go x;
                val b = Free ("lifted_base__", V);
                val F = Term.subst_bound (b, e);
              in
                if not (contains_free b F) then assign V L F
                else
                  (case index_path b b F of
                    SOME (P, x, W) => assign W (Term.subst_free [(b, L)] P) x
                  | NONE => assign V L (Term.subst_free [(b, L)] F))
              end
          | NONE => go_app t)
      | go t = go_app t
    and go_app (t1 $ t2) = go t1 $ go t2
      | go_app (Abs (n, T, b)) = Abs (n, T, go b)
      | go_app t = t;
  in go t end;

fun uncheck ctxt ts =
  map (fn t => (fold_updates ctxt (fold_reads ctxt t)) handle TERM _ => t | TYPE _ => t) ts;


(** printing **)

fun lift_handle_tr' [h] = Syntax.const @{syntax_const "_lifted"} $ h
  | lift_handle_tr' _ = raise Match;

fun lift_tr' [g] = Syntax.const @{syntax_const "_lifted"} $ g
  | lift_tr' _ = raise Match;

fun unlift_lvalue (t as Const (c, _) $ x) =
      if member (op =) [@{const_syntax LIFT_HANDLE}, @{const_syntax LIFT}] c then x
      else unlift_lvalue_app t
  | unlift_lvalue t = unlift_lvalue_app t
and unlift_lvalue_app t =
  (case strip_comb t of
    (h, a :: args) => list_comb (h, unlift_lvalue a :: args)
  | _ => raise Match);

fun assign_tr' [l, e] = Syntax.const @{syntax_const "_lassign"} $ unlift_lvalue l $ e
  | assign_tr' _ = raise Match;

end;
