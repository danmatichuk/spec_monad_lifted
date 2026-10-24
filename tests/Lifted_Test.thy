theory Lifted_Test
  imports "AutoCorres2_Main.AutoCorres_Main" "Spec_Monad_Lifted.Lifted"
begin

record st =
  quirk :: "nat list"
  cnt :: nat
  bufA :: "nat list"
  bufB :: "nat list"

datatype bname = A | B

primrec bget :: "bname \<Rightarrow> st \<Rightarrow> nat list" where
  "bget A = bufA" | "bget B = bufB"

primrec bupd :: "bname \<Rightarrow> (nat list \<Rightarrow> nat list) \<Rightarrow> st \<Rightarrow> st" where
  "bupd A = bufA_update" | "bupd B = bufB_update"

declare [[lifted_record st]]

record st2 = other :: nat \<comment> \<open>not registered\<close>

record st3 = grid :: "nat list list"
declare [[lifted_record st3]]
declare [[lifted_handle bget bupd]]

text \<open>The attribute checks the getter/updater types:\<close>
ML \<open>
  can (Thm.attribute_declaration (Lifted.handle_attr (@{const_name bget}, @{const_name quirk_update}))
    Drule.dummy_thm) (Context.Proof @{context})
  |> not |> @{assert}
\<close>

context includes lifted_syntax begin

definition t_let :: "nat \<Rightarrow> (unit, nat, st) spec_monad" where
  "t_let baz \<equiv> do { let x = \<langle>baz + cnt\<rangle>; return x }"

ML \<open>Thm.prop_of @{thm t_let_def}\<close>
thm t_let_def

text \<open>Assignment through an index of a record field.\<close>
definition t_upd :: "nat \<Rightarrow> nat \<Rightarrow> (unit, unit, st) spec_monad" where
  "t_upd i j \<equiv> do { quirk ! i := \<langle>quirk ! j\<rangle>; skip }"
ML \<open>Thm.prop_of @{thm t_upd_def}\<close>
thm t_upd_def

text \<open>Assignment through an index of a handle: no bget needed.\<close>
definition t_handle :: "bname \<Rightarrow> bname \<Rightarrow> nat \<Rightarrow> (unit, unit, st) spec_monad" where
  "t_handle z x i \<equiv> do { z ! i := \<langle>x ! i + 1\<rangle>; skip }"
ML \<open>Thm.prop_of @{thm t_handle_def}\<close>
thm t_handle_def

text \<open>Whole-location assignment, field and handle.\<close>
definition t_assign :: "bname \<Rightarrow> (unit, unit, st) spec_monad" where
  "t_assign z \<equiv> do { cnt := \<langle>cnt + 1\<rangle>; z := \<langle>quirk\<rangle>; cnt := 0 }"
thm t_assign_def

text \<open>Buffer passed as a name (identity) next to a read.\<close>
definition use_name :: "bname \<Rightarrow> nat \<Rightarrow> (unit, unit, st) spec_monad" where
  "use_name z n \<equiv> do { z ! 0 := n }"
definition t_name :: "bname \<Rightarrow> (unit, unit, st) spec_monad" where
  "t_name z \<equiv> do { \<langle>use_name z (z ! 0)\<rangle>; skip }"
thm t_name_def

text \<open>Reads inside a loop body are performed in every iteration.\<close>
definition t_loop :: "(unit, unit, st) spec_monad" where
  "t_loop \<equiv> do { forLoop 0 3 (\<lambda>i. do { quirk ! nat i := \<langle>cnt\<rangle> }); skip }"
thm t_loop_def

text \<open>Placement after an earlier effect of the same statement.\<close>
definition t_seq :: "(unit, unit, st) spec_monad \<Rightarrow> (unit, nat, st) spec_monad" where
  "t_seq m \<equiv> do { x \<leftarrow> m \<then> return \<langle>cnt\<rangle>; return x }"
ML \<open>Thm.prop_of @{thm t_seq_def}\<close>

text \<open>Conditions.\<close>
definition t_if :: "(unit, unit, st) spec_monad" where
  "t_if \<equiv> do { if \<langle>cnt = 0\<rangle> then do { cnt := 1 } else skip }"
thm t_if_def

text \<open>Semantics.\<close>
lemma "t_upd i j \<bullet> s \<lbrace>\<lambda>r t. quirk t = (quirk s)[i := quirk s ! j]\<rbrace>"
  unfolding t_upd_def by runs_to_vcg

lemma "t_handle z x i \<bullet> s \<lbrace>\<lambda>r t. bget z t = (bget z s)[i := bget x s ! i + 1]\<rbrace>"
  unfolding t_handle_def by runs_to_vcg (cases z; simp)

lemma "do { cnt := 5; let x = \<langle>cnt\<rangle>; return x } \<bullet> s \<lbrace>\<lambda>r t. r = Result 5\<rbrace>"
  by runs_to_vcg

text \<open>Nested index paths, and a reader that is not registered as an index.\<close>
definition t_nested :: "nat \<Rightarrow> nat \<Rightarrow> (unit, unit, st3) spec_monad" where
  "t_nested i j \<equiv> do { grid ! i ! j := \<langle>grid ! j ! i\<rangle> }"
thm t_nested_def
lemma "t_nested i j \<bullet> s \<lbrace>\<lambda>r t. grid t = (grid s)[i := (grid s ! i)[j := grid s ! j ! i]]\<rbrace>"
  unfolding t_nested_def by runs_to_vcg
ML \<open>
  can (Syntax.read_term @{context}) "do { hd quirk := 0 } :: (unit, unit, st) spec_monad"
  |> not |> @{assert}
\<close>

text \<open>Printing folds a read only where that keeps the meaning.\<close>
term "lgets cnt (\<lambda>v. return (v + 1)) :: (unit, nat, st) spec_monad"
term "lgets cnt (\<lambda>v. do { cnt := 5; return v }) :: (unit, nat, st) spec_monad"
term "do { x \<leftarrow> gets cnt; return x } :: (unit, nat, st) spec_monad"

text \<open>A location that is not a record field: a lens registered with \<open>lifted_field\<close>.\<close>
definition first :: "st \<Rightarrow> nat" where "first s = hd (quirk s)"
definition first_upd :: "(nat \<Rightarrow> nat) \<Rightarrow> st \<Rightarrow> st" where
  "first_upd f = quirk_update (\<lambda>xs. f (hd xs) # tl xs)"
declare [[lifted_field first first_upd]]

definition t_lens :: "(unit, unit, st) spec_monad" where
  "t_lens \<equiv> do { first := \<langle>first + cnt\<rangle>; first := \<langle>first + 1\<rangle> }"
thm t_lens_def

text \<open>Only registered locations are lifted: fields of an unregistered record are not.\<close>
ML \<open>
  can (Syntax.read_term @{context}) "return \<langle>other + 1\<rangle> :: (unit, nat, st2) spec_monad"
  |> not |> @{assert}
\<close>

text \<open>Errors (expected to fail).\<close>
ML \<open>
  can (Thm.attribute_declaration (Lifted.field_attr (@{const_name first}, @{const_name bufA_update}))
    Drule.dummy_thm) (Context.Proof @{context})
  |> not |> @{assert}
\<close>
text \<open>A pure region is not a statement (updates are always assignments):\<close>
ML \<open>
  can (Syntax.read_term @{context}) "do { \<langle>quirk[0 := 1]\<rangle> } :: (unit, unit, st) spec_monad"
  |> not |> @{assert}
\<close>
text \<open>Only handles are lifted, not containers of handles; variables bound inside a region are
  not lifted either. Both are type errors:\<close>
ML \<open>
  can (Syntax.read_term @{context}) "return \<langle>map (\<lambda>b. b ! 0) (bs :: bname list)\<rangle> :: (unit, nat list, st) spec_monad"
  |> not |> @{assert};
  can (Syntax.read_term @{context}) "return \<langle>(\<lambda>b::bname. b ! 0) A\<rangle> :: (unit, nat, st) spec_monad"
  |> not |> @{assert}
\<close>
text \<open>whereas handle *constants* are lifted (reads \<open>bufA\<close> and \<open>bufB\<close>):\<close>
term "return \<langle>map (\<lambda>b. b ! 0) [A, B]\<rangle> :: (unit, nat list, st) spec_monad"

end

end
