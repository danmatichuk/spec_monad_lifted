# Lifted expressions and assignments for `spec_monad` programs

Status: design + working prototype (`Lifted.thy`, `lifted.ML`; tests `Lifted_Test.thy`). Supersedes `Modifies_With.thy` for new code. §8 lists what the prototype
changed relative to the original design.

## 1. Goal

Write state-manipulating `spec_monad` code close to the imperative source, without explicit `gets`/`modify` plumbing and without guessing whether a name is a
local or a piece of state.

```isabelle
(λ(i, c). do {
   let c = ⟨c + ui (x @ i) + ui (y @ i)⟩;      (* x, y :: buf  — buffer *names* *)
   ⟨z⟦i := of_int c⟧⟩;                         (* update limb i of buffer z *)
   return (i + 1, c >>⇩l 32)
})
```

desugars to ordinary monadic code:

```isabelle
(λ(i, c). do {
   x_val ← gets (bget x); y_val ← gets (bget y);
   let c = c + ui (x_val @ i) + ui (y_val @ i);
   modify (bupd z (λv. v⟦i := of_int c⟧));
   return (i + 1, c >>⇩l 32)
})
```

(`gets … ⤜ …` is actually the marker `lgets`, see §6.)

## 2. Surface syntax

| Form | Meaning |
|---|---|
| `⟨e⟩` | **Lifted region.** Inside `e`, *locations* denote their current value. Regions may nest. |
| `L := e` | **Assignment** of the whole location `L` (a record field or a handle). `e` may contain regions. A **do-statement** (see §8); write `do { L := e }` elsewhere. |
| `⟨e⟩` in a monadic position, `e` pure | **Update** of a location occurring in `e` (§5.2), e.g. `⟨z⟦i := v⟧⟩`, `⟨quirk[i := quirk ! j]⟩`. |

Locals are ordinary `let x = …` / `x ← …`. `:=` only ever assigns state, so there is no
local-vs-field ambiguity (unlike `Modifies_With`'s `c := e`).

### Locations

* **Fields**: a getter `fld :: 's ⇒ 'v` with an updater `upd :: ('v ⇒ 'v) ⇒ 's ⇒ 's`, registered
  with `declare [[lifted_field fld upd]]` — any lens, not only record fields. `declare
  [[lifted_record T]]` registers every field of record type `T` (and its parents) with the updaters
  the record package defines; this attribute is the only record-specific code.
* **Handles**: values of a registered *handle type* `'h` naming a piece of state, with
  `get :: 'h ⇒ 's ⇒ 'v` and `upd :: 'h ⇒ ('v ⇒ 'v) ⇒ 's ⇒ 's`. Registered once:
  `declare [[lifted_handle bget bupd]]` (the handle type is the getter's first argument type). Then any term of type `buf` used *as a value of type `'v`* inside a
  region is read through `bget` — `⟨z⟦i := …⟧⟩`, no `bget z` needed.

## 3. Semantics

1. **Type-directed lifting.** Inside a region, an identifier `t :: 'a` used at type `'b` is
   * `t` itself if `'a = 'b` (e.g. a buffer passed *as a name* to `foo :: buf ⇒ …`, or any local);
   * a read of `get t` if `'a` is a handle type with value type `'b`;
   * a read of `t` if `t` is a registered field getter `'s ⇒ 'b`;
   * otherwise a type error.
   Shadowing is handled correctly: a local named like a field has its own type and stays a local.
2. **Read placement.** A read is performed at the start of the **smallest enclosing monadic
   computation** (subterm of type `(_, _, 's) spec_monad` for the location's state type `'s`):
   * `let x = ⟨baz + quirk⟩; rest` – before the `let` (exactly the user-level desugaring);
   * `x ← foo ⟨quirk⟩` – around `foo …`;
   * `if ⟨c⟩ then A else B` – before the `if`;
   * `forLoop 0 12 (λi. …⟨…⟩…)` – inside the loop body, every iteration;
   * `condM (leqM a b) (bar ⟨quirk⟩)` – when `bar` runs, i.e. *after* `leqM`.
   A syntactic rule ("start of the enclosing do-statement") would get the last case wrong.
3. Reads under a **pure** λ inside a region (`⟨map (λi. quirk ! i) is⟩`) are hoisted past the λ:
   the λ sees one state. Variables bound *inside* a region are never lifted (only identifiers
   that are free at the region are wrapped), so `⟨map (λb. b @ 0) bufs⟩` with `b :: buf` is a type
   error rather than a read; use an explicit `gets`. A location built from a variable bound
   *outside* the region (e.g. a loop variable) is read inside that binder; if the binder's body is
   not monadic this is an error.
4. Identical reads at the same placement point share one binding.

## 4. Pipeline

```
parse translation ──► type inference ⇄ lifted check ⇄ adhoc overloading ──► (stage 1) reject unresolved
   (markers)            (stage 0, iterated to a fixpoint by Syntax_Phases)
                                                                          uncheck: fold lgets ──► print
```

### 4.1 Parsing (term-level `parse_translation`)

Types are unknown at parse time, so the parser only places polymorphic markers:

* `⟨e⟩` ↦ `LREGION e'` where `e'` wraps every identifier in an argument position
  (free names, constructors; not function heads, not variables bound inside the region) as
  `LIFTQ t`. `LIFTQ, LREGION :: 'a ⇒ 'b` disconnect the identifier/region from its context's type,
  so inference succeeds whether `z :: buf` is used as a `buf` or as its contents.
* `L := e` ↦ `LASSIGN (LIFTQ L) e` with `LASSIGN :: 'v ⇒ 'v ⇒ ('e, unit, 's) spec_monad`.

### 4.2 Check phase (`Syntax_Phases.term_check' 0 "lifted"`)

Runs inside the stage-0 loop together with type inference and adhoc overloading (Isabelle iterates
all stage-0 checks to a fixpoint; unresolved overloading is only rejected at stage 1). Does nothing
while marker types are still `dummyT`. Decisions are **deferred until the other checks have stopped
changing the terms**: the first visit records the terms in the proof context and forces another
round; a visit with unchanged terms resolves the markers. This is necessary because e.g.
`Monad_Syntax.bind` is fully polymorphic (`'a ⇒ ('b ⇒ 'c) ⇒ 'd`) until adhoc overloading resolves it,
so right after inference a statement region's type is still a variable. Then, in order:

1. **Resolve `LIFTQ t : 'a ⇒ 'b`** by the rules of §3.1 to `t` or `LIFT g`
   (`LIFT :: ('s ⇒ 'v) ⇒ 'v`, `g` = `get t` or the selector). If `'b` (or `'a`) is still a type
   variable, it is unified (handles: `'b := 'v`); the substitution is applied to the whole term.
   Overloaded constants such as `x @ i` (`nth_gen`) only become resolvable after this unification,
   which is why this check must run *before* stage 1.
2. **Resolve `LASSIGN (LIFT g) e`** ↦ `modify (upd_g (λ_. e))`.
3. **Resolve `LREGION X : 'a ⇒ 'b`**:
   * `'a = 'b` (or `'b` a variable): value/call, drop the marker;
   * `'b` monadic, `'a` pure: **update** (§5.2) ↦ `modify (upd_g (λv. X[target := v]))`;
   * otherwise a type error.
4. **Place reads** (§3.2): bottom-up; each `LIFT g` becomes a fresh variable that is bound by
   `lgets g (λv. …)` at the smallest enclosing monadic subterm with `g`'s state type.

The result contains only real constants (`lgets`, `modify`, `bupd`, selectors, …); type inference
re-runs on it in the loop.

### 4.3 Printing (`Syntax_Phases.term_uncheck`)

* `lgets g (λv. M)` is folded back to `M[v := ⟨disp g⟩]` iff it is still **valid**: no proper
  monadic subterm of `M` (same state type) lies between `M` and an occurrence of `v`. Otherwise it
  is printed as an explicit bind. The check is needed because proofs (`simp`, unfolding `Let`, VCG)
  can change the continuation after parsing.
* `modify (upd_g (λ_. e))` prints as `L := e`; `modify (upd_g (λv. F v))` as `⟨F L⟩`.
* Updaters are recognised through the location registry (no naming conventions).
* `disp (bget h) = h`, `disp fld = fld`. Regions are printed around each folded occurrence
  (`ui (⟨x⟩ @ i)`); this is semantically identical to a larger region because lifting is
  type-directed. Recovering the exact original extent would need a region marker in the logic; not
  worth it.

## 5. Details

### 5.1 Location registry

`Generic_Data` with two tables, queried by the check and uncheck phases only:
fields (getter ↦ updater) and handles (handle type ↦ getter, updater). Three declaration
attributes fill it, each type-checking its arguments:

* `[[lifted_field get upd]]`: `get :: 's ⇒ 'v`, `upd :: ('v ⇒ 'v) ⇒ 's ⇒ 's`;
* `[[lifted_record T]]`: all fields of `T`; the updaters are taken from the record package's
  `update_defs` (checked against `Record.updateN`), not constructed from names;
* `[[lifted_handle get upd]]` (below).

The declaration attribute `[[lifted_handle get upd]]` checks `get :: 'h ⇒ 's ⇒ 'v` and
`upd :: 'h ⇒ ('v ⇒ 'v) ⇒ 's ⇒ 's` with `'h` a type constant, and stores `('h, get, upd)` in
`Generic_Data`. The usual frame lemma
`get b (upd b' f s) = (if b = b' then f (get b s) else get b s)` is the user's responsibility.

### 5.2 Updates (setter inference)

A region in a monadic position whose content `X :: 'a` is pure is an update of location `L` where
`L` is the leftmost **direct argument** of the root of `X` that is a lifted read of type `'a`:
`⟨z⟦i := v⟧⟩` (root `seq_update`), `⟨quirk[i := quirk ! j]⟩` (root `list_update`, first
`quirk`), `⟨cnt + 1⟩` (`cnt += 1`). All occurrences of `L` in `X` are read in the same state, so the
choice among them does not matter. No candidate ⇒ error suggesting `L := …`.

Open question: restrict to "update-shaped" roots (`list_update`, `seq_update`, `fun_upd`, record
updates) instead of any root? Inference over any root is simpler and the prototype does that.

### 5.3 The `lgets` marker

```isabelle
definition lgets :: "('s ⇒ 'v) ⇒ ('v ⇒ ('e,'a,'s) spec_monad) ⇒ ('e,'a,'s) spec_monad"
  where "lgets g k ≡ gets g ⤜ k"
```

Reads introduced by lifting use `lgets` rather than `gets ⤜`, so printing folds exactly the
lifted reads and never user-written `gets`. It has a `runs_to_vcg` rule and is **not** a simp rule:
* VCG proofs see it directly;
* `simp` does not flatten reads across statements (a feature), but generic monad lemmas
  (`bind_assoc`, …) do not apply under it until `unfolding lgets_def`;
* after unfolding, terms are plain `gets` and print plainly.

### 5.4 Known costs / risks

* Every identifier in a region is wrapped in `LIFTQ`, weakening inference inside regions; the
  post-unification repairs the common cases (numerals, overloaded operators). Type errors inside
  regions mention the markers.
* A term-level `L := e` is ambiguous with `xs[i := v]` / `f(x := y)` (it parses as a list literal or
  argument containing an assignment), hence `:=` is a do-statement form (§8).
* A read placed outside a pure λ that is *not* inside its region (e.g. a `whileLoop` condition)
  is read once; should become a warning (not in the prototype).

## 6. Rejected alternatives

* **Name-based lifting at parse time** (as in `Modifies_With`): cannot lift values of a handle
  type, and captures locals named like fields.
* **Coercions** (`declare [[coercion bget_val]]`): global rather than region-scoped, and not
  inserted through polymorphic overloaded constants (`x @ i` with `nth_gen :: 'a ⇒ nat ⇒ 'b` has no
  type clash), which is exactly the common case.
* **Syntactic read placement** (start of the enclosing do-statement): wrong for monadic arguments
  that run after other effects of the same statement (`condM c (bar ⟨q⟩)`).
* **Plain `gets` + heuristic folding**: folds user-written `gets` too; the validity check is
  needed either way, but the marker makes recognition exact.

## 7. Prototype scope (as planned)

`Lifted.thy`: markers, syntax (bundle `lifted_syntax`), handle registry, parse translation, check
phase (§4.2), uncheck/print (§4.3), `lgets` with VCG rule.
`Lifted_Test.thy`: round-trip and semantic tests on a small record, plus a port of a few
word operations (`add`, `shr`, `mod_half`).
Not in the prototype: the crossing-λ warning, region-extent recovery.

## 8. Prototype findings

What the prototype settled or changed:

* **Deferred check** (§4.2): resolving markers in the first round after inference gets statement
  regions wrong (generic `bind`). Fixed by acting only at the stage-0 fixpoint.
* **`:=` is a do-statement** (`do_bind`/`do_binds` productions with an AST translation to
  `_do_then`/`_do_final`); outside do-blocks it is only *printed* (`syntax (output)`), e.g.
  `if ⟨cnt⟩ = 0 then cnt := 1 else skip`. Write `do { cnt := 1 }` in branches.
* **Wrapping** skips the type/position arguments of `_constrain`, `_constrainAbs` and
  `_type_constraint_`, and treats a constrained head as atomic.
* **`Let` VCG rule** (`Let_runs_to`): locals are `let`-bound now, and `runs_to_vcg` does not step
  through `Let` by itself.
* **Printing**: regions are printed per occurrence and nest, e.g.
  `⟨z⟦i := ⟨x⟩ @ i⟧⟩`, `let c = c + ui (⟨x⟩ @ i) + ui (⟨y⟩ @ i)`, `cnt := ⟨cnt⟩ + 1`. Folding is
  refused when it would move a read past an effect: `lgets cnt (λv. do { cnt := 5; return v })`
  prints as is. User-written `gets` is never folded.
* **Do-notation printing** requires the AutoCorres2 printing setup (`AutoCorres2_Main`); with
  `Spec_Monad` alone, do-blocks print as `⤜` chains. Unrelated to this work.
* **Handle constants** are lifted too: `⟨map (λb. b ! 0) [A, B]⟩` reads buffers `A` and `B`.
* **Performance**: on the full 54-field `ecc_state`, definitions elaborate in ~10 ms and the
  `sq_inner1` spec is proved by `runs_to_vcg` alone, as with `Modifies_With`.

* **Registration** is by declaration attributes (`lifted_field`, `lifted_record`,
  `lifted_handle`), which type-check getter and updater. Fields are no longer recognised by the
  `fld`/`fld_update` naming convention: only registered locations are lifted (an unregistered
  record's fields are a type error inside regions), and arbitrary lenses can be locations
  (`Lifted_Test.thy`: `first`/`first_upd` on the head of a list field).

Still open: the crossing-λ warning (§5.4), printing invalid `lgets` as an explicit bind (currently
printed raw as `lgets g (λv. …)`).

## 9. Assignment is the only way to write state (revision)

The statement-level update regions of §5.2 (a pure `⟨…⟩` in statement position updating a location
it mentions) are **removed**: `⟨…⟩` only ever denotes a value, and a pure region in statement
position is an error. All writes are assignments to an **lvalue**:

    lvalue ::= location | rd lvalue i        (rd a registered index reader)

* `[[lifted_index rd upd]]` registers an assignable index: `rd :: 'c ⇒ 'i ⇒ 'v`,
  `upd :: 'c ⇒ 'i ⇒ 'v ⇒ 'c` (type-checked). `Lifted.thy` registers `nth`/`list_update`.
* The assignment syntax is the reader's own notation, as in C-style languages (`z[i] = e` reads like `z[i]`):
  `z @ i := of_int c`, `quirk ! i := ⟨quirk ! j⟩`, nested `grid ! i ! j := 0`, plus
  `cnt := ⟨cnt + 1⟩` for whole locations. The right-hand side is an ordinary expression; `⟨…⟩` has
  no role in the lvalue.
* Only the base of the lvalue is lifted (marked `LIFTQ` at parse time); indices are plain
  expressions (use `⟨…⟩` to read state in an index).
* Desugaring: `L ! i ! j := e` ↦ `modify (upd_L (λv. v[i := (v ! i)[j := e]]))`.
* Overloaded readers (`@` is `nth_gen` until adhoc overloading picks `nth_seq`) are handled by the
  stage-0 deferral: an assignment whose reader is not yet a registered constant is left in place
  for another round; it is an error only once nothing changes any more.
* Printing inverts this: `modify (upd_L (λv. F))` prints as an indexed assignment when `F` is a
  chain of registered updates along a reader path, and as `L := F[v := ⟨L⟩]` otherwise.
* Bug found while implementing: the update function must be built with `abstract_over` after
  `incr_boundvars` (not `absfree`), otherwise loose variables of an enclosing λ (loop indices) are
  captured.
