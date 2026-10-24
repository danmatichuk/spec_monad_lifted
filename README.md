# Spec_Monad_Lifted

Isabelle/HOL infrastructure for writing AutoCorres2 `spec_monad` programs in an imperative style,
and for executing their deterministic fragment.

* `theories/Lifted.thy` (+ `lifted.ML`): lifted expressions `⟨e⟩` (read state: record fields,
  registered handles such as buffer names) and assignments `L := e`, `L ! i := e`, `z @ i := e`
  to lvalues. Locations are registered with declaration attributes:
  `[[lifted_record T]]`, `[[lifted_field get upd]]`, `[[lifted_handle get upd]]`,
  `[[lifted_index rd upd]]`. Desugars to plain `gets`/`modify`/`bind` (reads via `lgets`) in a
  check phase, and prints back in the surface syntax.
* `theories/Spec_Monad_Code.thy`: code generation for deterministic programs. `det` embeds
  `'s ⇒ ('a × 's) option` and is the code constructor of `spec_monad`; `det_code c1 ... cn`
  derives code equations `ci x = det F` for program definitions (callees first).
* `docs/lifted_syntax_design.md`: design notes.

Sessions: `Spec_Monad_Lifted` (on `AutoCorres2_Main`) and `Spec_Monad_Lifted_Test`.
Bundle: `includes lifted_syntax`.
