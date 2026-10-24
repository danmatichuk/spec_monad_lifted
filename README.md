# Spec_Monad_Lifted

Isabelle/HOL infrastructure for writing AutoCorres2 `spec_monad` programs in an imperative style,
with a bridge to the `spec_monad` code generator.

* `theories/Lifted.thy` (+ `lifted.ML`): lifted expressions `⟨e⟩` (read state: record fields,
  registered handles such as buffer names) and assignments `L := e`, `L ! i := e`, `z @ i := e`
  to lvalues. Locations are registered with declaration attributes:
  `[[lifted_record T]]`, `[[lifted_field get upd]]`, `[[lifted_handle get upd]]`,
  `[[lifted_index rd upd]]`. Desugars to plain `gets`/`modify`/`bind` (reads via `lgets`) in a
  check phase, and prints back in the surface syntax.
* `code/Lifted_Code.thy` (session `Spec_Monad_Lifted_Code`): makes lifted programs executable with
  the code generator of `~/Code/spec_monad_code` (session `Spec_Monad_Code`, `det_code`).
* `docs/lifted_syntax_design.md`: design notes.

Sessions: `Spec_Monad_Lifted` (on `AutoCorres2_Main`, no dependency on the code generator),
`Spec_Monad_Lifted_Code` (needs `Spec_Monad_Code`) and `Spec_Monad_Lifted_Test`.
Bundle: `includes lifted_syntax`.
