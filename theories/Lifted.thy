theory Lifted
  imports "AutoCorres2.Spec_Monad"
begin

text \<open>
  Lifted expressions \<open>\<langle>e\<rangle>\<close> and assignments \<open>L := e\<close> for \<open>spec_monad\<close> programs.
  Design: docs/lifted_syntax_design.md.
\<close>

section \<open>Logical constants\<close>

definition lgets :: "('s \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('e::default, 'a, 's) spec_monad) \<Rightarrow> ('e, 'a, 's) spec_monad" where
  "lgets g k \<equiv> Spec_Monad.bind (gets g) k"

lemma lgets_runs_to[runs_to_vcg]: "k (g s) \<bullet> s \<lbrace>Q\<rbrace> \<Longrightarrow> lgets g k \<bullet> s \<lbrace>Q\<rbrace>"
  unfolding lgets_def by runs_to_vcg

text \<open>Locals are \<open>let\<close>-bound (\<open>let x = \<langle>e\<rangle>\<close>), so the VCG steps through \<open>Let\<close>.\<close>
lemma Let_runs_to[runs_to_vcg]: "f a \<bullet> s \<lbrace>Q\<rbrace> \<Longrightarrow> Let a f \<bullet> s \<lbrace>Q\<rbrace>"
  by simp

lemma always_progress_lgets[always_progress_intros]:
  "(\<And>v. always_progress (k v)) \<Longrightarrow> always_progress (lgets g k)"
  unfolding lgets_def by (intro always_progress_intros)

section \<open>Markers\<close>

text \<open>Parse-time markers (resolved by the check phase) and print-time markers (introduced by the
  uncheck phase). None of them survives checking.\<close>

consts
  LIFTQ :: "'a \<Rightarrow> 'b"            \<comment> \<open>identifier inside a region, lifted or not depending on types\<close>
  LREGION :: "'a \<Rightarrow> 'b"          \<comment> \<open>a region: value, call or update depending on types\<close>
  LASSIGN :: "'v \<Rightarrow> 'v \<Rightarrow> ('e, unit, 's) spec_monad"   \<comment> \<open>\<open>L := e\<close>\<close>
  LIFT :: "('s \<Rightarrow> 'v) \<Rightarrow> 'v"       \<comment> \<open>a read of a getter, to be placed\<close>
  LIFT_HANDLE :: "'h \<Rightarrow> 'v"      \<comment> \<open>printing: read through a handle\<close>

syntax
  "_lifted" :: "'a \<Rightarrow> 'a"
  "_lassign" :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  "_do_lassign" :: "'a \<Rightarrow> 'a \<Rightarrow> do_bind"
  "_do_lassign_final" :: "'a \<Rightarrow> 'a \<Rightarrow> do_binds"

translations
  "_do_lassign l e" \<leftharpoondown> "_do_then (_lassign l e)"
  "_do_lassign_final l e" \<leftharpoondown> "_do_final (_lassign l e)"

text \<open>\<open>L := e\<close> is a do-statement (a term-level form would clash with \<open>xs[i := v]\<close>);
  outside do-blocks it is only printed.\<close>

bundle lifted_syntax begin
syntax
  "_lifted" :: "'a \<Rightarrow> 'a"  (\<open>\<langle>_\<rangle>\<close>)
  "_do_lassign" :: "'a \<Rightarrow> 'a \<Rightarrow> do_bind"  (\<open>(2_ :=/ _)\<close> [51, 0] 13)
  "_do_lassign_final" :: "'a \<Rightarrow> 'a \<Rightarrow> do_binds"  (\<open>(2_ :=/ _)\<close> [51, 0] 13)
syntax (output)
  "_lassign" :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"  (\<open>(2_ :=/ _)\<close> [51, 0] 50)
end

ML_file \<open>lifted.ML\<close>

parse_ast_translation \<open>
  [(@{syntax_const "_do_lassign"}, K Lifted.do_assign_ast_tr),
   (@{syntax_const "_do_lassign_final"}, K Lifted.do_assign_final_ast_tr)]
\<close>

parse_translation \<open>
  [(@{syntax_const "_lifted"}, K Lifted.region_tr),
   (@{syntax_const "_lassign"}, K Lifted.assign_tr)]
\<close>

print_translation \<open>
  [(@{const_syntax LIFT_HANDLE}, K Lifted.lift_handle_tr'),
   (@{const_syntax LIFT}, K Lifted.lift_tr'),
   (@{const_syntax LASSIGN}, K Lifted.assign_tr')]
\<close>

setup \<open>
  Context.theory_map
   (Syntax_Phases.term_check' 0 "lifted" Lifted.check #>
    Syntax_Phases.term_uncheck ~10 "lifted" Lifted.uncheck)
\<close>

text \<open>Registration of locations and assignable indices (declaration attributes):
  \<^item> \<open>[[lifted_index rd upd]]\<close>: \<open>rd :: 'c \<Rightarrow> 'i \<Rightarrow> 'v\<close>, \<open>upd :: 'c \<Rightarrow> 'i \<Rightarrow> 'v \<Rightarrow> 'c\<close>; then
    \<open>rd lv i := e\<close> (e.g. \<open>xs ! i := e\<close>) assigns through the index;
  \<^item> \<open>[[lifted_field get upd]]\<close>: \<open>get :: 's \<Rightarrow> 'v\<close>, \<open>upd :: ('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's\<close>;
  \<^item> \<open>[[lifted_record T]]\<close>: every field of record type \<open>T\<close>, with the updaters of the record package;
  \<^item> \<open>[[lifted_handle get upd]]\<close>: \<open>get :: 'h \<Rightarrow> 's \<Rightarrow> 'v\<close>, \<open>upd :: 'h \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's\<close>;
    \<open>'h\<close> is the handle type.\<close>

attribute_setup lifted_field = \<open>
  Args.const {proper = true, strict = true} -- Args.const {proper = true, strict = true} >> Lifted.field_attr
\<close> "register a state field for lifted expressions: getter and updater"

attribute_setup lifted_record = \<open>
  Args.typ >> Lifted.record_attr
\<close> "register all fields of a record type for lifted expressions"

attribute_setup lifted_index = \<open>
  Args.const {proper = true, strict = true} -- Args.const {proper = true, strict = true} >> Lifted.index_attr
\<close> "register an assignable index: reader c i and updater c i v (lvalues c ! i := e)"

attribute_setup lifted_handle = \<open>
  Args.const {proper = true, strict = true} -- Args.const {proper = true, strict = true} >> Lifted.handle_attr
\<close> "register a handle type for lifted expressions: getter and updater"

declare [[lifted_index nth list_update]]

end
