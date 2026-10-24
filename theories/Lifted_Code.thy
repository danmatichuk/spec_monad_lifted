theory Lifted_Code
  imports "Spec_Monad_Lifted.Lifted" "Spec_Monad_Code.Spec_Monad_Code"
begin

text \<open>Code generation for programs in the lifted syntax: the reads introduced by lifting
  (\<open>lgets\<close>) fold into \<open>det\<close> like \<open>gets\<close>; everything else desugars to plain \<open>spec_monad\<close>.\<close>

lemma det_lgets[det_fold]: "lgets g (\<lambda>v. det (k v)) = det (\<lambda>s. k (g s) s)"
  by (rule spec_monad_ext) (simp add: lgets_def run_bind run_det_eq)

end
