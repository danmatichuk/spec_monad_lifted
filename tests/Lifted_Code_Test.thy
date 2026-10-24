theory Lifted_Code_Test
  imports "AutoCorres2_Main.AutoCorres_Main" "Spec_Monad_Lifted_Code.Lifted_Code"
begin

text \<open>A small program with a loop, a field update and an indexed assignment, executed through
  its derived code equation.\<close>

record st = cnt :: nat  xs :: "nat list"
declare [[lifted_record st]]

context includes lifted_syntax begin

definition step :: "nat \<Rightarrow> (unit, unit, st) spec_monad" where
  "step i \<equiv> do { xs ! i := \<langle>cnt\<rangle>; cnt := \<langle>cnt + 1\<rangle> }"

definition prog :: "(unit, nat, st) spec_monad" where
  "prog \<equiv> do {
     n \<leftarrow> whileLoop (\<lambda>i _. i < 3) (\<lambda>i. do { step i; return (i + 1) }) 0;
     let r = \<langle>cnt * 10 + n\<rangle>;
     return r
   }"

end

det_code step prog

lemma "run_det prog \<lparr>cnt = 5, xs = [0, 0, 0]\<rparr> = Some (83, \<lparr>cnt = 8, xs = [5, 6, 7]\<rparr>)"
  by eval

end
