theory SumUpAutomat

imports automaton.dAutomaton_causal sumUpAutomat_inc

begin
(*SumUp automaton*)
fun dAsumUp_transition::"S_sumUp \<Rightarrow> (nat) \<Rightarrow> (S_sumUp \<times> nat)"where
"dAsumUp_transition (S n) (input) = (S (n+input),n+input)"

interpretation sumUp_sscanl:sscanlGen "dAsumUp_transition" "S 0" "buildSumUpinSBE" "buildSumUpoutSBE"
  by(unfold_locales)
  
abbreviation sumUpStep::"(S_sumUp \<Rightarrow> (inSumUp\<^sup>\<Omega> \<rightarrow> outSumUp\<^sup>\<Omega>))"where
"sumUpStep \<equiv> dawStateSem sumUp_sscanl.da"

definition sumUpSpf::"(inSumUp\<^sup>\<Omega> \<rightarrow> outSumUp\<^sup>\<Omega>)"where
"sumUpSpf = dawSem sumUp_sscanl.da"

lemma sumUpingetset_eq:"sumUpInSBE.getterSB\<cdot>(sumUpInSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma sumUpoutgetset_eq:"sumUpOutSBE.getterSB\<cdot> (sumUpOutSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma sumUpstep2sscanl:"sumUpOutSBE.getterSB\<cdot>(sumUpStep state\<cdot>(sumUpInSBE.setterSB\<cdot>input)) = sscanlAsnd dAsumUp_transition state\<cdot>input"
  by (simp add: sumUp_sscanl.daut2sscanl)

lemma sumUp_step_t1:"sscanlAsnd dAsumUp_transition (S n)\<cdot>(\<up>(a) \<bullet> s) = \<up>(n+a) \<bullet> sscanlAsnd dAsumUp_transition (S (n+a))\<cdot>(s)"
  by simp

lemma sumup_invariante:"snth n input \<le> snth n (sumUpOutSBE.getterSB\<cdot>(sumUpStep state\<cdot>(sumUpInSBE.setterSB\<cdot>input)))"
  apply(simp add: sumUpstep2sscanl)
proof(induction n arbitrary: input state)
case 0
  then show ?case
    by(subst scases[of input]; cases state;simp_all)
next
  case (Suc n)
  then show ?case
    by(subst scases[of input]; cases state;simp_all)
qed


end