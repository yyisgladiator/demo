theory NotAutomat

imports automaton.dAutomaton_causal notAutomat_inc

begin
(*Not automaton*)
fun dAnot_transitionH::"S_not \<Rightarrow> (bool) \<Rightarrow> (S_not \<times> bool)"where
"dAnot_transitionH S (bool) = (S,(\<not>bool))"

definition dNot_transition::"S_not \<Rightarrow> inNot\<^sup>\<surd> \<Rightarrow> (S_not\<times> outNot\<^sup>\<surd>)"where
"dNot_transition S insbe = (let (nextState, output) = dAnot_transitionH S (sbeGen.getter buildNotinSBE insbe) in
                           (nextState, sbeGen.setter buildNotoutSBE output)) "

definition dAnot::"(S_not, inNot, outNot) dAutomaton_strong"where
"dAnot = (| dawTransition =dNot_transition,
                 dawInitState = Single, dawInitOut = sbeGen.setter buildNotoutSBE True|)"


(*And Sem*)
abbreviation notStep::"(S_not \<Rightarrow> (inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>))"where
"notStep \<equiv> dawStateSem dAnot"

definition notSpf::"(inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>)"where
"notSpf = dasSem dAnot"


interpretation not_smap:smapGen "dAnot" "buildNotinSBE" "buildNotoutSBE" Single
  sorry

lemma notingetset_eq:"notInSBE.getterSB\<cdot>(notInSBE.setterSB\<cdot>s) = s"
  by(simp add: notInSBE.getset_eq)

lemma notoutgetset_eq:"notOutSBE.getterSB\<cdot> (notOutSBE.setterSB\<cdot>s) = s"
  by(simp add: notOutSBE.getset_eq)

lemma notstep2smap:"notOutSBE.getterSB\<cdot>(notStep state\<cdot>(notInSBE.setterSB\<cdot>input)) = (smap not_smap.smapTransition)\<cdot>input"
  by (simp add: notInSBE.getset_eq not_smap.daut2smap notoutgetset_eq)

thm dAutomaton_weak.select_convs

lemma "notOutSBE.getterSB\<cdot>(notSpf\<cdot>(notInSBE.setterSB\<cdot>input)) = \<up>True \<bullet>(smap not_smap.smapTransition)\<cdot>input"
  apply(simp add: notSpf_def dasSem_def)
  apply(subst notOutSBE.gettersb_unfold)
  apply(simp add: dAnot_def)
  by (metis dAnot_def dAutomaton_weak.select_convs(1) notstep2smap)

lemma "smap not_smap.smapTransition\<cdot>(\<up>bool \<bullet> s) = \<up>(\<not>bool) \<bullet> smap not_smap.smapTransition\<cdot>s"
  by(simp add: dAnot_def dNot_transition_def)

end