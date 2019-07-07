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
"notSpf = notStep (dawInitState dAnot)"


interpretation not_sscanl:smapGen "dAnot" "buildNotinSBE" "buildNotoutSBE" Single
  sorry


end