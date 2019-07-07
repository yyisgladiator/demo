theory AndAutomat

imports automaton.dAutomaton_causal andAutomat_inc

begin
(*And automaton*)
fun dAand_transitionH::"S_and \<Rightarrow> (bool\<times> bool) \<Rightarrow> (S_and \<times> bool)"where
"dAand_transitionH S (bool1,bool2) = (S,(bool1 \<and> bool2))"

definition dAnd_transition::"S_and \<Rightarrow> inAnd\<^sup>\<surd> \<Rightarrow> (S_and \<times> outAnd\<^sup>\<surd>)"where
"dAnd_transition S insbe = (let (nextState, output) = dAand_transitionH S (sbeGen.getter buildAndinSBE insbe) in
                           (nextState, sbeGen.setter buildAndoutSBE output)) "

definition dAand::"(S_and, inAnd, outAnd,emptychan) dAutomaton_weak"where
"dAand = (| dawTransition =dAnd_transition,
                 dawInitState = Single , dawInitOut = Abs_sbElem(None) |)"

(*And Sem*)

definition andStep::"(S_and \<Rightarrow> (inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>))"where
"andStep = dawStateSem dAand"

definition andSpf::"(inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>)"where
"andSpf = andStep (dawInitState dAand)"

interpretation and_smap:smapGen "dAand" "buildAndinSBE" "buildAndoutSBE" "Single"
  sorry

lemma andingetset_eq:"andInSBE.getterSB\<cdot>(andInSBE.setterSB\<cdot>s) = s"
  apply(rule andInSBE.getset_eq)
  apply(simp add: chIsEmpty_def cEmpty_def)
  using cEmpty_def somechan_class.chan_empty by fastforce

lemma andoutgetset_eq:"andOutSBE.getterSB\<cdot> (andOutSBE.setterSB\<cdot>s) = s"
  apply(rule andOutSBE.getset_eq)
  apply(simp add: chIsEmpty_def cEmpty_def)
  using cEmpty_def somechan_class.chan_empty by fastforce

lemma "andOutSBE.getterSB\<cdot>(andStep Single\<cdot>(andInSBE.setterSB\<cdot>input)) = (smap and_smap.smapTransition)\<cdot>input"
  by(simp add: andStep_def and_smap.daut2smap andingetset_eq andoutgetset_eq)

lemma "andOutSBE.getterSB\<cdot>(andStep Single\<cdot>(andInSBE.setterSB\<cdot>(\<up>(x,y)))) = \<up>(x\<and>y)"
  sorry


end