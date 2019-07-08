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

abbreviation andStep::"(S_and \<Rightarrow> (inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>))"where
"andStep \<equiv> dawStateSem dAand"

definition andSpf::"(inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>)"where
"andSpf = dawSem dAand"

interpretation and_smap:smapGen "dAand" "buildAndinSBE" "buildAndoutSBE" "Single"
  sorry

lemma andingetset_eq:"andInSBE.getterSB\<cdot>(andInSBE.setterSB\<cdot>s) = s"
  by(simp add: andInSBE.getset_eq)

lemma andoutgetset_eq:"andOutSBE.getterSB\<cdot> (andOutSBE.setterSB\<cdot>s) = s"
  by(simp add: andOutSBE.getset_eq)

lemma andstep2smap:"andOutSBE.getterSB\<cdot>(andStep state\<cdot>(andInSBE.setterSB\<cdot>input)) = (smap and_smap.smapTransition)\<cdot>input"
  by (simp add: andInSBE.getset_eq and_smap.daut2smap andoutgetset_eq)

lemma "andOutSBE.getterSB\<cdot>(andSpf\<cdot>(andInSBE.setterSB\<cdot>input)) =(smap and_smap.smapTransition)\<cdot>input"
  by(simp add: andSpf_def dawSem_def andstep2smap)

lemma "(smap and_smap.smapTransition)\<cdot>(\<up>(x,y) \<bullet> s) = \<up>(x\<and>y) \<bullet> smap and_smap.smapTransition\<cdot>s"
  by(simp add: dAand_def dAnd_transition_def)

end