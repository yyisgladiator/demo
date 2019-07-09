theory AndAutomat

imports automaton.dAutomaton_causal andAutomat_inc

begin
(*And automaton*)
fun dAand_transition::"S_and \<Rightarrow> (bool\<times> bool) \<Rightarrow> (S_and \<times> bool)"where
"dAand_transition S (bool1,bool2) = (S,(bool1 \<and> bool2))"


interpretation and_smap:smapGen "dAand_transition" Single "True" "buildAndinSBE" "buildAndoutSBE" "Single"
  apply(unfold_locales)
  using S_and.exhaust by blast

(*And Sem*)

abbreviation andStep::"(S_and \<Rightarrow> (inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>))"where
"andStep \<equiv> dawStateSem and_smap.da"

definition andSpf::"(inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>)"where
"andSpf = dawSem and_smap.da"


lemma andingetset_eq:"andInSBE.getterSB\<cdot>(andInSBE.setterSB\<cdot>s) = s"
  by(simp add: andInSBE.getset_eq)

lemma andoutgetset_eq:"andOutSBE.getterSB\<cdot> (andOutSBE.setterSB\<cdot>s) = s"
  by(simp add: andOutSBE.getset_eq)

lemma andstep2smap:"andOutSBE.getterSB\<cdot>(andStep state\<cdot>(andInSBE.setterSB\<cdot>input)) = smap (\<lambda>e. snd(dAand_transition state e))\<cdot>input"
  apply(subst and_smap.daut2smap)
  by (simp add: andInSBE.getset_eq and_smap.daut2smap andoutgetset_eq)

lemma "andOutSBE.getterSB\<cdot>(andSpf\<cdot>(andInSBE.setterSB\<cdot>input)) =smap (\<lambda>e. snd(dAand_transition state e))\<cdot>input"
  by(simp add: andSpf_def dawSem_def andstep2smap)

lemma "(smap and_smap.smapTransition)\<cdot>(\<up>(x,y) \<bullet> s) = \<up>(x\<and>y) \<bullet> smap and_smap.smapTransition\<cdot>s"
  by(simp add: dAand_def dAnd_transition_def)

end