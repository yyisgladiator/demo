theory NotAutomat

imports automaton.dAutomaton_causal notAutomat_inc

begin
(*Not automaton*)
fun dAnot_transition::"S_not \<Rightarrow> (bool option) \<Rightarrow> (S_not \<times> bool option)"where
"dAnot_transition S (Some bool) = (S,(Some (\<not>bool)))" |
"dAnot_transition S (None) = (S,(Some True))"

interpretation not_smap:smapGen "dAnot_transition" Single "buildNotinSBE" "buildNotoutSBE" Single
  apply(unfold_locales)
  using S_not.exhaust by auto

definition "notStrong  \<equiv>  daw2das not_smap.da (notOutSBE.setter (Some True))"

abbreviation notStep::"(S_not \<Rightarrow> (inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>))"where
"notStep \<equiv> dawStateSem not_smap.da"

definition notSpf::"(inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>)"where
"notSpf = dasSem notStrong"

lemma notingetset_eq:"notInSBE.getterSB\<cdot>(notInSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma notoutgetset_eq:"notOutSBE.getterSB\<cdot> (notOutSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma notstep2smap:"notOutSBE.getterSB\<cdot>(notStep state\<cdot>(notInSBE.setterSB\<cdot>input)) = (smap not_smap.smapTransition)\<cdot>input"
  by (metis (mono_tags, lifting) S_not.exhaust not_smap.daut2smap somechannotempty)

lemma "notOutSBE.getterSB\<cdot>(notSpf\<cdot>(notInSBE.setterSB\<cdot>input)) = \<up>(Some True) \<bullet>(smap not_smap.smapTransition)\<cdot>input"
  by(simp add: notSpf_def dasSem_def dasinitout_well das2daw_trunc_well dawSem_def notstep2smap notStrong_def daw2das_def)

lemma not_step_t1:"smap not_smap.smapTransition\<cdot>(\<up>(Some bool) \<bullet> s) = \<up>(Some (\<not>bool)) \<bullet> smap not_smap.smapTransition\<cdot>s"
  by simp

lemma not_step_t2:"smap not_smap.smapTransition\<cdot>(\<up>(None) \<bullet> s) = \<up>(Some True) \<bullet> smap not_smap.smapTransition\<cdot>s"
  by simp

end