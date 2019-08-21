theory AndAutomat

imports automaton.dAutomaton_causal inAndData outAndData

begin

(*State datatype*)
datatype S_and = Single

instance S_and::countable
  by(countable_datatype)


(*And automaton*)
fun dAand_transition::"S_and \<Rightarrow> (bool option \<times> bool option) \<Rightarrow> (S_and \<times> bool option)"where
"dAand_transition S (Some bool1,Some bool2) = (S,(Some (bool1 \<and> bool2)))" |
"dAand_transition S (None,bool2) = (S,(Some False))" |
"dAand_transition S (bool1,None) = (S,(Some False))"


interpretation and_smap:smapGen "dAand_transition" Single "buildAndinSBE" "buildAndOutSBE" "Single"
  apply(unfold_locales)
  using S_and.exhaust by blast

(*And Sem*)

abbreviation andStep::"(S_and \<Rightarrow> (inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>))"where
"andStep \<equiv> dawStateSem and_smap.da"

definition andSpf::"(inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>)"where
"andSpf = dawSem and_smap.da"



(* TESTS: *)
lemma andingetset_eq:"andInSBE.getterSB\<cdot>(andInSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma andoutgetset_eq:"andOutSBE.getterSB\<cdot> (andOutSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma andstep2smap:"andOutSBE.getterSB\<cdot>(andStep Single\<cdot>(andInSBE.setterSB\<cdot>input)) = smap and_smap.smapTransition\<cdot>input"
  by(simp add: and_smap.daut2smap)

lemma "andOutSBE.getterSB\<cdot>(andSpf\<cdot>(andInSBE.setterSB\<cdot>input)) =smap and_smap.smapTransition\<cdot>input"
  apply(simp add: andSpf_def dawSem_def)
  by (metis (mono_tags, lifting) S_and.exhaust andstep2smap)

lemma and_step_t1:"(smap and_smap.smapTransition)\<cdot>(\<up>((Some x),(Some y)) \<bullet> s) = \<up>(Some (x\<and>y)) \<bullet> smap and_smap.smapTransition\<cdot>s"
  by(simp)

lemma and_step_t2:"(smap and_smap.smapTransition)\<cdot>(\<up>((None),(y)) \<bullet> s) = \<up>(Some (False)) \<bullet> smap and_smap.smapTransition\<cdot>s"
  by(simp)

lemma and_step_t3:"(smap and_smap.smapTransition)\<cdot>(\<up>((x),(None)) \<bullet> s) = \<up>(Some (False)) \<bullet> smap and_smap.smapTransition\<cdot>s"
  apply(simp)
  by (metis dAand_transition.elims option.distinct(1) snd_conv)

end