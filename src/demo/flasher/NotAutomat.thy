theory NotAutomat

imports automaton.dAutomaton_causal notAutomat_inc emptychanData

begin
(*Not automaton*)
fun dAnot_transition::"S_not \<Rightarrow> (bool) \<Rightarrow> (S_not \<times> bool)"where
"dAnot_transition S (bool) = (S,(\<not>bool))"


interpretation not_smap:smapGen "dAnot_transition" Single "buildNotinSBE" "buildNotoutSBE" Single
  apply(unfold_locales)
  apply auto[1]
  done

abbreviation notStep::"(S_not \<Rightarrow> (inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>))"where
"notStep \<equiv> dawStateSem not_smap.da"

definition notSpf::"(inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>)"where
"notSpf = dasSem (dAutomaton_weak.extend not_smap.da (dAutomaton_strong.fields (notOutSBE.setter True)))"


lemma dasinitout_well:"(dasInitOut
         (dAutomaton_weak.extend daw
           (dAutomaton_strong.fields
             sbe))) = sbe" (*How proof this?*)
  sorry

lemma das2daw_trunc_well:"dAutomaton_weak.truncate
                (dAutomaton_weak.extend da
                  (dAutomaton_strong.fields sbe)) = da" (*How proof this?*)
  sorry

lemma notingetset_eq:"notInSBE.getterSB\<cdot>(notInSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma notoutgetset_eq:"notOutSBE.getterSB\<cdot> (notOutSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma notstep2smap:"notOutSBE.getterSB\<cdot>(notStep state\<cdot>(notInSBE.setterSB\<cdot>input)) = (smap not_smap.smapTransition)\<cdot>input"
  by (metis (full_types) S_not.exhaust not_smap.daut2smap)

thm dAutomaton_weak.select_convs


lemma "notOutSBE.getterSB\<cdot>(notSpf\<cdot>(notInSBE.setterSB\<cdot>input)) = \<up>True \<bullet>(smap not_smap.smapTransition)\<cdot>input"
  by(simp add: notSpf_def dasSem_def dasinitout_well das2daw_trunc_well dawSem_def notstep2smap)

lemma not_step:"smap not_smap.smapTransition\<cdot>(\<up>bool \<bullet> s) = \<up>(\<not>bool) \<bullet> smap not_smap.smapTransition\<cdot>s"
  by simp

end