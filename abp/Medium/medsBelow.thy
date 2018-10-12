theory medsBelow

imports abpGenerat.Fair99MediumAutomaton abpGenerat.FairMediumAutomaton

begin


lemma meds_transition_h_below: "(fairMediumTransitionH (s,m)) \<sqsubseteq> (fair99MediumTransitionH (s,m))"
  apply(cases m)
   apply(cases s)
  sorry

lemma meds_aut_below: "fairMediumAutomaton \<sqsubseteq> fair99MediumAutomaton"
  apply(rule nda_belowI)
     apply simp_all
   apply(simp add: fairMediumInitials_def fair99MediumInitials_def)
  sorry

lemma meds_below: "fairMediumStep s \<sqsubseteq> fair99MediumStep s"
  sorry

end