theory medsBelow

imports abpGenerat.Fair99MediumAutomaton abpGenerat.FairMediumAutomaton

begin

lemma fairmedstate_cases: "\<And>x P.      \<lbrakk>x = (FairMediumState Single 0) \<Longrightarrow> P; 
                        \<And>n. x = FairMediumState Single (Suc n) \<Longrightarrow> P\<rbrakk> 
                        \<Longrightarrow> P"
  by (metis FairMediumState.exhaust FairMediumSubstate.exhaust not0_implies_Suc)

lemma setflat_one[simp]: "setflat\<cdot>{x} = x"
  by(simp add: setflat_insert)

lemma meds_transition_h_below: "(fairMediumTransitionH (s,m)) \<sqsubseteq> (fair99MediumTransitionH (s,m))"
  apply(cases m)
  by(rule fairmedstate_cases [of s], auto simp add: less_set_def)+

lemma meds_aut_below: "fairMediumAutomaton \<sqsubseteq> fair99MediumAutomaton"
  apply(rule nda_belowI)
     apply simp_all
   defer
  apply(auto simp add: below_fun_def fairMediumTransition_def fair99MediumTransition_def)
   apply (simp add: meds_transition_h_below)
  apply(simp add: fairMediumInitials_def fair99MediumInitials_def)
  by(auto simp add: less_set_def)

lemma meds_below: "fairMediumStep s \<sqsubseteq> fair99MediumStep s"
  apply(simp add: fairMediumStep_def fair99MediumStep_def)
  by (simp add: fun_belowD meds_aut_below monofunE nda_h_mono)

end