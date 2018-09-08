theory medsBelow

imports medFairAut medUnfairAut

begin


lemma meds_transition_h_below: "medFairTransitionH s m \<subseteq> medUnfairTransitionH s m"
  apply(cases m)
   apply(cases s)
  by auto
  
lemma meds_aut_below: "medUnfairAut \<sqsubseteq> medFairAut"
  apply(rule nda_belowI)
     apply simp_all
   apply(simp add: ndaInitialState.rep_eq medFairAut.rep_eq medUnfairAut.rep_eq)
  apply(simp add: ndaTransition.rep_eq medFairAut.rep_eq medUnfairAut.rep_eq)
  apply(auto simp add: below_fun_def less_set_def)
  using meds_transition_h_below by fastforce

lemma meds_below: "medUnfair s \<sqsubseteq> medFair s"
  unfolding medUnfair_def medFair_def
  by (simp add: fun_belowD meds_aut_below monofunE nda_h_mono)

end