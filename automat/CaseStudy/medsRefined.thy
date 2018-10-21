theory medsRefined

imports medFairStep medUnfairStep automat.ndaStateRefine

begin

lemma "medUnfair \<sqsubseteq> medFair n"
  apply(simp add: medUnfair_def medFair_def)
  oops


end
