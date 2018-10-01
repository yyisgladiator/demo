theory ndaStateRefine

imports ndAutomaton

begin
default_sort type


definition isStateRefined :: "('s1, 'm::message) ndAutomaton \<Rightarrow> ('s2, 'm::message) ndAutomaton \<Rightarrow> bool" where
"isStateRefined nda1 nda2 = (ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2 \<and> ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2 
                  \<and>  (\<exists>f. \<forall>s sbe t out. 
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe))))
                      ))"



lemma ndaconcout_staterefine: assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "ndaConcOutFlatten (ndaDom\<cdot>nda1) (ndaRan\<cdot>nda1) ((ndaTransition\<cdot>nda1) (s, e)) 
      = ndaConcOutFlatten (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) ((ndaTransition\<cdot>nda2) (f s, e))"
  apply(simp add: ndaConcOutFlatten_def)
  apply(simp add: setrevImage_def)
  sorry


lemma nda_h_inner_staterefine: assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "nda_h_inner nda1 h s = nda_h_inner nda2 h (f s)"
  apply(simp add: nda_h_inner_def Let_def ndaHelper2_def)
  apply(subst dom_eq, subst ran_eq)
  by(subst ndaconcout_staterefine, simp_all add: assms)
  

(* I cannot use "isStateRefined" because i need the f *)
lemma nda_h_staterefine: assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "nda_h nda1 s = nda_h nda2 (f s)"
  apply(simp add: nda_h_def)
  sorry







lemma nda_h_final_back: assumes "\<And>state sbe. sbeDom sbe = ndaDom\<cdot>nda \<Longrightarrow> spsConcIn (sbe2SB sbe) (other state) = 
  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state,sbe)) (other)"
  and "\<And> state. uspecDom\<cdot>(other state) = ndaDom\<cdot>nda" and "\<And> state. uspecRan\<cdot>(other state) = ndaRan\<cdot>nda"
shows "nda_h nda = other" 
  oops




end