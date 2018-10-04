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
  oops


lemma helper_todo: assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "nda_h_inner nda1 h s = nda_h_inner nda2 h (f s)"
  apply(simp add: nda_h_inner_def Let_def ndaHelper2_def)
  apply(subst dom_eq, subst ran_eq)
 (*  apply(subst ndaconcout_staterefine, simp_all add: assms) *)
  oops



lemma ndaimage_staterefine2:
assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "(setrevImage (\<lambda>(s, sb). ndaTodo_h (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) (s, sb) (\<lambda>s. h (f s)))
       ((ndaTransition\<cdot>nda1) (x, e))) 
\<sqsubseteq> (setrevImage (\<lambda>(s, sb). ndaTodo_h (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) (s, sb) h) ((ndaTransition\<cdot>nda2) (f x, e)))"
  apply(simp add: setrevImage_def ndaTodo_h_def)
  sorry                       

lemma ndaimage_staterefine2:
assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "(setrevImage (\<lambda>(s, sb). ndaTodo_h (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) (s, sb) (\<lambda>s. h (f s)))
       ((ndaTransition\<cdot>nda1) (x, e))) 
\<sqsubseteq> (setrevImage (\<lambda>(s, sb). ndaTodo_h (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) (s, sb) h) ((ndaTransition\<cdot>nda2) (f x, e)))"
  apply(simp add: setrevImage_def ndaTodo_h_def)

lemma ndaconcout_staterefine2:
assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "ndaConcOutFlatten (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) ((ndaTransition\<cdot>nda1) (x, e)) (\<lambda>s::'a. h (f s)) 
  = ndaConcOutFlatten (ndaDom\<cdot>nda2) (ndaRan\<cdot>nda2) ((ndaTransition\<cdot>nda2) (f x, e)) h"
  apply(simp add: ndaConcOutFlatten_def)
  sorry

lemma nda_h_inner_staterefine: 
assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "nda_h_inner nda1 (\<lambda>s::'a. h (f s)) \<sqsubseteq> (\<lambda>s::'a. nda_h_inner nda2 h (f s))"
  apply(simp add: nda_h_inner_def Let_def ndaHelper2_def)
  apply(simp add: dom_eq ran_eq)
  unfolding below_fun_def
  apply auto
  by(subst ndaconcout_staterefine2, simp_all add: assms)


lemma lfp_lfp_below:
    assumes "monofun g1" 
    and "monofun g2"
    and "goodFormed C1 g1" 
    and "goodFormed C2 g2"
    and "C1 \<in> DIV" 
    and "C2 \<in> DIV"
    and "\<And>x. g2 (f x) \<sqsubseteq> f (g1 x)"
    and "\<And>x. x\<in>C1 \<Longrightarrow> f x \<in>C2"
  shows "(lfp C2 g2) \<sqsubseteq> f (lfp C1 g1)"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) below_refl lfp_all)


(* I cannot use "isStateRefined" because i need the f *)
lemma nda_h_staterefine: assumes dom_eq: "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2" and ran_eq: "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "\<And>s sbe t out. sbeDom sbe = ndaDom\<cdot>nda1 \<Longrightarrow>  (
                        ((t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda1) (s, sbe))))
                          \<longleftrightarrow>
                        ((f t, out) \<in> ((inv Rev) ((ndaTransition\<cdot>nda2) (f s, sbe)))))"
shows "nda_h nda1 \<sqsubseteq> (\<lambda>h s. h (f s)) (nda_h nda2)"
  apply(simp add: nda_h_def)
  apply(subst lfp_lfp_below [of "nda_h_inner nda2" ])
         apply (simp add: nda_h_inner_monofun)+
  apply (auto simp add: nda_inner_good)+
  apply (simp add: nda_h_valid_domain)+
  apply (simp add: nda_h_inner_staterefine assms)
  by (simp add: SetPcpo.setify_def dom_eq ran_eq)








end