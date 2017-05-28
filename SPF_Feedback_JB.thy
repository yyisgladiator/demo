(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: production ready lemmata for the feedback operator
                 based on Feedback_MW
*)

theory SPF_Feedback_JB
imports SPF_Comp SPF_MW
    
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)
  
(* definitions see SPF_Comp.thy *)


    


(* The general proof structure for cont and spf_well is again an inner to outer approach,
   I start with some lemmata about spfFeedH, then the iteration over the helper, 
   the lub over the helper and finally over the feedback operator itself *)  

(* ----------------------------------------------------------------------- *)
section \<open>spfFeedHelp\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>cont\<close>

(* spfFeed is cont in z to resolve the \<Lambda> *)
lemma spfFeedH_cont[simp]: "cont (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
proof -
  have f1:"cont (\<lambda>z. (Rep_cfun (Rep_SPF f))\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f))"
   by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  thus ?thesis
    by(simp add: Rep_CSPF_def)
qed
  
lemma spfFeedH_cont2[simp]: "cont (\<lambda> x. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
proof -
  have f1: "cont (\<lambda>x. (x \<uplus> z))" (* really important line *)
    by simp
  hence f2:"cont (\<lambda>x. (Rep_cfun (Rep_SPF f))\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f))"
   by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  thus ?thesis
    by(simp add: Rep_CSPF_def)
qed
  
lemma spfFeedH_mono[simp]: "monofun (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
  using cont2mono spfFeedH_cont by blast

    
lemma spfFeedH_continX[simp]: "cont (\<lambda> x. spfFeedH f x)"
proof -
  have "cont (\<lambda>x. \<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
    by(simp add: cont2cont_LAM)
  thus ?thesis
    by(simp add: spfFeedH_def)
qed
  
subsection \<open>dom\<close>
  
lemma spfFeedH_dom [simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f" 
                           and "sbDom\<cdot>sb = spfRan\<cdot>f"
shows "sbDom\<cdot>((spfFeedH f x)\<cdot>sb) = (spfRan\<cdot>f)"
  by (simp add: spfFeedH_def assms(1) assms(2))


(* ----------------------------------------------------------------------- *)
section \<open>iter_spfFeedH\<close>
(* ----------------------------------------------------------------------- *) 
 
subsection \<open>cont_mono\<close>
  
  (* as iterate is cont it can be easily proven that the abbreviation is cont *)
lemma iter_spfFeedH_cont[simp]: "cont (\<lambda>x. iter_spfFeedH f i x)"
  by simp

lemma iter_spfFeedH_mono[simp]: "monofun (\<lambda>x. iter_spfFeedH f i x)"
  by (simp add: cont2mono)
    
lemma iter_spfFeedH_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_spfFeedH f i) x) \<sqsubseteq> ((iter_spfFeedH f i) y)"
  using assms monofun_def by fastforce
    
lemma iter_spfFeedH_chain[simp]: assumes "sbDom\<cdot>x =  spfDom\<cdot>f - spfRan\<cdot>f"
  shows "chain (\<lambda>i. iter_spfFeedH f i x)"
  apply(rule sbIterate_chain)
  by(simp add: assms)
    
    
subsection \<open>dom\<close>
  
lemma iter_spfFeedH_dom: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "sbDom\<cdot>(iter_spfFeedH f i x) = (spfRan\<cdot>f)"
  by (subst iter_sbfix_dom, simp add: assms)
    
    
    
(* ----------------------------------------------------------------------- *)
section \<open>lub_iter_spfFeedH\<close>
(* ----------------------------------------------------------------------- *) 
  
subsection \<open>mono\<close> 
  
(* the lub over the iterations of spfFeedH is monotone if the assumptions hold *)
  (* requires chain property, hence the input must have the right domain *)
lemma lub_iter_spfFeedH_mono_req:  assumes "x \<sqsubseteq> y" and  "sbDom\<cdot>x =  (spfDom\<cdot>f - spfRan\<cdot>f)"
  shows "(\<Squnion>i.(iter_spfFeedH f i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfFeedH f i) y)"
  by (simp add: assms lub_iter_sbfix_mono_req)
  
  (* show that the lub over the iteration fulfills the requirements of a monotone function *)
lemma if_lub_iter_spfFeedH_mono_req: assumes "x \<sqsubseteq> y"
  shows "((\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x)) x)
         \<sqsubseteq> ((\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x)) y)"
  by (rule if_lub_iter_sbfix_mono_req, simp_all add: assms)

  
subsection \<open>cont\<close>  
  
(* the lub of iter_spfFeedH, when applied to a chain, is again a chain *)
  (* this property follows from the monotonicity of lub_iter_spfFeedH *)
lemma chain_lub_iter_spfFeedH: assumes "chain Y" and  "(sbDom\<cdot>(\<Squnion>i. Y i) =  (spfDom\<cdot>f - spfRan\<cdot>f))"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_spfFeedH f ia (Y i))"
  by (simp add: assms chain_lub_iter_sbfix)

subsection \<open>dom\<close>  
  (* the domain of the lub over the iteration is spfRan\<cdot>f *)
   (* this property is required for the spf_well proof *)
lemma lub_iter_spfFeedH_dom[simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "sbDom\<cdot>(\<Squnion>i. iter_spfFeedH f i x) = (spfRan\<cdot>f)"
  by (simp add: lub_iter_sbfix_dom assms)
  
(* ----------------------------------------------------------------------- *)
section \<open>spfFeedbackOperator\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>mono\<close> 
  
  (* as the lub over the iteration fulfilled the requirements for mono and the correct domain is 
    assured via the \<leadsto> the complete operator is monotone *)
lemma spf_feedback_mono[simp]: "monofun (\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) 
                                                      \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x) )"
  by (simp add: if_lub_iter_spfFeedH_mono_req monofun_def)
  
    
subsection \<open>cont\<close>
(* General proof Idea: show that part behind \<leadsto> is cont if input has correct domain and otherwise. 
   This procedure is necessary as the chain properties of iter_spfFeedH only hold if the input 
   domain is correct *)
  
  (* Show that 2nd goal from contI holds if input on spfcomp has the correct domain *)   
lemma chain_if_lub_iter_spfFeedH_domI: assumes "chain Y"
                                       and     "(sbDom\<cdot>(\<Squnion>i. Y i) = (spfDom\<cdot>f - spfRan\<cdot>f))"
shows "(sbDom\<cdot>(\<Squnion>i. Y i) = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto>  (\<Squnion>i.(iter_spfFeedH f i) (\<Squnion>i. Y i))
        \<sqsubseteq>  (\<Squnion>i. (sbDom\<cdot>(Y i) = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto>(\<Squnion>ia. (iter_spfFeedH f ia) (Y i)))"
  apply (rule chain_if_lub_iter_sbfix_case)
    by (simp_all add: assms)

     
  (* based on the previous lemma show that the the 2nd goal from contI holds independently from 
      the input bundle domain *)
lemma chain_if_lub_iter_spfFeedH: assumes "chain Y"
  shows "(sbDom\<cdot>(\<Squnion>i. Y i) = (spfDom\<cdot>f - spfRan\<cdot>f))\<leadsto>(\<Squnion>i. iter_spfFeedH f i (\<Squnion>i. Y i))  
         \<sqsubseteq> (\<Squnion>i. (sbDom\<cdot>(Y i) = (spfDom\<cdot>f - spfRan\<cdot>f))\<leadsto>(\<Squnion>ia. iter_spfFeedH f ia (Y i)))" 
  apply (rule chain_if_lub_iter_sbfix)
    by (simp_all add: assms)
    

(* Based on all the previous lemmata it can now be proven that the feedback operator is 
   continuous and spf_well *)  

  (* Yes :) *)
lemma spf_feed_cont[simp]: "cont (\<lambda>x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) 
                                                      \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x))"
  apply (rule sbfix_contI)
    by simp_all
    
    
lemma spf_feed_well[simp]:
  "spf_well (\<Lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x))"
  apply (simp add: spf_well_def)
  apply (simp only: domIff2)
  apply (simp add: sbdom_rep_eq)
    by (auto)  

 
subsection \<open>range / dom\<close>  
  
lemma spf_feed_dom[simp]: "spfDom\<cdot>(spfFeedbackOperator f) = spfDom\<cdot>f - spfRan\<cdot>f"
  apply(simp add: spfFeedbackOperator2_iter_spfFeedH)
  apply(subst spfDomAbs)
  by(simp_all)

lemma spf_feed_ran[simp]: "spfRan\<cdot>(spfFeedbackOperator f) = spfRan\<cdot>f"
  apply(simp add: spfFeedbackOperator2_iter_spfFeedH)
  apply(subst spfran_least)
  apply(subst spfDomAbs)
  by(simp_all)
    
(* ----------------------------------------------------------------------- *)
section \<open>spfFeed2-basic-prop\<close>
(* ----------------------------------------------------------------------- *) 
(* WARNING this section is covering a obsolete Operator ! ! ! *)
  
subsection \<open>spfFeedH2\<close>
  
  
lemma spfFeedH2_cont[simp]: "cont (\<lambda> z. x \<uplus> (f\<rightleftharpoons>(z\<bar>(spfDom\<cdot>f))))"
  by (metis Rep_CSPF_def cont_Rep_cfun2 cont_compose conthelper)
    
lemma spfFeedH2_continX[simp]: "cont (\<lambda> x. spfFeedH2 f x)"
proof -
  have "\<forall>x. cont(\<lambda>z. x \<uplus> (f\<rightleftharpoons>(z\<bar>(spfDom\<cdot>f))))"
    by simp
  thus ?thesis
    apply (subst spfFeedH2_def)
    by (simp add: cont2cont_LAM)
qed
  
  
lemma spfFeedH2_dom: assumes "sbDom\<cdot>x= spfDom\<cdot>f - spfRan\<cdot>f" 
                     and "sbDom\<cdot>sb = (spfDom\<cdot>f \<union> spfRan\<cdot>f)"
  shows "sbDom\<cdot>((spfFeedH2 f x )\<cdot>sb) = (spfDom\<cdot>f \<union> spfRan\<cdot>f)"
    by (simp add: spfFeedH2_def assms(1) assms(2))

      
subsection \<open>iter_spfCompH3\<close>
    
lemma iter_spfFeedH2_cont[simp]: "cont (\<lambda> x. iter_spfFeedH2 f i x)"
  by simp
    
lemma iter_spfFeedH2_mono[simp]: "monofun (\<lambda> x. iter_spfFeedH2 f i x)"
  by (simp add: cont2mono)
    
lemma iter_spfFeedH2_mono2: assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_spfFeedH2 f i) x) \<sqsubseteq> ((iter_spfFeedH2 f i) y)"
  using assms monofun_def by fastforce
    
lemma iter_spfFeedH2_chain[simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "chain (\<lambda>i. iter_spfFeedH2 f i x)"
  apply (rule sbIterate_chain)
  by (simp add: assms spfFeedH2_dom)
    
lemma iter_spfFeedH2_dom[simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "sbDom\<cdot>(iter_spfFeedH2 f i x) = (spfDom\<cdot>f \<union> spfRan\<cdot>f)"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: assms spfFeedH2_dom)
    
subsection \<open>lub_iter_spfCompH3\<close>
  
lemma lub_iter_spfFeedH2_dom[simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "sbDom\<cdot>(\<Squnion>i. iter_spfFeedH2 f i x) = (spfDom\<cdot>f \<union> spfRan\<cdot>f)"
  apply(subst lub_iter_sbfix_dom)
    by (simp add: assms spfFeedH2_dom)
       
       
(* ----------------------------------------------------------------------- *)
section \<open>old2new spfFeed eq\<close>
(* ----------------------------------------------------------------------- *)   
  
  
lemma iter_spfFeedH_px_chain[simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "chain (\<lambda> i. x \<uplus> iter_spfFeedH f i x)"
    by (simp add: assms)
  
lemma lub_iter_spfFeedH_eq: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "((\<Squnion>i. (x \<uplus> iter_spfFeedH f i x)) \<bar> (spfRan\<cdot>f)) = (\<Squnion>i. (iter_spfFeedH f i) x)"
proof -
  have "(\<Squnion>i. (x \<uplus> iter_spfFeedH f i x)) = x \<uplus> (\<Squnion>i. iter_spfFeedH f i x)"
    by (simp add: assms contlub_cfun_arg)
  thus ?thesis
    using assms by auto
qed
  
lemma lub_iter_spfFeedH2_spfFeedHwX_eq_req_1: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "(iter_spfFeedH2 f i x) \<sqsubseteq> (x \<uplus> (iter_spfFeedH f i x))"
proof (induction i)
  case 0
  then show ?case
    by (simp add: assms)
next
  case (Suc i)
  then show ?case
    apply (unfold iterate_Suc)
    apply (subst spfFeedH2_def, subst spfFeedH_def)
    apply (auto)
    apply (rule sbunion_pref_eq2)
    apply(rule spf_pref_eq, rule sbres_pref_eq)
    by (simp)
qed
  
lemma lub_iter_spfFeedH2_spfFeedHwX_eq_req_2: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "(x \<uplus> iter_spfFeedH f i x) \<sqsubseteq> (iter_spfFeedH2 f (Suc i) x)"
proof (induction i)
  case 0
  then show ?case
    apply (simp add: spfFeedH2_def)
    apply (subst sbunion_pref_eq2)
      by simp_all
next
  case (Suc i)
  then show ?case
    apply (unfold iterate_Suc)
    apply (subst spfFeedH2_def, subst spfFeedH_def)
    apply (auto)
    apply (rule sbunion_pref_eq2)
    apply (rule spf_pref_eq)
      by (rule sbres_pref_eq, simp)
qed
  
  
lemma lub_iter_spfFeedHwX_spfFeedH2_eq: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "(\<Squnion>i. (iter_spfFeedH2 f i x)) = (\<Squnion>i. (x \<uplus> iter_spfFeedH f i x))"
  by (meson assms lub_interl_chain_eq lub_iter_spfFeedH2_spfFeedHwX_eq_req_1 
            lub_iter_spfFeedH2_spfFeedHwX_eq_req_2)
          
lemma lub_iter_spfFeedH2_spfFeedH_eq: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f"
  shows "(\<Squnion>i. (iter_spfFeedH f i) x) = (\<Squnion>i. (iter_spfFeedH2 f i x)) \<bar> (spfRan\<cdot>f)"
    by (simp add: assms lub_iter_spfFeedHwX_spfFeedH2_eq lub_iter_spfFeedH_eq)


lemma spfFeed_and_spfFeed2_eq_req: "(sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> ((\<Squnion>i. (iter_spfFeedH2 f i x))\<bar> (spfRan\<cdot>f))
                 = (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i. (iter_spfFeedH f i) x)"
proof (cases "sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)")
  case True
  then show ?thesis
    by (simp add: lub_iter_spfFeedH2_spfFeedH_eq)
next
  case False
  then show ?thesis 
    by simp
qed
  
  
(* show that new definition is cont and spf_well based on the proof for the old one *)
lemma spf_FeedH2_cont[simp]:
  shows "cont (\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i. (iter_spfFeedH2 f i x))\<bar>(spfRan\<cdot>f))"
  by (simp add: spfFeed_and_spfFeed2_eq_req)
    
lemma spf_FeedH2_well[simp]:
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x =(spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i. (iter_spfFeedH2 f i x))\<bar>(spfRan\<cdot>f))"
  by (simp add: spfFeed_and_spfFeed2_eq_req)
    
    
(* used abbreviations are equal to spfcomp2 function *)   
    (* Substitute with this lemma if you need cont properties for spfFeedH2 *)
lemma spfFeedbackOperator2_to_FeedH2: "spfFeedbackOperator2 f
  = Abs_CSPF(\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i. (iter_spfFeedH2 f i x))\<bar>(spfRan\<cdot>f))"
  apply (simp add: spfFeedbackOperator2_def)
  apply (subst spfFeedH2_def)
  by simp
    
    
(* both definitions deliver an equal result *)
lemma spf_feed_operator_eq: "spfFeedbackOperator f = spfFeedbackOperator2 f"
  apply (subst spfFeedbackOperator2_to_FeedH2)
  apply (subst spfFeedbackOperator2_iter_spfFeedH)
    by (simp add: spfFeed_and_spfFeed2_eq_req)
    
end