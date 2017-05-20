(*  Title:  SPF_FeedComp.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: lemmas for feedback composition with the genranal composition operator
*)

theory SPF_FeedComp_JB
  (* check if StreamCase_Study is really necessary *)
  imports Streams SB SPF SPF_Composition_JB  ParComp_MW_JB SerComp_JB SPF_Templates SPF_MW "CaseStudies/StreamCase_Study"
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>general-lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
(* This is a hack to get \<Longrightarrow> instead of \<longrightarrow> from contI2 *)
lemma mycontI2: assumes "monofun (f::'a::cpo \<Rightarrow> 'b::cpo)" and "(\<And>Y. chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i)))"
  shows "cont f"
  by (simp add: Cont.contI2 assms(1) assms(2))
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)

definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c1, c2, c3)" 
  
definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c3,c2)"

(* use new definition of composition and leave out hide as it is not production ready yet *)
(* sum1EqCh can be used later when hide is introduced *)
definition s1SPF :: "nat SPF" where
"s1SPF \<equiv> spfcomp2 addC append0C"


subsection \<open>component properties\<close>
  (* spf_well and cont proofs left out this should work automatically *)
    
  
lemma addC_dom [simp]: "spfDom\<cdot>addC = {c1,c2}"
  by (simp add: addC_def)
    
lemma addC_ran [simp]: "spfRan\<cdot>addC = {c3}"
  by (simp add: addC_def)
    
lemma addC_rep_eq: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
  by (simp add: addC_def SPF2x1_rep_eq, auto)
    
lemma addC_apply: "([c3 \<mapsto> (add\<cdot>s1\<cdot>s2)]\<Omega>) = addC \<rightleftharpoons> ([c1 \<mapsto> (s1:: nat stream), c2  \<mapsto> (s2:: nat stream)]\<Omega>)"
  by(simp add: addC_def SPF2x1_apply)
    
    
(* append0C *)
lemma append0C_dom [simp]: "spfDom\<cdot>append0C = {c3}"
  by (simp add: append0C_def)
    
lemma append0C_ran [simp]: "spfRan\<cdot>append0C = {c2}"
  by (simp add: append0C_def)
    
lemma append0C_rep_eq: "Rep_CSPF append0C = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>((appendElem2 0)\<cdot>(sb . c3))]\<Omega>))"
  by (simp add: append0C_def SPF1x1_rep_eq, auto)
    
lemma append0C_apply: "append0C \<rightleftharpoons> ([c3 \<mapsto> s]\<Omega>) = ([c2 \<mapsto> (appendElem2 0)\<cdot>(s:: nat stream)]\<Omega>)"
  by(simp add: append0C_def SPF1x1_apply)
    
lemma append0C_apply2: "([c2 \<mapsto> (appendElem2 0)\<cdot>(s:: nat stream)]\<Omega>) = append0C \<rightleftharpoons> ([c3 \<mapsto> s]\<Omega>)"
  by(simp add: append0C_apply)
    
    
subsection \<open>composition prerequirements\<close>
  
lemma spf_comp_well_add_append[simp]: "spfComp_well addC append0C"
  by (simp add: spfComp_well_def)
    
lemma spf_C_add_append[simp]: "C addC append0C = {c1,c2,c3}"
  by (auto simp add: C_def)

lemma spf_L_add_append[simp]: "L addC append0C = {c2, c3}"
  by (auto simp add: L_def)

lemma spf_Oc_add_append[simp]: "Oc addC append0C = {c2, c3}"
  by (auto simp add: Oc_def)

lemma spf_I_add_append[simp]: "I addC append0C = {c1}"
  by(auto simp add: I_def)

lemma spfDom_add_append[simp]: "spfDom\<cdot>(spfcomp addC append0C) = {c1}"
  by(simp add: spfComp_dom_I)

lemma spfRan_add_append[simp]: "spfRan\<cdot>(spfcomp addC append0C) = {c2, c3}"
  by(simp add: spfComp_ran_Oc)
  
    
    
    
(* ----------------------------------------------------------------------- *)
section \<open>sum equality\<close>
(* ----------------------------------------------------------------------- *)
  
(* cont proofs can be lefft out as general cont of spfComp has been showed
  PROOF STRATEGY: equality chain *)
  
lemma sum4_cont[simp]: "cont  (\<lambda>x. (fix\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>((appendElem2 0)\<cdot>z  ))))"
 by (simp add: fix_def)
  
subsection \<open>step1\<close>
  
lemma sum4_lub_iter_eq: "sum4 = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>((appendElem2 0)\<cdot>z ))\<cdot>\<bottom>)"
  by (simp add: sum4_def fix_def appendElem2_def)
    
subsection \<open>step2\<close>
lemma sum4_sb_input_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>z))\<cdot>(\<bottom>))\<cdot>sb"
  apply(subst sum4_lub_iter_eq)
  by (simp add: assms)
    
subsection \<open>step3\<close>
  
lemma step3_inner_mono [simp]: fixes f1:: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "monofun (\<lambda> z. [ch1 \<mapsto> f1\<cdot>x\<cdot>((appendElem2 0)\<cdot>(z . ch2))]\<Omega> )"
  apply(rule monofunI)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  
lemma step3_inner_chain1 [simp]: fixes f:: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y  \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  f\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>((Y i) . ch2))]\<Omega>)"
    apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    
lemma [simp]: "cont (\<lambda>z. \<up>0 \<bullet> z)"
  by (simp add: appendElem_def)
    

lemma step3_inner_lub: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> (\<Squnion>i. f\<cdot>x\<cdot>((appendElem2 0)\<cdot>(Y i . ch2))) = f\<cdot>x\<cdot>((appendElem2 0)\<cdot>((Lub Y). ch2))"
proof -
  assume a1: "chain Y"
  then have "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed
(*
lemma step3_inner_lub: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y \<longrightarrow>  ((\<Squnion>i. f\<cdot>x\<cdot>((appendElem2 0)\<cdot>(Y i . ch2))) = f\<cdot>x\<cdot>((appendElem2 0)\<cdot>((Lub Y). ch2)))"
proof -
  have f1: "\<not> chain (\<lambda>n. Y n . ch2) \<or> f\<cdot>x\<cdot>(\<Squnion>n. appendElem2 0\<cdot>(Y n . ch2)) = (\<Squnion>n. f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Y n . ch2)))"
    using ch2ch_Rep_cfunR contlub_cfun_arg by blast
  { assume "chain (\<lambda>n. Y n . ch2)"
    have "(\<exists>c. \<not> chain (\<lambda>n. Y n . c)) \<or> (chain Y \<longrightarrow> (\<Squnion>n. f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Y n . ch2))) = f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Lub Y . ch2)))"
      using f1 by (metis contlub_cfun_arg sbgetch_lub) }
  then show ?thesis
    using ch2ch_Rep_cfunL ch2ch_Rep_cfunR by blast
qed
  *)

lemma step3_inner_lub_dom: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" 
shows "chain Y \<Longrightarrow> {ch1} = sbDom\<cdot>(\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Y i . ch2))]\<Omega>)"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i. [ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>((Y i) . ch2))]\<Omega>)"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>([ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>((Y i) . ch2))]\<Omega>) = {ch1}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub step3_inner_lub)
  hence f3: "\<forall> i. ([ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>((Y i) . ch2))]\<Omega>)  \<sqsubseteq> (\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Y i . ch2))]\<Omega>)"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed
  
    
  
lemma step3_innter_cont [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "cont (\<lambda> z. [ch1 \<mapsto> f\<cdot>x\<cdot>((appendElem2 0)\<cdot>(z . ch2))]\<Omega> )"
  apply (rule mycontI2, simp only: step3_inner_mono)
  apply(rule sb_below) (* must work *)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub step3_inner_lub)
    by (simp add: step3_inner_lub_dom)

    
lemma sb_in_out_iter_eq: "(iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3
       = iterate i\<cdot>(\<Lambda> z. add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z)))\<cdot>(\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case 
  proof -
    have "\<forall> x. \<forall> sb. ((\<Lambda> z. [c3 \<mapsto> add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>sb) . c3 = (\<Lambda> z. add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z)))\<cdot>(sb . c3)"
      by (simp)
    thus ?case
      apply (unfold iterate_Suc)
      by (simp add: Suc.IH)
  qed
qed
  

lemma test17: "sbDom\<cdot>(iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) = {c3}"
  oops
    
    (* insert lemma sb \<sqsubseteq> sb2 < = > sb . ch \<sqsubseteq> sb2 . ch JUST LIKE: sbres_pref_eq*)
    (*
lemma test16: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "(\<Squnion>i. ((iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3))
        = ((\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>))) .c3)"
   sorry
*)
lemma test18: "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>s\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) . c3 = (\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>s\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3)"
  apply (rule sbgetch_lub)
  apply(rule sbIterate_chain)
  by (simp add: sbdom_rep_eq)
  

    (* resulting lemma of step3 *)
lemma sum4_sb_in_out_pre1: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) sb) .c3"
  by (simp add: sum4_sb_input_eq assms test18 sb_in_out_iter_eq)

    
subsection \<open>step4\<close>  
  
lemma cont2[simp]: "cont (\<lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))"
  sorry (* left out as this is very similar to cont of comp helper *)
        (* requires cont [c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3)) proof first *)
    
lemma step4_dom: 
shows "sbDom\<cdot>((\<Lambda> z.([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2, c3}^\<bottom>)) = {c2, c3}"
proof -
  have "sbDom\<cdot>([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>\<epsilon>)]\<Omega>) = {c3}"
    by (simp add: sbdom_rep_eq)
  moreover
  have "sbDom\<cdot>([c2 \<mapsto> appendElem2 0\<cdot>\<epsilon>]\<Omega>) = {c2}"
    by (simp add: sbdom_rep_eq)
  ultimately
  show ?thesis
    by simp
qed
  
lemma step4_iter_eq: "iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>) . c3 =  iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>) . c3"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
  proof -
    have f1: "\<And> z. (([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>)) . c3 =  add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))"
      apply (subst sbunion_getchL)
      by (simp_all add: sbdom_rep_eq)
    thus ?thesis
      apply (unfold iterate_Suc)
      apply (simp add: f1)
      using Suc.IH by presburger
  qed 
qed
    
  
  
    (* resulting lemma of step 4 *)
lemma sum4_sb_in_out_pre2: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2, c3}^\<bottom>)) sb) .c3"
  apply (simp only: sum4_sb_in_out_pre1 assms)
  apply (subst sbgetch_lub)
   apply(rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (subst sbgetch_lub)
   apply(rule sbIterate_chain)
    apply(simp only: step4_dom)
    by (simp only: step4_iter_eq)
    

  subsection \<open>step5\<close>  
    
lemma cont5[simp]: "cont (\<lambda> z.  ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))"
  sorry (* left out as this is very similar to cont of comp helper *)
        (* requires cont [c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3)) proof first *)
    
lemma sbleast_c2_c3: "{c2, c3}^\<bottom> = {c3}^\<bottom> \<uplus> {c2}^\<bottom>"
  apply(rule sb_eq)
   apply(simp)
   by auto
  
lemma step5_lub_iter_eq_req_1: "iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>)
                               \<sqsubseteq> iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>) "
proof (induction i)
  case 0
  then show ?case
    by (simp only: iterate_0, simp)     
next
  case (Suc i)
  then show ?case sorry
qed
    
lemma step5_lub_iter_eq_req_2: "iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>) 
                               \<sqsubseteq> iterate (Suc i)\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    apply (simp only: iterate_0, unfold iterate_Suc, simp)
    apply (subst sbleast_c2_c3, subst sbunion_pref_eq)
      apply (rule less_SBI, simp_all add: sbLeast_def)
        using insert_dom apply fastforce
      apply (rule less_SBI, simp_all add: sbLeast_def)
        using insert_dom by fastforce      
next
  case (Suc i)
  then show ?case sorry
qed
    
lemma step5_lub_iter_eq: "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>)) = (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>))"
  apply (rule lub_interl_chain_eq)
  using step5_lub_iter_eq_req_1 apply blast
  using step5_lub_iter_eq_req_2 by blast

    
  (* resulting lemma of step 5 *)
lemma sum4_sb_in_out_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)) sb) .c3"
  apply (simp only: sum4_sb_in_out_pre2 assms)
    using step5_lub_iter_eq by presburger
    
    
subsection \<open>step6\<close> 
  
  (* resulting lemma of step 6 *)
lemma add_addSPF_eq: assumes "sbDom\<cdot>sb = {c1}"
  shows "(iter_spfCompH3 addC append0C i) sb
        = iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(sb . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)"
    apply (simp add: spfCompH3_def addC_apply append0C_apply)
proof (induction i)
  case 0
  then show ?case 
    by simp
next
  case (Suc i)
  then show ?case 
    apply (unfold iterate_Suc)
    sorry
qed
    (* We know that sb has domain c1, the criticical point here is the domain of z, which is {c2,c3} 
      after this is shown it should be rather easy to proof the lemma using the apply lemmata
      MAYBE requires another cont proof :/ of (\<Lambda> z. ([c3 \<mapsto> add\<cdot>(sb . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)*)
    
  
  (* FINAL lemma *)
lemma sum4_sb_spf_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Squnion>i. (iter_spfCompH3 addC append0C i) sb) .c3"
  apply (subst add_addSPF_eq, simp add: assms)
    by (simp add: sum4_sb_in_out_eq assms)
  
end
  

