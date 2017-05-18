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
section \<open>sume equality\<close>
(* ----------------------------------------------------------------------- *)
  
(* cont proofs can be lefft out as general cont of spfComp has been showed
  PROOF STRATEGY: equality chain *)
  
lemma sum4_cont[simp]: "cont  (\<lambda>x. (fix\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>(\<up>0\<bullet>(z)))))"
 by (simp add: fix_def)
  
subsection \<open>step1\<close>
  
lemma sum4_lub_iter_eq: "sum4 = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>(\<up>0\<bullet>(z)))\<cdot>\<bottom>)"
  by (simp add: sum4_def fix_def)
    
subsection \<open>step2\<close>
lemma sum4_sb_input_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z)))\<cdot>(\<bottom>))\<cdot>sb"
  apply(subst sum4_lub_iter_eq)
  by (simp add: assms)
    
subsection \<open>step3\<close>
  
lemma step3_inner_mono [simp]: fixes f1:: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "monofun (\<lambda> z. [ch1 \<mapsto> f1\<cdot>x\<cdot>(\<up>0\<bullet>(z . ch2))]\<Omega> )"
  apply(rule monofunI)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  
lemma step3_inner_chain1 [simp]: fixes f:: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y  \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  f\<cdot>(x)\<cdot>(\<up>0\<bullet> ((Y i) . ch2))]\<Omega>)"
    apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    
lemma [simp]: "cont (\<lambda>z. \<up>0 \<bullet> z)"
  by (simp add: appendElem_def)
    
lemma step3_inner_lub [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> (\<Squnion>i. f\<cdot>x\<cdot>(Y i . ch2)) = f\<cdot>x\<cdot>(\<up>0\<bullet> ((Lub Y). ch2))"
proof -
  assume "chain Y"
  then have "(\<Squnion>n. f\<cdot>x\<cdot>(Y n . ch2)) = f\<cdot>x\<cdot>(\<up>0\<bullet> (Lub Y . ch2))"
    sorry
  then show ?thesis
    by metis
qed
  
lemma step3_innter_cont [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "cont (\<lambda> z. [ch1 \<mapsto> f\<cdot>x\<cdot>(\<up>0\<bullet>(z . ch2))]\<Omega> )"
  apply (rule contI2, simp)
     apply (subst sb_below)
    apply (simp add: sbdom_rep_eq )
    sorry
 

     
lemma test12a[simp] : "cont (\<lambda> z. [c3 \<mapsto> add\<cdot>x\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega> )"
 by simp
    
lemma test12b [simp]: "cont (\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>))"
  (* sbFix lemmata would be very handy here :D *)
  (* otherwise this shold be provable manually using the same proof structure as in the feedback 
     cont proof *)
  sorry
    

lemma sb_in_out_iter_eq: "(iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3
       = iterate i\<cdot>(\<Lambda> z. add\<cdot>(x)\<cdot>(\<up>0\<bullet>(z)))\<cdot>(\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case 
  proof -
    have "\<forall> x. \<forall> sb. ((\<Lambda> z. [c3 \<mapsto> add\<cdot>(x)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>sb) . c3 = (\<Lambda> z. add\<cdot>(x)\<cdot>(\<up>0\<bullet>(z)))\<cdot>(sb . c3)"
      by (simp add: test12a)
    thus ?case
      apply (unfold iterate_Suc)
      by (simp add: Suc.IH)
  qed
qed
  

lemma test17: "sbDom\<cdot>(iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) = {c3}"
  sorry
    
    (* insert lemma sb \<sqsubseteq> sb2 < = > sb . ch \<sqsubseteq> sb2 . ch JUST LIKE: sbres_pref_eq*)
    (*
lemma test16: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "(\<Squnion>i. ((iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3))
        = ((\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>))) .c3)"
   sorry
*)
lemma test18: "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>s\<cdot>(\<up>0 \<bullet> z . c3)]\<Omega>)\<cdot>({c3}^\<bottom>)) . c3 = (\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>s\<cdot>(\<up>0 \<bullet> z . c3)]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3)"
  apply (rule sbgetch_lub)
  apply(rule sbIterate_chain)
  by (simp add: sbdom_rep_eq)
  

lemma sum4_sb_in_out_pre1: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) sb) .c3"
  by (simp add: sum4_sb_input_eq assms test18 sb_in_out_iter_eq)

    
subsection \<open>step4\<close>  
  
lemma sum4_sb_in_out_pre2: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(\<up>0\<bullet>(z . c3))]\<Omega>)  \<uplus> ([c2 \<mapsto> (\<up>0\<bullet>(z . c3))]\<Omega>))\<cdot>({c2, c3}^\<bottom>)) sb) .c3"
  apply (simp only: sum4_sb_in_out_pre1 assms)
  apply (subst sbgetch_lub)
   apply(rule sbIterate_chain, simp add: sbdom_rep_eq)
  apply (subst sbgetch_lub)
   apply(rule sbIterate_chain, simp add: sbdom_rep_eq)
    (* show domain of the sbunion see spfCompH3_dom as an example in SPF_Composition_JB *)
    (* show iterate .c3 equality with induction *)
  sorry 
    

subsection \<open>step5\<close>  
  
lemma sum4_sb_in_out_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> (\<up>0\<bullet>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)) sb) .c3"
  sorry (* proof by induction or show via interleaved chains*)
    
    
subsection \<open>step6\<close> 
  
lemma add_addSPF_eq: assumes "sbDom\<cdot>sb = {c1}"
  shows "(iter_spfCompH3 addC append0C i) sb
        = iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(sb . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> (\<up>0\<bullet>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)"
  apply (simp add: spfCompH3_def addC_apply)
    (* substitute with append0C_apply2 *)
    (* Do rest with induction *)
    sorry
    
  
lemma sum4_sb_spf_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Squnion>i. (iter_spfCompH3 addC append0C i) sb) .c3"
  apply (subst add_addSPF_eq, simp add: assms)
    by (simp add: sum4_sb_in_out_eq assms)
  
end
  

