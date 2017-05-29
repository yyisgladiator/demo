(*  Title:  SPF_FeedComp.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: lemmas for feedback composition with the genranal composition operator
*)

theory SPF_FeedComp_JB
  (* check if StreamCase_Study is really necessary *)
  imports SPF_Comp  ParComp_MW_JB  SPF_Templates SPF_MW "CaseStudies/StreamCase_Study"
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>general-lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
(* This is a hack to get \<Longrightarrow> instead of \<longrightarrow> from contI2 *)
lemma mycontI2: assumes "monofun (f::'a::cpo \<Rightarrow> 'b::cpo)" and "(\<And>Y. chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i)))"
  shows "cont f"
  by (simp add: Cont.contI2 assms(1) assms(2))
  
    

  
        (*
proof -
      obtain nn :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat" where
        f1: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
        using po_class.chain_def by moura
      have "nn (\<lambda>n. Y (n * Suc (m))) * Suc (m) \<le> Suc (nn (\<lambda>n. Y (n * Suc (m)))) * Suc (m)"
        by auto
      then show ?thesis
        using f1 by (meson assms po_class.chain_mono)
    qed
*)
    
 (* lubs are equal if chain index is multiplied *)
lemma lub_range_mult:  fixes Y:: "nat \<Rightarrow> 'a::cpo" assumes "chain Y" and "m \<ge> 1"
  shows "(\<Squnion>i. Y (i)) = (\<Squnion>i. Y (m * i))"
proof -
  have f1: "\<forall> (i::nat). i \<le> (m * i)"
    using assms(2) by auto
  have f2: "\<forall> i. Y (i) \<sqsubseteq> Y (m * i)"
    by (simp add: assms(1) f1 po_class.chain_mono)
  have f3: "chain (\<lambda>i. Y (m * i))"
    by (metis (no_types, lifting) Suc_n_not_le_n assms mult.commute nat_le_linear 
          nat_mult_le_cancel_disj po_class.chain_def po_class.chain_mono) 
        
  hence "(\<Squnion>i. Y (m * i)) \<sqsubseteq> (\<Squnion>i. Y (i))"
    using assms lub_below_iff by blast    
  thus ?thesis
    by (simp only: assms below_antisym f2 f3 lub_mono)
qed
  
lemma lub_mult_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "chain Y" and "chain Z" and "m \<ge> 1"
  and "\<And> i. Y (i) = Z (m * i)"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
  apply (simp only: assms(4))
  using assms(2) assms(3) lub_range_mult by fastforce
  
lemma lub_mult2_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "chain Y" and "chain Z"
  and "\<And> i. Y (i) = Z (2 * i)"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
  by (metis One_nat_def Suc_n_not_le_n assms(1) assms(2) assms(3) le_add_same_cancel1 
        lub_mult_shift_eq mult_2 nat_le_linear nat_mult_1_right)
    
lemma cont_pref_eq1I: assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>a \<sqsubseteq> f\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
     
lemma cont_pref_eq2I:  assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>x\<cdot>a \<sqsubseteq> f\<cdot>x\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
    
    
lemma cfun_arg_eqI:  assumes "(a = b)"
  shows "f\<cdot>a = f\<cdot>b"
  by (simp add: assms)
    
lemma spf_arg_eqI:  assumes "(a = b)"
  shows "f\<rightleftharpoons>a = f\<rightleftharpoons>b"
  by (simp add: assms)
    
lemma sbunion_eqI:  assumes "(a = b)" and "(c = d)"
  shows "(a \<uplus> c = b \<uplus> d)"
  by (simp add: assms(1) assms(2))
    
    
lemma sb_one_ch_eqI: assumes "x = y"
  shows "[ch \<mapsto> x]\<Omega> = [ch \<mapsto> y]\<Omega>"
  by (simp add: assms)
    
lemma nat_sb_repackage: assumes "ch \<in> sbDom\<cdot>sb"
  shows "(sb::nat SB) \<bar> {ch} = [ch \<mapsto> sb . ch]\<Omega>"
  apply (rule sb_eq)
  by (simp_all add: assms sbdom_rep_eq)
    
lemma sbres_sbdom_supset: assumes "sbDom\<cdot>sb \<subseteq> cs"
  shows "sb \<bar> cs = sb \<bar> (sbDom\<cdot>sb)"
  by (simp add: assms)
    
lemma sbres_sbdom_supset_inter: 
  shows "sb \<bar> cs = sb \<bar> (cs \<inter> (sbDom\<cdot>sb))"
  by (smt inf.right_idem inf_commute inf_sup_ord(1) sb_eq 
          sbrestrict2sbgetch sbrestrict_sbdom set_mp)
    
    

    
(* used for substitution *)
lemma two_times_one_insert: "2 * (Suc 0) = Suc(Suc(0))"
  by simp
    
lemma two_times_suci_insert: "2 * (Suc i) = (2 + (2*i))"
  by simp

    
lemma two_suc_suc_eq_insert: "2 = Suc(Suc(0))"
  by simp
    
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



abbreviation sum4_sb_inout2_iter :: "nat SB \<Rightarrow> nat \<Rightarrow> nat SB" where
"(sum4_sb_inout2_iter x i) \<equiv>  iterate (i)\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>)"

abbreviation sum4_sb_inout3_iter :: "nat SB \<Rightarrow> nat \<Rightarrow> nat SB" where
"(sum4_sb_inout3_iter x i) \<equiv>  iterate (i)\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>)"


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
lemma sum4_sb_in_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>z))\<cdot>(\<bottom>))\<cdot>sb"
  apply(subst sum4_lub_iter_eq)
  by (simp add: assms)
    
subsection \<open>step3\<close>
  
lemma sum4_sb_inout1_inner_mono [simp]: fixes f1:: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "monofun (\<lambda> z. [ch1 \<mapsto> f1\<cdot>x\<cdot>((appendElem2 0)\<cdot>(z . ch2))]\<Omega> )"
  apply(rule monofunI)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  
lemma sum4_sb_inout1_inner_chain1 [simp]: fixes f:: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y  \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  f\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>((Y i) . ch2))]\<Omega>)"
    apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    

    

lemma sum4_sb_inout1_inner_lub: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> (\<Squnion>i. f\<cdot>x\<cdot>((appendElem2 0)\<cdot>(Y i . ch2))) = f\<cdot>x\<cdot>((appendElem2 0)\<cdot>((Lub Y). ch2))"
proof -
  assume a1: "chain Y"
  then have "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed


lemma sum4_sb_inout1_inner_lub_dom: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" 
shows "chain Y \<Longrightarrow> {ch1} = sbDom\<cdot>(\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Y i . ch2))]\<Omega>)"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i. [ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>((Y i) . ch2))]\<Omega>)"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>([ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>((Y i) . ch2))]\<Omega>) = {ch1}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
  hence f3: "\<forall> i. ([ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>((Y i) . ch2))]\<Omega>)  \<sqsubseteq> (\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(appendElem2 0\<cdot>(Y i . ch2))]\<Omega>)"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed
  
    
  
lemma sum4_sb_inout1_inner_cont [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
  shows "cont (\<lambda> z. [ch1 \<mapsto> f\<cdot>x\<cdot>((appendElem2 0)\<cdot>(z . ch2))]\<Omega> )"
  apply (rule mycontI2, simp only: sum4_sb_inout1_inner_mono)
  apply(rule sb_below) (* must work *)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
    by (simp add: sum4_sb_inout1_inner_lub_dom)

    
lemma sum4_sb_inout1_iter_eq: 
  shows "(iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3
        = iterate i\<cdot>(\<Lambda> z. add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z)))\<cdot>(\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case 
  proof -
    have "\<forall> x. \<forall> sb. ((\<Lambda> z. [c3 \<mapsto> add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>sb) . c3 
                    = (\<Lambda> z. add\<cdot>(x)\<cdot>((appendElem2 0)\<cdot>(z)))\<cdot>(sb . c3)"
      by (simp)
    thus ?case
      apply (unfold iterate_Suc)
      by (simp add: Suc.IH)
  qed
qed
  


lemma sum4_sb_inout1_lub_getch: 
  shows "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>s\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) . c3 
       = (\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>s\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) .c3)"
  apply (rule sbgetch_lub)
  apply(rule sbIterate_chain)
  by (simp add: sbdom_rep_eq)
  

    (* resulting lemma of step3 *)
lemma sum4_sb_inout1_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>)) sb) .c3"
  by (simp add: sum4_sb_in_eq assms sum4_sb_inout1_lub_getch sum4_sb_inout1_iter_eq)

    
subsection \<open>step4\<close>  

lemma contAppendSB_contHelp[simp]: "cont (\<lambda> z. ((appendElem2 0)\<cdot>(z . c3)))"
  by(simp add: appendElem2_def)
    
lemma contAppendSB_monofun[simp]: "monofun (\<lambda> z. ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))"
    apply(rule monofunI)
    apply (rule sb_below)
     apply (simp add: sbdom_insert)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
    
lemma contAppendSB_chain[simp]: "chain Y \<Longrightarrow> chain (\<lambda> i. ([c2 \<mapsto> ((appendElem2 0)\<cdot>((Y i) . c3))]\<Omega>))"
    apply (rule chainI)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
      by (simp add: monofun_cfun po_class.chainE)

lemma contAppendSB_innerLub: "chain Y \<Longrightarrow> (\<Squnion> i. ((appendElem2 0)\<cdot>((Y i) . c3))) = (appendElem2 0)\<cdot>((Lub Y) . c3)"
proof -
  assume a1: "chain Y"
  then have f1: "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed 
  
lemma contAppendSB_innerLub_dom: "chain Y \<Longrightarrow> {c2} = sbDom\<cdot>(\<Squnion>i. ([c2 \<mapsto> ((appendElem2 0)\<cdot>((Y i) . c3))]\<Omega>))"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i.([c2 \<mapsto> ((appendElem2 0)\<cdot>((Y i) . c3))]\<Omega>))"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>(([c2 \<mapsto> ((appendElem2 0)\<cdot>((Y i) . c3))]\<Omega>)) = {c2}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
  hence f3: "\<forall> i. (([c2 \<mapsto> ((appendElem2 0)\<cdot>((Y i) . c3))]\<Omega>))  \<sqsubseteq> (\<Squnion>i. ([c2 \<mapsto> ((appendElem2 0)\<cdot>((Y i) . c3))]\<Omega>))"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed
  
lemma contAppendSB: "cont (\<lambda> z. ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))"
  apply (rule mycontI2, simp only: contAppendSB_monofun)
  apply(rule sb_below)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub contAppendSB_innerLub)
  by (simp add: contAppendSB_innerLub_dom)
    

lemma sum4_sb_inout2_iterable_cont [simp]: 
  shows "cont (\<lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)  
                      \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))"
by (simp add: contAppendSB Rep_CSPF_def)
    
lemma sum4_sb_inout2_dom: 
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
  
lemma sum4_sb_inout2_iter_eq: "iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>)\<cdot>({c3}^\<bottom>) . c3 =  iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>) . c3"
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
lemma sum4_sb_inout2_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((appendElem2 0)\<cdot>(z . c3))]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2, c3}^\<bottom>)) sb) .c3"
  apply (simp only: sum4_sb_inout1_eq assms)
  apply (subst sbgetch_lub)
   apply(rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (subst sbgetch_lub)
   apply(rule sbIterate_chain)
    apply(simp only: sum4_sb_inout2_dom)
    by (simp only: sum4_sb_inout2_iter_eq)
    

subsection \<open>step5\<close> 
    
    
lemma contAddSB_contHelp[simp]: "cont (\<lambda> z.  add\<cdot>(x . c1)\<cdot>(z . c2))"
  by(simp add: appendElem2_def)
    
lemma contAddSB_monofun[simp]: "monofun (\<lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>))"
    apply(rule monofunI)
    apply (rule sb_below)
     apply (simp add: sbdom_insert)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
    
lemma contAddSB_chain[simp]: "chain Y \<Longrightarrow> chain (\<lambda> i. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((Y i) . c2)]\<Omega>))"
    apply (rule chainI)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq)
    apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
    by (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE)

lemma contAddSB_innerLub[simp]: "chain Y \<Longrightarrow> (\<Squnion> i.  add\<cdot>(x . c1)\<cdot>((Y i) . c2)) =  add\<cdot>(x . c1)\<cdot>((Lub Y) . c2)"
proof -
  assume a1: "chain Y"
  then have f1: "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed 
  
lemma contAddSB_innerLub_dom: "chain Y \<Longrightarrow> {c3} = sbDom\<cdot>(\<Squnion>i. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((Y i) . c2)]\<Omega>))"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((Y i) . c2)]\<Omega>))"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>(([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((Y i) . c2)]\<Omega>)) = {c3}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
  hence f3: "\<forall> i. (([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((Y i) . c2)]\<Omega>))  \<sqsubseteq> (\<Squnion>i. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((Y i) . c2)]\<Omega>))"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed
  
lemma contAddSB: "cont (\<lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>))"
  apply (rule mycontI2, simp only: contAddSB_monofun)
  apply(rule sb_below)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub contAddSB_innerLub)
  by (simp add: contAddSB_innerLub_dom)

lemma sum4_sb_inout3_iterable_cont[simp]: "cont (\<lambda> z.  ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))"  
by (simp add: contAddSB contAppendSB Rep_CSPF_def)

    



lemma sum4_sb_inout2_iter_suc_insert: "sum4_sb_inout2_iter x (Suc i) = ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>((sum4_sb_inout2_iter x (i)) . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>((sum4_sb_inout2_iter x (i)) . c3)]\<Omega>)"
  by simp
    
lemma sum4_sb_inout3_iter_suc_insert: "sum4_sb_inout3_iter x (Suc i) = ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((sum4_sb_inout3_iter x (i)) . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>((sum4_sb_inout3_iter x (i)) . c3)]\<Omega>)"
  by simp
  

    
lemma sum4_sb_inout3_iter_two_suc_insert: "sum4_sb_inout3_iter x ((2::nat) *  (Suc i)) = (\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>(sum4_sb_inout3_iter x (Suc (2 * i)))"
  by simp
    

    

    

    
lemma sum4_sb_inout3_iter_2_suc_insert: " (\<Lambda> (z::nat SB). ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 (0::nat)\<cdot>(z . c3)]\<Omega>))\<cdot>(([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c3)]\<Omega>))
                   =  ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>((([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c3)]\<Omega>)) . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>((([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c3)]\<Omega>)) . c3)]\<Omega>)"
  by (subst beta_cfun, simp, simp)
    
lemma sum4_sb_inout3_iter_getch2_insert: "([c2 \<mapsto> appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c3)]\<Omega>) . c2 = appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c3)"
  by simp
 
lemma sum4_sb_inout3_iter_getch3_insert: "([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c2)]\<Omega>) . c3 = add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * Suc i) . c2)"
  by simp
    


    
lemma sum4_sb_inout3_even_iter_ch_eq: assumes "((sum4_sb_inout3_iter x ((2::nat) * i) . c3)) = ((add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c2))) "
  shows "add\<cdot>(x . c1)\<cdot>(appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c3)) = add\<cdot>(x . c1)\<cdot>(appendElem2 (0::nat)\<cdot>(add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c2)))"
    by (simp add: assms)
    
lemma iter_new_ch_eq: "sum4_sb_inout3_iter x ((2::nat) * i) . c3 = add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c2)"
proof (induction i)
  case 0
  then show ?case
    by (simp add: sbdom_rep_eq)
next
  case (Suc i)
  hence "sum4_sb_inout3_iter (x::nat SB) ((2::nat) * (i::nat)) . c3 = add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c2)"
    by blast
  then show ?case
    apply(subst sum4_sb_inout3_iter_two_suc_insert, subst sum4_sb_inout3_iter_suc_insert)
    by (simp add: sbdom_rep_eq)    
qed


    
(* this lemma is very hacky written because simp goes wild *)
lemma step5_lub_iter_eq_req: "sum4_sb_inout2_iter x (Suc i) = sum4_sb_inout3_iter x (2 * (Suc i))"
proof (induction i)
  case 0
  then show ?case
    apply(subst two_times_one_insert)
    apply (unfold iterate_Suc)
    apply auto
      apply(rule sbunion_eqI, rule sb_one_ch_eqI)
      by (simp_all add: sbdom_rep_eq)
next
  case (Suc i)
  then show ?case
    (* TODO: Avoid these substs with ISAR *)
    apply (subst sum4_sb_inout2_iter_suc_insert)
    apply(subst sum4_sb_inout3_iter_two_suc_insert, subst sum4_sb_inout3_iter_suc_insert, subst sum4_sb_inout3_iter_2_suc_insert)
    apply(rule sbunion_eqI)
      (* channel c3 *)
       apply(rule sb_one_ch_eqI)
       apply(rule cfun_arg_eqI)
        apply(subst sbunion_getchR)
      apply (simp add: sbdom_rep_eq, simp only: sum4_sb_inout3_iter_getch2_insert)
      (* channel c2 *)
    apply(rule sb_one_ch_eqI)
    apply(rule cfun_arg_eqI)
       apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
    apply(simp only: sum4_sb_inout3_iter_getch3_insert)
      by (simp only: iter_new_ch_eq)   
  qed
    
lemma step5_lub_iter_eq_req2: "sum4_sb_inout2_iter x (i) = sum4_sb_inout3_iter x (2 * (i))"
  proof (cases "i = 0")
    case True
    then show ?thesis 
      by simp
  next
    case False
    then show ?thesis
      apply (simp add: not0_implies_Suc step5_lub_iter_eq_req)
    proof-
      obtain j where "i = Suc(j)"
        using False not0_implies_Suc by auto
      thus ?thesis
        using step5_lub_iter_eq_req by blast
    qed  
qed
 
  

  
lemma step5_lub_iter_eq: "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(appendElem2 0\<cdot>(z . c3))]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>)) = (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>) \<uplus> ([c2 \<mapsto> appendElem2 0\<cdot>(z . c3)]\<Omega>))\<cdot>({c2, c3}^\<bottom>))"
  apply (rule lub_mult2_shift_eq)
    apply (rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (rule sbIterate_chain, simp add: sbdom_rep_eq)
    by (simp add: step5_lub_iter_eq_req2)

    
  (* resulting lemma of step 5 *)
lemma sum4_sb_in_out_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(x . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)) sb) .c3"
  apply (simp only: sum4_sb_inout2_eq assms)
    using step5_lub_iter_eq by presburger
    
    
  subsection \<open>step6\<close> 
    
lemma sum4_sb_inout3_iter2_insert: "sum4_sb_inout3_iter sb (Suc i) = ([c3 \<mapsto> add\<cdot>(sb . c1)\<cdot>((sum4_sb_inout3_iter sb i) . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>((sum4_sb_inout3_iter sb i) . c3))]\<Omega>)"
  by simp
    

    
lemma test131: "iter_spfCompH3 addC append0C (Suc i) sb =  ((addC \<rightleftharpoons>((sb \<uplus> (iter_spfCompH3 addC append0C i sb))  \<bar> spfDom\<cdot>addC)) \<uplus>  (append0C\<rightleftharpoons>((sb \<uplus> (iter_spfCompH3 addC append0C (i) sb))  \<bar> spfDom\<cdot>append0C)))"
  apply (unfold iterate_Suc, subst spfCompH3_def)
  apply (subst Abs_cfun_inverse2)
   apply (simp only: spfCompH3_cont)
   by simp

lemma sbdom_iter_addc_append: assumes "sbDom\<cdot>sb = {c1}"
  shows "sbDom\<cdot>(iter_spfCompH3 addC append0C i sb) = {c2,c3}"
    by (metis Oc_def assms iter_spfCompH3_dom spf_I_add_append spf_Oc_add_append)
  
  
    
lemma sum4_sb_inout3_iter_dom: "sbDom\<cdot>(sum4_sb_inout3_iter sb i) = {c2, c3}"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
    apply (subst sum4_sb_inout3_iter_suc_insert)
    by (simp add: sbdom_rep_eq)
qed
      
  (* resulting lemma of step 6 *)
lemma add_addSPF_eq: assumes "sbDom\<cdot>sb = {c1}"
  shows "(iter_spfCompH3 addC append0C i) sb
        = iterate i\<cdot>(\<Lambda> z. ([c3 \<mapsto> add\<cdot>(sb . c1)\<cdot>(z . c2)]\<Omega>)  \<uplus> ([c2 \<mapsto> ((appendElem2 0)\<cdot>(z . c3))]\<Omega>))\<cdot>({c2,c3}^\<bottom>)"
proof (induction i)
  case 0
  then show ?case 
    by simp
next
  case (Suc i)
  hence "iter_spfCompH3 addC append0C i sb = sum4_sb_inout3_iter sb i"
    by blast
  then show ?case 
    apply (subst sum4_sb_inout3_iter2_insert, subst test131) (* unroll iterate *)
    apply(rule sbunion_eqI)
      
      (* addC component *)
      apply (subst addC_apply, rule spf_arg_eqI, simp)
      apply(subst sbunion_restrict3)
       (* left bundle prep *)
       apply(subst sbres_sbdom_supset, simp add: assms)
       apply(simp only: assms, subst nat_sb_repackage, simp add: assms)
       (* right bundle prep *)
       apply(subst sbres_sbdom_supset_inter, simp add: sum4_sb_inout3_iter_dom) (* reeduce restriction sect *)
       apply(subst nat_sb_repackage, simp add: sum4_sb_inout3_iter_dom, simp add: sbunion_insert) 
      
       (* append0C component *)
       apply (subst append0C_apply2, rule spf_arg_eqI, simp)
       apply(subst nat_sb_repackage)
         apply(simp add: sum4_sb_inout3_iter_dom)
         by (rule sb_one_ch_eqI, rule sbunion_getchR, simp add: sum4_sb_inout3_iter_dom)   
qed
    
  
  (* FINAL lemma *)
lemma sum4_sb_spf_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Squnion>i. (iter_spfCompH3 addC append0C i) sb) .c3"
  apply (subst add_addSPF_eq, simp add: assms sbdom_rep_eq)
  by (simp add: sum4_sb_in_out_eq assms)
    
    
    
(* ----------------------------------------------------------------------- *)
chapter \<open>more general feedback\<close>
(* ----------------------------------------------------------------------- *)
  
abbreviation gen_fix :: "(nat stream \<rightarrow> nat stream \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream)" where
"gen_fix f1 f2 \<equiv> (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z ))\<cdot>\<bottom>)"

lemma gen_fix_cont[simp]: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont  (\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z ))\<cdot>\<bottom>)"
  by simp
  
subsection \<open>step2\<close>
  
lemma spf_feed_sb_in_eq: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
                         assumes "sb = ([ch1 \<mapsto> s]\<Omega>)"
 shows "(gen_fix f1 f2)\<cdot>s = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>z))\<cdot>(\<bottom>))\<cdot>sb"
 by (simp add: assms)
  

subsection \<open>step3\<close>
  
lemma spf_feed_sb_inout1_inner_mono [simp]: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "monofun (\<lambda> z. [ch1 \<mapsto> f1\<cdot>x\<cdot>(f2\<cdot>(z . ch2))]\<Omega> )"
  apply(rule monofunI)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  
lemma spf_feed_sb_inout1_inner_chain1 [simp]: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y  \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  f1\<cdot>(x)\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)"
    apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    

    

lemma spf_feed_sb_inout1_inner_lub: fixes f :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> (\<Squnion>i. f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))) = f\<cdot>x\<cdot>(f2\<cdot>((Lub Y). ch2))"
proof -
  assume a1: "chain Y"
  then have "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed


lemma spf_feed_sb_inout1_inner_lub_dom: fixes f :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
shows "chain Y \<Longrightarrow> {ch1} = sbDom\<cdot>(\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))]\<Omega>)"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>([ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>) = {ch1}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
  hence f3: "\<forall> i. ([ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)  \<sqsubseteq> (\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))]\<Omega>)"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed
  
    
  
lemma spf_feed_sb_inout1_inner_cont [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(z . ch2))]\<Omega> )"
  apply (rule mycontI2, simp only: spf_feed_sb_inout1_inner_mono)
  apply(rule sb_below) (* must work *)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
   apply (simp add: spf_feed_sb_inout1_inner_lub_dom)
  proof -
    fix Y :: "nat \<Rightarrow> nat SB" and c :: channel
    assume a1: "chain Y"
    then have "\<And>c. (\<Squnion>n. (c\<cdot>(Y n)::channel \<rightarrow> nat stream)) = c\<cdot>(Lub Y)"
      by (simp add: contlub_cfun_arg)
    then show "f\<cdot>x\<cdot>(f2\<cdot>(\<Squnion>n. Y n . ch2)) \<sqsubseteq> (\<Squnion>n. f\<cdot>x\<cdot>(f2\<cdot>(Y n . ch2)))"
      using a1 by (metis ch2ch_Rep_cfunR contlub_cfun_fun po_eq_conv spf_feed_sb_inout1_inner_lub)
  qed
    
lemma spf_feed_sb_inout1_iter_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "(iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) .ch3
        = iterate i\<cdot>(\<Lambda> z. f1\<cdot>(x)\<cdot>(f2\<cdot>(z)))\<cdot>(\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case 
    apply (unfold iterate_Suc)
    by (simp add: Suc.IH)
qed
  

lemma spf_feed_sb_inout1_lub_getch:  fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>s\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) . ch3 
       = (\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>s\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) .ch3)"
  apply (rule sbgetch_lub)
  apply(rule sbIterate_chain)
  by (simp add: sbdom_rep_eq)
    
    (* resulting lemma of step3 *)
lemma spf_feed_sb_inout1_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "sb = ([ch1 \<mapsto> s]\<Omega>)"
  shows "(gen_fix f1 f2)\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) sb) .ch3"
  by (simp add: spf_feed_sb_in_eq assms spf_feed_sb_inout1_lub_getch spf_feed_sb_inout1_iter_eq)
    
    
subsection \<open>step4\<close>  
  
lemma contfun_contHelp[simp]: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. (f2\<cdot>(z . ch3)))"
  by simp
    
lemma contfun_monofun[simp]: fixes f2 :: "nat stream \<rightarrow> nat stream"
shows "monofun (\<lambda> z. ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
    apply(rule monofunI)
    apply (rule sb_below)
     apply (simp add: sbdom_insert)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
    
lemma contfun_chain[simp]: fixes f2 :: "nat stream \<rightarrow> nat stream" 
  shows "chain Y \<Longrightarrow> chain (\<lambda> i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    apply (rule chainI)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    
    
lemma contfun_innerLub: fixes f2 :: "nat stream \<rightarrow> nat stream" 
  shows "chain Y \<Longrightarrow> (\<Squnion> i. (f2\<cdot>((Y i) . ch3))) = f2\<cdot>((Lub Y) . ch3)"
proof -
  assume a1: "chain Y"
  then have f1: "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed 
  
lemma contfun_innerLub_dom: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> {ch2} = sbDom\<cdot>(\<Squnion>i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i.([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>(([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>)) = {ch2}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub sum4_sb_inout1_inner_lub)
  hence f3: "\<forall> i. (([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))  \<sqsubseteq> (\<Squnion>i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed

lemma contfun_getch_cont [simp]: fixes f2 :: "nat stream \<rightarrow> nat stream" 
  shows "cont (\<lambda> z. ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
  apply (rule mycontI2, simp only: contfun_monofun)
  apply(rule sb_below)
   apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub contAppendSB_innerLub 
                        contfun_innerLub_dom)
    using ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg po_eq_conv by blast
  
      
lemma spf_feed_sb_inout2_iterable_cont [simp]: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)  
                      \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
  by simp  
    
lemma spf_feed_sb_inout2_dom: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
shows "sbDom\<cdot>((\<Lambda> z.([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)  \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)) = {ch2, ch3}"
proof -
  have "sbDom\<cdot>([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>\<epsilon>)]\<Omega>) = {ch3}"
    by (simp add: sbdom_rep_eq)
  moreover
  have "sbDom\<cdot>([ch2 \<mapsto> f2\<cdot>\<epsilon>]\<Omega>) = {ch2}"
    by (simp add: sbdom_rep_eq)
  ultimately
  show ?thesis
    by simp
qed
  
lemma spf_feed_inout2_iter_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3"
  shows "iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>) . ch3 
        =iterate i\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>) . ch3"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
  proof -
    have f1: "\<And> z. (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)  \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>)) . ch3 
                    = f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))"
      apply (subst sbunion_getchL)
       apply (simp_all add: sbdom_rep_eq assms)
        using assms by blast
    thus ?thesis
      apply (unfold iterate_Suc)
      apply (simp add: f1)
      using Suc.IH by presburger
  qed 
qed

lemma gen_fix_insert: "(\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z))\<cdot>\<epsilon>)\<cdot>s = (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>s\<cdot>(f2\<cdot>z))\<cdot>\<epsilon>)"
  by simp  
  
    
    (* resulting lemma of step 4 *)
lemma spf_feed_sb_inout2_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "sb = ([ch1 \<mapsto> s]\<Omega>)" and "ch2 \<noteq> ch3"
  shows "(gen_fix f1 f2)\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)  \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)) sb) .ch3"
proof -
  have f1: "(gen_fix f1 f2)\<cdot>s =((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) sb) .ch3"
    using assms(1) spf_feed_sb_inout1_eq by blast
  show ?thesis   
  apply (simp only: f1)
  apply (subst sbgetch_lub)
  apply(rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (subst sbgetch_lub)
   apply(rule sbIterate_chain)
     apply(simp only: spf_feed_sb_inout2_dom)
    by(subst spf_feed_inout2_iter_eq, simp_all add: assms)
qed
  
  
subsection \<open>step5\<close>  
  
lemma spf_feed_sb_inout3_iterable_cont[simp]: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z.  ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))"
  by simp
    
abbreviation spf_feed_sb_inout2_iter :: "(nat stream \<rightarrow> nat stream  \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> nat SB \<Rightarrow> nat \<Rightarrow> nat SB" where
"spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i \<equiv>  iterate (i)\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)"

abbreviation spf_feed_sb_inout3_iter :: "(nat stream \<rightarrow> nat stream  \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> nat SB \<Rightarrow> nat \<Rightarrow> nat SB" where
"spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i \<equiv>  iterate (i)\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)"
  
 


lemma spf_feed_sb_inout2_iter_suc_insert: "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x (Suc i) 
                            = (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>((spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i) . ch3))]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i) . ch3)]\<Omega>))"
  by simp

lemma spf_feed_sb_inout3_iter_suc_insert: "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (Suc i)
                            = (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i) . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i) . ch3)]\<Omega>))"
  by simp
    
lemma spf_feed_sb_inout3_iter_two_suc_insert: "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) *  (Suc i))
   = (\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (Suc (2 * i)))"
  by simp
    
  (*
lemma spf_feed_sb_inout3_iter_2_suc_insert: "(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>(([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch3)]\<Omega>))
        = (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) *  (Suc i))) . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) *  (Suc i))) . ch3)]\<Omega>))"
 *)

(* for the getch inserts use sb_onech_getch_insert *)
  
end
  

