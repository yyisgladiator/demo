(*  Title:  SPF_FeedComp.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: Extension for SPFComp, handles lifting of feedback composition
*)

theory SPF_FeedComp
  (* check if StreamCase_Study is really necessary *)
  imports SPF_Comp  SPF_Templates
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>general-lemmas\<close>
(* ----------------------------------------------------------------------- *)

    
lemma nat_sb_repackage: assumes "ch \<in> sbDom\<cdot>sb"
  shows "(sb::nat SB) \<bar> {ch} = [ch \<mapsto> sb . ch]\<Omega>"
  apply (rule sb_eq)
  by (simp_all add: assms sbdom_rep_eq)
    


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
  
  (* generalization of sum4 *)
abbreviation gen_fix :: "(nat stream \<rightarrow> nat stream \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream)" where
"gen_fix f1 f2 \<equiv> (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z ))\<cdot>\<bottom>)"  
    
abbreviation spf_feed_sb_inout2_iter :: "(nat stream \<rightarrow> nat stream  \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> nat SB \<Rightarrow> nat \<Rightarrow> nat SB" where
"spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i \<equiv>  iterate (i)\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)"

abbreviation spf_feed_sb_inout3_iter :: "(nat stream \<rightarrow> nat stream  \<rightarrow> nat stream) \<Rightarrow> (nat stream \<rightarrow> nat stream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> nat SB \<Rightarrow> nat \<Rightarrow> nat SB" where
"spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i \<equiv>  iterate (i)\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)"    
    
    
(* ----------------------------------------------------------------------- *)
section \<open>more general feedback\<close>
(* ----------------------------------------------------------------------- *)
  
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
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
  hence f3: "\<forall> i. ([ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)  \<sqsubseteq> (\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))]\<Omega>)"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed
  
    
  
lemma spf_feed_sb_inout1_inner_cont [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(z . ch2))]\<Omega> )"
  apply (rule mycontI2, simp only: spf_feed_sb_inout1_inner_mono)
  apply(rule sb_below) (* must work *)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
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
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
  hence f3: "\<forall> i. (([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))  \<sqsubseteq> (\<Squnion>i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed

lemma contfun_getch_cont [simp]: fixes f2 :: "nat stream \<rightarrow> nat stream" 
  shows "cont (\<lambda> z. ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
  apply (rule mycontI2, simp only: contfun_monofun)
  apply(rule sb_below)
   apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub 
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
lemma spf_feed_sb_inout3_iter_2_suc_insert: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream" 
shows " (\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>(([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch3)]\<Omega>))
                   =  (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch3)]\<Omega>)) . ch2)]\<Omega>)
                       \<uplus> ([ch2 \<mapsto> f2\<cdot>((([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch3)]\<Omega>)) . ch3)]\<Omega>))"
  apply (subst beta_cfun, simp)
    by blast
    

(* for the getch inserts use sb_onech_getch_insert *)
      
lemma spf_feed_sb_inout3_even_iter_ch_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"  
 (* assumes "((sum4_sb_inout3_iter x ((2::nat) * i) . c3)) = ((add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c2))) " and "ch2 \<noteq> ch3"
  shows "add\<cdot>(x . c1)\<cdot>(appendElem2 (0::nat)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c3)) = add\<cdot>(x . c1)\<cdot>(appendElem2 (0::nat)\<cdot>(add\<cdot>(x . c1)\<cdot>(sum4_sb_inout3_iter x ((2::nat) * i) . c2)))" *)
  assumes "((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch3)) = ((add\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch2)))" 
  shows "f1\<cdot>(x . ch1)\<cdot>(appendElem2 (0::nat)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch3)) = f1\<cdot>(x . ch1)\<cdot>(appendElem2 (0::nat)\<cdot>(add\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch2)))"
    by (simp add: assms)
   
 
lemma spf_feed_iter_new_ch_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch3 = f1\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch2)"
  proof (induction i)
    case 0
    then show ?case 
      apply (simp add: sbdom_rep_eq)
      by (simp add: assms(2))
  next
    case (Suc i)
    hence "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i) . ch3 = f1\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i) . ch2)"
      by blast
    then show ?case
      apply (subst spf_feed_sb_inout3_iter_two_suc_insert, subst spf_feed_sb_inout3_iter_suc_insert)
      apply(simp add: sbgetch_rep_eq) 
      apply (subst sbunion_getchR, simp add: sbdom_rep_eq)
      apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
         using assms apply blast
         apply(simp add: sbdom_rep_eq)
       apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
         using assms apply blast
         apply (simp)
         apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
         using assms apply blast
         by simp             
     qed
       
(* this lemma is very hacky written because simp goes wild *)
lemma spf_feed_step5_lub_iter_eq_req: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x (Suc i) = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * (Suc i))"
proof (induction i)
  case 0
  then show ?case
    apply(subst two_times_one_insert)
    apply (unfold iterate_Suc)
    apply auto
    apply(rule sbunion_eqI, rule sb_one_ch_eqI)
     apply (simp_all add: sbdom_rep_eq assms)
    apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
      using assms apply blast
      by simp
next
  case (Suc i)
  hence "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x (Suc i) = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * Suc i)"
    by blast
  then show ?case
    apply (subst spf_feed_sb_inout2_iter_suc_insert)
    apply(subst spf_feed_sb_inout3_iter_two_suc_insert, subst spf_feed_sb_inout3_iter_suc_insert, subst spf_feed_sb_inout3_iter_2_suc_insert)
    apply(rule sbunion_eqI)
      (* channel ch3 *)
     apply(rule sb_one_ch_eqI)
     apply(rule cfun_arg_eqI)
     apply(subst sbunion_getchR)
      apply (simp add: sbdom_rep_eq)
     apply (simp only: sb_onech_getch_insert)
      (* channel ch2 *) 
    apply(rule sb_one_ch_eqI)
    apply(rule cfun_arg_eqI)
    apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
    using assms apply blast
    apply (simp only: sb_onech_getch_insert)
      by (rule spf_feed_iter_new_ch_eq, simp_all add: assms)     
  qed
    
lemma spf_feed_step5_lub_iter_eq_req2: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i)"
proof (cases "i = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  hence "0 < i \<Longrightarrow> spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i)"
    proof -
    obtain j where "i = Suc(j)"
      using False not0_implies_Suc by auto
    thus ?thesis
      using spf_feed_step5_lub_iter_eq_req assms by blast
  qed
  then show ?thesis
    using False by blast      
qed
 
lemma spf_feed_step5_lub_iter_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "(\<Squnion>i. spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i) = (\<Squnion>i. spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i)"
  apply (rule lub_mult2_shift_eq)
    apply (rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (rule sbIterate_chain, simp add: sbdom_rep_eq)
  using spf_feed_step5_lub_iter_eq_req2 assms by simp
    
  (** resulting lemma of step 5 *)
lemma spf_feed_sb_in_out_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream" fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "sb = ([ch1 \<mapsto> s]\<Omega>)" and "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "(gen_fix f1 f2)\<cdot>s = (\<lambda> x. (\<Squnion>i. spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i)) sb . ch3"
proof -
  have f1: "(gen_fix f1 f2)\<cdot>s = (\<Squnion>i. spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 sb i) . ch3"
    by (rule spf_feed_sb_inout2_eq, simp_all add: assms)
  show ?thesis
    apply (subst f1)
    using spf_feed_step5_lub_iter_eq assms by presburger
qed
  
end
  

