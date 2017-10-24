(*  Title:        SPF
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Extends "Stream Processing Functions"
*)

theory SPF_JB
imports SPF

begin
  
default_sort message 

(*
declare [[show_types]]
declare [[show_consts]]
*)

section \<open>definitions\<close>

definition spfApplyOut :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<rightarrow> 'a SPF" where
"spfApplyOut k \<equiv> (\<Lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"

(*
definition spfApplyOut_pre :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<Rightarrow> channel set \<Rightarrow>  bool" where
"spfApplyOut_pre k g cs \<equiv> \<forall> b. sbDom\<cdot>b = spfDom\<cdot>g \<longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
*)

section \<open>spfApplyOut\<close>

section \<open>resulting spf\<close>
  (* to show properties for the spfApplyOut function we first have to show that it delivers us a 
     valid SPF *)

lemma spfapplyout_spf_cont [simp]: "cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))"
proof (rule spf_contI)
  show "\<And>x y. sbDom\<cdot>x = spfDom\<cdot>g \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> k\<cdot>(g \<rightleftharpoons> x) \<sqsubseteq> k\<cdot>(g \<rightleftharpoons> y)"
    using monofun_cfun_arg spf_pref_eq by blast

  show "\<And>Y. chain Y \<Longrightarrow> sbDom\<cdot>(\<Squnion>i. Y i) = spfDom\<cdot>g \<Longrightarrow> k\<cdot>(g \<rightleftharpoons> (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. k\<cdot>(g \<rightleftharpoons> Y i))"
    proof -
    fix Y :: "nat \<Rightarrow> 'a SB"
    assume a1: "chain Y"
      have f2: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'a SB)::'b) = (\<Squnion>n. c\<cdot>(f n))"
        using contlub_cfun_arg by blast
      have f3: "Rep_CSPF g (Lub Y) = (\<Squnion>n. Rep_CSPF g (Y n))"
        using a1 contlub_cfun_arg by blast
      have "\<forall>f. \<not> chain f \<or> lub\<rightharpoonup>range f = (\<Squnion>n. (f\<rightharpoonup>n::'a SB))"
        using op_the_lub by blast
      hence "(\<Squnion>n. k\<cdot>\<lambda>n. Rep_CSPF g (Y n)\<rightharpoonup>n) = k\<cdot>(g \<rightleftharpoons> Lub Y)"
        using f3 f2 a1 by (metis (no_types) ch2ch_Rep_cfunR op_the_chain)
      thus "k\<cdot>(g \<rightleftharpoons> (\<Squnion>n. Y n)) \<sqsubseteq> (\<Squnion>n. k\<cdot>(g \<rightleftharpoons> Y n))"
        by auto
    qed
qed  

 (* intro lemma for spe_well proofs with spf_applyout *)
lemma spfapplyout_spf_wellI [simp]: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>g \<Longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))"
  apply (rule spf_wellI)
  apply (simp_all add: domIff2)
  by (simp add: assms)

lemma spfapplyout_spf_dom [simp]: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>g \<Longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "spfDom\<cdot>(Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) = spfDom\<cdot>g"
  by (simp add: assms spfDomAbs)
   
lemma spfapplyout_spf_ran [simp]: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>g \<Longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "spfRan\<cdot>(Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) = cs"
  apply (subst spfran_least)
  by (simp add: spfapplyout_spf_dom assms)

lemma spfapplyout_spf_apply: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>g \<Longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
                             and "sbDom\<cdot>sb = spfDom\<cdot>g"
  shows "(Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) \<rightleftharpoons> sb = k\<cdot>(g \<rightleftharpoons>sb)"
  by (simp add: assms)



 (* show that spfApplyOut is continuous in its second argument *)

  (* put this into SPF.thy *)
lemma spfbelowI: assumes "\<And> x. P x \<Longrightarrow> (f x) \<sqsubseteq> (g x)"
                 and "cont (\<lambda> x. (P x) \<leadsto> (f x))" and "cont (\<lambda> x. (P x) \<leadsto> g x)" 
                 and "spf_well (\<Lambda> x. (P x) \<leadsto> (f x))" and "spf_well (\<Lambda> x. (P x) \<leadsto> g x)"
  shows "Abs_SPF (\<Lambda> x. (P x) \<leadsto> (f x)) \<sqsubseteq> Abs_SPF (\<Lambda> x. (P x) \<leadsto> (g x))"
proof -
  have f1:  "\<And> f g. (spf_well f) \<and> (spf_well g) \<Longrightarrow> (f \<sqsubseteq> g) \<Longrightarrow> (Abs_SPF f \<sqsubseteq> Abs_SPF g)"
    by (simp add: below_SPF_def)
  have f2: "\<And> f g. (cont f) \<and> (cont g) \<Longrightarrow> (f \<sqsubseteq> g) \<Longrightarrow> (Abs_cfun f \<sqsubseteq> Abs_cfun g)"
    by (simp add: below_cfun_def)
  have f3: "(\<lambda>x. (P x)\<leadsto>f x) \<sqsubseteq> (\<lambda>x. (P x)\<leadsto>g x)"
    by (simp add: assms(1) below_option_def fun_belowI)
  show ?thesis
    apply (rule f1)
      apply (simp add: assms(4) assms(5))
      apply (rule f2)
        apply (simp add: assms(2) assms(3))
         by (simp add: f3)
qed

  (* put this into SPF.thy *)
lemma spfbelowI2: assumes "cs1 = cs2"  
                 and "\<And> x. (sbDom\<cdot>x = cs2) \<Longrightarrow> (f x) \<sqsubseteq> (g x)" 
                 and "cont (\<lambda> x. (sbDom\<cdot>x = cs1) \<leadsto> (f x))" 
                 and "cont (\<lambda> x. (sbDom\<cdot>x = cs2) \<leadsto> g x)" 
                 and "spf_well (\<Lambda> x. (sbDom\<cdot>x = cs1) \<leadsto> (f x))" 
                 and "spf_well (\<Lambda> x. (sbDom\<cdot>x = cs2) \<leadsto> g x)"
  shows "Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = cs1) \<leadsto> (f x)) \<sqsubseteq> Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = cs2) \<leadsto> (g x))"
proof -
  have f1:  "\<And> f g. (spf_well f) \<and> (spf_well g) \<Longrightarrow> (f \<sqsubseteq> g) \<Longrightarrow> (Abs_SPF f \<sqsubseteq> Abs_SPF g)"
    by (simp add: below_SPF_def)
  have f2: "\<And> f g. (cont f) \<and> (cont g) \<Longrightarrow> (f \<sqsubseteq> g) \<Longrightarrow> (Abs_cfun f \<sqsubseteq> Abs_cfun g)"
    by (simp add: below_cfun_def)
  have f3: "(\<lambda>x. (sbDom\<cdot>x = cs1)\<leadsto>f x) \<sqsubseteq> (\<lambda>x. (sbDom\<cdot>x = cs2) \<leadsto>g x)"
    apply (subst assms(1))
    by (simp add: assms(2) below_option_def fun_belowI)
  show ?thesis
    apply (rule f1)
      apply (simp add: assms(5) assms(6))
      apply (rule f2)
        apply (simp add: assms(3) assms(4))
         by (simp add: f3)
qed

lemma spfapplyout_mono [simp]:  assumes "\<forall> cin. \<exists> cout. \<forall>b. sbDom\<cdot>b = cin \<longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cout"
  shows " monofun (\<lambda>g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x)))"
proof -
  have f1: "\<And> x. spf_well (\<Lambda> xa. (sbDom\<cdot>xa = spfDom\<cdot>x)\<leadsto>k\<cdot>(x \<rightleftharpoons> xa))"
  apply (rule spf_wellI)
  apply (simp_all add: domIff2)
    sorry

  have f2: "\<And> y. spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>y)\<leadsto>k\<cdot>(y \<rightleftharpoons> x))"
  apply (rule spf_wellI)
  apply (simp_all add: domIff2)
    sorry


  show ?thesis
    apply (rule monofunI)
    apply (rule spfbelowI2)
    apply (simp_all add: assms)
    apply (simp add: spfdom_eq)
    apply (metis (full_types) below_SPF_def below_option_def below_refl monofun_cfun_arg 
                                monofun_cfun_fun)
    by (simp_all add: f1 f2)
qed

lemma spfapplyout_chain [simp]: assumes "chain Y"
  shows "Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(\<Squnion>i. Y i))\<leadsto>k\<cdot>((\<Squnion>i. Y i) \<rightleftharpoons> x)) 
          \<sqsubseteq> (\<Squnion>i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
  by simp


lemma spfapplyout_cont [simp]:  assumes "\<forall> cin. \<exists> cout. \<forall>b. sbDom\<cdot>b = cin \<longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cout"
  shows "cont (\<lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"
  apply (rule contI2)
  using assms apply auto[1]
 
  sorry

(* further properties *)

lemma spfapplyout_insert:
  shows "spfApplyOut k\<cdot>f =  Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))"
  by (simp add: spfApplyOut_def)

lemma spfapplyout_dom: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>f \<Longrightarrow> sbDom\<cdot>(k\<cdot>(f \<rightleftharpoons> b)) = cs" 
  shows "spfDom\<cdot>(spfApplyOut k\<cdot>f) = spfDom\<cdot>f"
  apply (simp add: spfapplyout_insert)
  by (simp add: assms)

lemma spfapplyout_ran: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>f \<Longrightarrow> sbDom\<cdot>(k\<cdot>(f \<rightleftharpoons> b)) = cs" 
  shows "spfRan\<cdot>(spfApplyOut k\<cdot>f) = cs"
  apply (simp add: spfapplyout_insert)
  by (simp add: assms)

lemma spfapplyout_apply:  assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>f \<Longrightarrow> sbDom\<cdot>(k\<cdot>(f \<rightleftharpoons> b)) = cs" 
                              and "sbDom\<cdot>sb = spfDom\<cdot>f"
  shows "(spfApplyOut k\<cdot>f) \<rightleftharpoons> sb = k\<cdot>(f \<rightleftharpoons>sb)"
  apply (simp add: spfapplyout_insert)
  by (simp add: spfapplyout_spf_apply assms)


end