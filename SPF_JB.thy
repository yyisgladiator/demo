(*  Title:        SPF
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Extends "Stream Processing Functions" by SpfApplyIn/Out etc ...
*)

theory SPF_JB
imports SPF

begin
  
default_sort message 

declare [[show_types]]

declare [[show_consts]]

section \<open>definitions\<close>

definition spfApplyOut :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<rightarrow> 'a SPF" where
"spfApplyOut k \<equiv> (\<Lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"

definition spfApplyIn :: "('m SB \<rightarrow> 'm SB) \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where 
"spfApplyIn k \<equiv> \<Lambda> g. Abs_CSPF (\<lambda>x. (Rep_CSPF g)(k\<cdot>x))" 
 
(*
definition spfApplyIn2 :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<rightarrow> 'a SPF" where
"spfApplyIn2 k \<equiv> (\<Lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>(k\<cdot>x) = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"
*)

(*
definition spfApplyOut_pre :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<Rightarrow> channel set \<Rightarrow>  bool" where
"spfApplyOut_pre k g cs \<equiv> \<forall> b. sbDom\<cdot>b = spfDom\<cdot>g \<longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
*)

lemma spfapplyin_eq_pre: "(Rep_CSPF spf)(f\<cdot>x) = (sbDom\<cdot>(f\<cdot>x) = spfDom\<cdot>spf) \<leadsto> (spf \<rightleftharpoons>(f\<cdot>x))"
  by (metis domIff option.collapse spfLeastIDom spf_sbdom2dom spfdom2sbdom)

(*
 (* convert between original and proof oriented definition *)
lemma spfapplyin_eq: "spfApplyIn k = spfApplyIn2 k"
  apply (subst spfApplyIn_def, subst spfApplyIn2_def)
  apply (subst spfapplyin_eq_pre)
  by simp
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

lemma spfbelowI3: assumes "\<And> x. (sbDom\<cdot>x = cs) \<Longrightarrow> (f x) \<sqsubseteq> (g x)"
  shows "(\<lambda> x. (sbDom\<cdot>x = cs) \<leadsto> (f x)) \<sqsubseteq> (\<lambda> x. (sbDom\<cdot>x = cs) \<leadsto> (g x))"
  by (simp add: assms below_option_def fun_belowI)
  

lemma spfapplyout_mono [simp]:  assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows " monofun (\<lambda>g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x)))"
  apply (rule monofunI)
    apply (rule spfbelowI2)
    apply (simp_all add: assms)
    apply (simp add: spfdom_eq)
    by (metis (full_types) below_SPF_def below_option_def below_refl monofun_cfun_arg 
                                monofun_cfun_fun)

(* this is just a proxy definition used to make the simplifier less agressive ;) *)
definition "applyab k \<equiv> (\<lambda>g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x)))"

lemma applyab_mono [simp]: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows " monofun (applyab k)"
  apply (subst applyab_def)
  by (rule spfapplyout_mono, simp add: assms)

lemma applyab_rev: "(\<lambda>g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x))) = applyab k"
  by (simp add: applyab_def)

lemma applyab_rev2: "Abs_CSPF (\<lambda>xa::'a SB. (sbDom\<cdot>xa = spfDom\<cdot>x)\<leadsto>k\<cdot>(x \<rightleftharpoons> xa)) = applyab k x"
  by (simp add: applyab_def)

lemma spfapplyout_chain: assumes "chain Y" and "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "chain (\<lambda> i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
proof  (rule chainI)
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chainE by auto

  have f2: "\<And> i. spfDom\<cdot>(Y (Suc i)) = spfDom\<cdot>(Y i)"
    using f1 spfdom_eq by blast

  have f3: "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> Abs_CSPF (\<lambda>xa. (sbDom\<cdot>xa = spfDom\<cdot>(x))\<leadsto>k\<cdot>(x \<rightleftharpoons> xa)) 
                           \<sqsubseteq> Abs_CSPF (\<lambda>xa. (sbDom\<cdot>xa = spfDom\<cdot>(y))\<leadsto>k\<cdot>(y \<rightleftharpoons> xa))"
    apply (subst (1 2) applyab_rev2)
    using applyab_mono assms(2) monofun_def by blast

  show "\<And>i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
            \<sqsubseteq> Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y (Suc i)))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
    apply (rule f3)
    by (simp add: f1)
qed

lemma spf_well_lub : assumes "chain Y" and "\<And> i. spf_well (Y i)"
  shows "spf_well (\<Squnion> i. Y i)"
  by (simp add: admD assms(1) assms(2))

lemma test3: assumes "Rep_SPF f1 = Rep_SPF f2"
  shows "f1 = f2"
  using Rep_SPF_inject assms by blast

(* definition spfApplyOut :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<rightarrow> 'a SPF" where
"spfApplyOut k \<equiv> (\<Lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))" *)

definition my_test :: "(nat \<Rightarrow> 'a SB \<rightarrow> 'a SB option) \<Rightarrow> 'a SPF" where
"my_test Y \<equiv> \<Squnion> i. (Abs_SPF (Y i))"

lemma my_test_resub: "(\<Squnion> i. (Abs_SPF (Y i))) = my_test Y"
  by (simp add: my_test_def)


lemma abs_spf_lub_chain : assumes "chain Y" and "\<And> i. spf_well (Y i)"
  shows "(\<Squnion> i. Abs_SPF (Y i)) = Abs_SPF (\<Squnion> i. Y i)"
proof -
  have f1: "spf_well (Lub Y)"
    by (simp add: admD assms(1) assms(2))
  have f2: "Rep_SPF (\<Squnion>i::nat. Abs_SPF (Y i)) =  (\<Squnion>i::nat. Rep_SPF (Abs_SPF (Y i)))"
  proof -
    have "\<forall>c. c \<notin> Collect spf_well \<or> Rep_SPF (Abs_SPF c::'a SPF) = c"
      by (metis Abs_SPF_inverse)
    then have "chain (\<lambda>n. Abs_SPF (Y n))"
      by (metis (no_types) assms(1) assms(2) below_SPF_def mem_Collect_eq po_class.chain_def)
    then show ?thesis
      by (simp add: assms(2) f1 lub_SPF)
  qed
  have f3: "\<And> i. Rep_SPF (Abs_SPF (Y i)) = (Y i)"
    using assms(2) by auto
  show ?thesis
    apply (subst my_test_resub)
    apply (rule test3)
    apply (simp add: my_test_def f1 f2)
    by (simp add: f3)
qed

lemma spf_chain_dom: assumes "chain (Y :: nat \<Rightarrow> 'a SPF)" and "spfDom\<cdot>(Y 0) = cs"
  shows "\<And> i. spfDom\<cdot>(Y i) = cs"
  using assms(1) assms(2) spfdom_eq_lub by blast

lemma spf_chain_ran: assumes "chain (Y :: nat \<Rightarrow> 'a SPF)" and "spfRan\<cdot>(Y 0) = cs"
  shows "\<And> i. spfRan\<cdot>(Y i) = cs"
  using assms(1) assms(2) spfran_eq_lub by blast
  
lemma my_func_eq: assumes "\<And> x. (f x) = (g x)"
  shows "f = g"
  by (simp add: assms ext)
  

lemma cfun_below: assumes "x \<sqsubseteq> y" and "cont x" and "cont y"
  shows "Abs_cfun x \<sqsubseteq> Abs_cfun y"
  by (simp add: assms(1) assms(2) assms(3) below_cfun_def)
  

lemma spfapplyout_chain_lub [simp]: assumes "chain Y" and "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(\<Squnion>i. Y i))\<leadsto>k\<cdot>((\<Squnion>i. Y i) \<rightleftharpoons> x)) 
          \<sqsubseteq> (\<Squnion>i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
proof -
  have f1: "\<And> i. spfDom\<cdot>(Y i) = spfDom\<cdot>(\<Squnion>i. Y i)"
    using assms(1) spfdom_eq_lub by blast
  have f11: "\<And> i. spfDom\<cdot>(\<Squnion>i. Y i) = spfDom\<cdot>(Y i)"
    using assms(1) spfdom_eq_lub by blast
  
  have f10: "\<And> i. cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    apply (subst f11, subst spfapplyout_spf_cont)
    by simp

  (* show some chain properties *)
  have f12: "(\<lambda>i::nat. \<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
              = (\<lambda>i::nat. \<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    using f1 by auto

  have f30: "\<And> i .(\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                    =  (\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    by (simp add: f1)
  have f30_rev: "\<And> i .  (\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                       = (\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    by (simp add: f30)

  have f14: "chain (\<lambda>i::nat. \<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    (* see general process above *)
  proof (rule chainI)
    have f141: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)
     
    have "\<And> i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) \<sqsubseteq>
                (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
      apply (rule cfun_below)
        apply (simp_all add: f10)
        apply (rule spfbelowI3)
      by (metis below_SPF_def below_option_def below_refl cfun_below_iff 
                f141 monofun_cfun_arg)
      
    thus  "\<And>i::nat.
       (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) \<sqsubseteq>
       (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y (Suc i)))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
      by (simp add: f1)
  qed
      
       

(*  chain (\<lambda>i::nat. \<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) *)

  have f20: "(\<Squnion>i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) 
                  = (Abs_CSPF (\<Squnion>i.  (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))))"
    apply (subst abs_spf_lub_chain)
    apply (simp_all add: f12)
      apply (simp add: f14)
      apply (subst f30)
        apply (rule spfapplyout_spf_wellI)
        apply (simp add: assms)
        apply (subst f30_rev)
        by (metis (no_types, lifting) Abs_cfun_inverse2 cfun.lub_cfun f10 f12 f14 lub_eq)

  have f40: "\<And> f1 f2. Rep_CSPF f1 \<sqsubseteq> Rep_CSPF f2 \<Longrightarrow> f1 \<sqsubseteq> f2"
     by (meson below_SPF_def below_cfun_def)

  have f52: "\<And> x. (\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x)) = k\<cdot>(Lub Y \<rightleftharpoons> x)"
    proof -
      fix x :: "'a SB"
      have f1: "chain (\<lambda>n. Rep_SPF (Y n))"
        using assms(1) rep_spf_chain by blast
      then have f2: "chain (the_abbrv (\<lambda>n. Rep_CSPF (Y n) x))"
        using ch2ch_Rep_cfunL op_the_chain by blast
      have f3: "Lub Y = Abs_SPF (\<Squnion>n. Rep_SPF (Y n))"
        using assms(1) lub_SPF by blast
    have "spf_well (\<Squnion>n. Rep_SPF (Y n))"
      using f1 rep_spf_well spf_well_lub by blast
      then have "Rep_CSPF (Lub Y) = Rep_cfun (\<Squnion>n. Rep_SPF (Y n))"
        using f3 by simp
      then have "Rep_CSPF (Lub Y) x = (\<Squnion>n. Rep_CSPF (Y n) x)"
        using f1 by (simp add: contlub_cfun_fun)
    then have "Lub Y \<rightleftharpoons> x = (\<Squnion>n. \<lambda>n. Rep_CSPF (Y n) x\<rightharpoonup>n)"
      using f1 ch2ch_Rep_cfunL op_the_lub by auto
    then have "(\<Squnion>n. k\<cdot>\<lambda>n. Rep_CSPF (Y n) x\<rightharpoonup>n) = k\<cdot>(Lub Y \<rightleftharpoons> x)"
      using f2 by (simp add: cont2contlubE)
      then show "(\<Squnion>n. k\<cdot>(Y n \<rightleftharpoons> x)) = k\<cdot>(Lub Y \<rightleftharpoons> x)"
        by blast
    qed
    have f60: "chain (\<lambda>i. (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
      proof (rule chainI)
        have f161: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
          by (simp add: assms(1) po_class.chainE)

        show "\<And>i::nat. (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                       \<sqsubseteq> (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
          apply (rule spfbelowI3)
          by (metis below_SPF_def below_option_def below_refl cfun_below_iff 
                f161 monofun_cfun_arg)
      qed
      have f100: "\<And> x. (\<Squnion>i::nat. (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) x 
                          = (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x))) x"
      apply (simp)
      apply rule
         apply (smt ch2ch_fun f60 image_cong lub_fun option.collapse option.discI option.inject 
                          option_chain_cases part_the_lub some_lub_chain_eq)
        by (smt Abs_cfun_inverse2 below_option_def cfun_below_iff f10 f12 f14 image_cong 
                    is_ub_thelub rep_cfun_cont)
      
    have f51: "(\<Squnion>i::nat. (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) 
                      = (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x)))"
    using f100 by auto 
  show ?thesis
    apply (subst f30_rev)
    apply (subst f20)
    apply (subst f51)
    apply (subst f52)
    by simp
qed

lemma spfapplyout_cont [simp]:  assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "cont (\<lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"
  apply (rule contI2)
  using assms apply auto[1]
  by (simp add: assms)

(* further properties *)

lemma spfapplyout_insert: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "spfApplyOut k\<cdot>f =  Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))"
  by (simp add: spfApplyOut_def assms)

lemma spfapplyout_dom: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "spfDom\<cdot>(spfApplyOut k\<cdot>f) = spfDom\<cdot>f"
  by (simp add: spfapplyout_insert assms)


lemma spfapplyout_ran: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "spfRan\<cdot>(spfApplyOut k\<cdot>f) = spfRan\<cdot>f"
  by (simp add: spfapplyout_insert assms)

lemma spfapplyout_apply:  assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
                              and "sbDom\<cdot>sb = spfDom\<cdot>f"
  shows "(spfApplyOut k\<cdot>f) \<rightleftharpoons> sb = k\<cdot>(f \<rightleftharpoons>sb)"
  by (simp add: spfapplyout_insert assms)

section \<open>spfApplyIn2\<close>
(* note that these proofs only really work if k does not change the domain *)

lemma spfapplyin_spf_cont [simp]: "cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))"
proof (rule spf_contI)
  show "\<And>(x::'a SB) y::'a SB. sbDom\<cdot>x = spfDom\<cdot>g \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> g \<rightleftharpoons> k\<cdot>x \<sqsubseteq> g \<rightleftharpoons> k\<cdot>y"
    by (simp add: monofun_cfun_arg spf_pref_eq)
  show "\<And>Y::nat \<Rightarrow> 'a SB. chain Y \<Longrightarrow> sbDom\<cdot>(\<Squnion>i::nat. Y i) = spfDom\<cdot>g 
                \<Longrightarrow> g \<rightleftharpoons> k\<cdot>(\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. g \<rightleftharpoons> k\<cdot>(Y i))"
    by (simp add: contlub_cfun_arg op_the_lub)
qed

lemma spfapplyin_ran: assumes "\<And> x. sbDom\<cdot>(k\<cdot>x) = sbDom\<cdot>x" and "sbDom\<cdot>b = spfDom\<cdot>g"
  shows "sbDom\<cdot>(g \<rightleftharpoons> k\<cdot>b) = spfRan\<cdot>g"
  by (simp add: assms(1) assms(2))

lemma spfapplyin_spf_wellI [simp]: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))"
  apply (rule spf_wellI)
    apply (simp_all add: domIff2)
    by (simp add: assms(1))



lemma spfapplyin_spf_dom [simp]:  assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "spfDom\<cdot>(Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) = spfDom\<cdot>g"
  by (simp add: assms spfDomAbs)

lemma spfapplyin_spf_ran [simp]: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "spfRan\<cdot>(Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) =  spfRan\<cdot>g"
  apply (subst spfran_least)
  by (simp add: spfapplyin_spf_dom assms)

lemma spfapplyin_spf_apply:  assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
                             and "sbDom\<cdot>sb = spfDom\<cdot>g"
  shows "(Abs_SPF (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) \<rightleftharpoons> sb = g \<rightleftharpoons> (k\<cdot>sb)"
  by (simp add: assms)

lemma spfapplyin_mono [simp]: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "monofun (\<lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"
apply (rule monofunI)
    apply (rule spfbelowI2)
    apply (simp_all add: assms)
    apply (simp add: spfdom_eq)
    by (metis (full_types) below_SPF_def below_option_def below_refl monofun_cfun_arg 
                                monofun_cfun_fun)

(* this is just a proxy definition used to make the simplifier less agressive ;) *)
definition "applycd k = (\<lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"


lemma applycd_mono [simp]: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "monofun (applycd k)"
  apply (subst applycd_def)
  by (rule spfapplyin_mono, simp add: assms)

(* applycd substitution and reverse substitution lemmata *)

lemma applycd_rev: "(\<lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) = applycd k"
  by (simp add: applycd_def)

lemma applycd_rev2: "Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))) = applycd k g"
  by (simp add: applycd_def)

lemma spfapplyin_chain [simp]: assumes "chain Y" and "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "chain (\<lambda> i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i)) \<leadsto> ((Y i) \<rightleftharpoons>(k\<cdot>x))))"
proof (rule chainI)
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chainE by auto

  have f2: "\<And> i. spfDom\<cdot>(Y (Suc i)) = spfDom\<cdot>(Y i)"
    using f1 spfdom_eq by blast

  have f3: "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> Abs_CSPF (\<lambda>xa. (sbDom\<cdot>xa = spfDom\<cdot>x) \<leadsto> (x \<rightleftharpoons>(k\<cdot>xa)))
                             \<sqsubseteq> Abs_CSPF (\<lambda>xa. (sbDom\<cdot>xa = spfDom\<cdot>y) \<leadsto> (y \<rightleftharpoons>(k\<cdot>xa)))"
    apply (subst (1 2) applycd_rev2)
    using applycd_mono assms(2) monofun_def by blast

  show "\<And>i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x) 
            \<sqsubseteq> Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y (Suc i)))\<leadsto>Y (Suc i) \<rightleftharpoons> k\<cdot>x)"
    apply (rule f3)
    by (simp add: f1)
qed

lemma spfapplyin_chain_lub [simp]: assumes "chain Y" and "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows " Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(\<Squnion>i::nat. Y i))\<leadsto>(\<Squnion>i. Y i) \<rightleftharpoons> k\<cdot>x) \<sqsubseteq>
       (\<Squnion>i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x))"
proof -
  have f1: "\<And> i. spfDom\<cdot>(Y i) = spfDom\<cdot>(\<Squnion>i. Y i)"
    using assms(1) spfdom_eq_lub by blast
  have f11: "\<And> i. spfDom\<cdot>(\<Squnion>i. Y i) = spfDom\<cdot>(Y i)"
    using assms(1) spfdom_eq_lub by blast

  have f10: "\<And> i. cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y)) \<leadsto> ((Y i) \<rightleftharpoons>(k\<cdot>x)))"
    apply (subst f11, subst spfapplyin_spf_cont)
    by simp

  (* handy substitution facts *)

  have f12: "(\<lambda> i::nat. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))) 
              = (\<lambda> i::nat. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
    using f1 by auto

  (* like f12 but without the outer lambda function *)
  have f30: "\<And> i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)) 
                  = (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))"
    by (simp add: f1)
  have f30_rev: "\<And> i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)) 
                      = (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))"
    by (simp add: f30)

  have f14: "chain (\<lambda> i::nat. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
  proof (rule chainI)
    have f141: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)

    have "\<And> i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)) 
                \<sqsubseteq> (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y (Suc i)) \<rightleftharpoons> (k\<cdot>x))"
      apply (rule cfun_below)
        apply (simp_all add: f10)
        apply (rule spfbelowI3)
        by (metis (no_types) below_SPF_def below_option_def below_refl cfun_below_iff f141)


      thus "\<And> i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x) 
               \<sqsubseteq> (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Y (Suc i)))\<leadsto>Y (Suc i) \<rightleftharpoons> k\<cdot>x)"
     by (simp add: f1)
  qed

  have f20: "(\<Squnion>i. Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))
            = Abs_CSPF (\<Squnion>i.(\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
    apply (subst abs_spf_lub_chain)
    apply (simp_all add: f12)
      apply (simp add: f14)
     apply (subst f30)
     apply (rule spfapplyin_spf_wellI, simp add: assms)
    apply (subst f30_rev)
    apply (subst cfun.lub_cfun)
    apply (subst f30, simp add: f14)
    using f10 by auto[1]
    
  have f40: "\<And> f1 f2. Rep_CSPF f1 \<sqsubseteq> Rep_CSPF f2 \<Longrightarrow> f1 \<sqsubseteq> f2"
    by (meson below_SPF_def below_cfun_def)

  have f52: "\<And> x. (\<Squnion>i. (Y i) \<rightleftharpoons> (k\<cdot>x)) = ((\<Squnion>i. Y i) \<rightleftharpoons> k\<cdot>x)"
  proof -
    fix x :: "'a SB"
    have "chain (\<lambda>n. Rep_SPF (Y n))"
      by (metis assms(1) rep_spf_chain)
    then have f1: "spf_well (\<Squnion>n. Rep_SPF (Y n))"
      using rep_spf_well spf_well_lub by blast
    have "\<forall>f s. \<not> chain f \<or> (Lub f\<cdot>(s::'a SB)::'a SB option) = (\<Squnion>n. f n\<cdot>s)"
      using contlub_cfun_fun by blast
    then have "(\<Squnion>n. \<lambda>n. Rep_CSPF (Y n) (k\<cdot>x)\<rightharpoonup>n) = Lub Y \<rightleftharpoons> k\<cdot>x"
      using f1 by (simp add: assms(1) lub_SPF op_the_lub)
    then show "(\<Squnion>n. Y n \<rightleftharpoons> k\<cdot>x) = (\<Squnion>n. Y n) \<rightleftharpoons> k\<cdot>x"
      by meson
  qed
  have f60: "chain (\<lambda> i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
  proof (rule chainI)
    have f601: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)
    show "\<And>i. (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x) 
               \<sqsubseteq> (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>Y (Suc i) \<rightleftharpoons> k\<cdot>x)"
      apply (rule cfun_below)
        apply (simp_all add: f10)
        apply (rule spfbelowI3)
      by (metis (no_types) below_SPF_def below_option_def below_refl cfun_below_iff f601)
  qed
          
  have f100: "\<And> x. (\<Squnion>i::nat. (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))) x 
                          = (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i. (Y i) \<rightleftharpoons> (k\<cdot>x))) x"
    apply simp
    apply rule
     apply (smt Abs_cfun_inverse2 assms(2) ch2ch_Rep_cfunL contlub_cfun_fun f10 f11 f60 
                image_cong op_the_lub option.collapse option.discI option_chain_cases 
                rep_cfun_cont some_lub_chain_eq spfapplyin_eq_pre)
     by (smt Abs_cfun_inverse2 below_option_def cfun_below_iff f10 f12 f14 image_cong 
                    is_ub_thelub rep_cfun_cont)
   
   have f101: "(\<Squnion>i::nat. (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))) 
                = (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i. (Y i) \<rightleftharpoons> (k\<cdot>x)))" 
     using f100 by auto
  show ?thesis
    apply (subst f30_rev)
     apply (subst f20)
     apply (subst f101)
     apply (subst f52)
     by simp
qed


lemma spfapplyin_cont [simp]: assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b"
  shows "cont (\<lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"
  apply (rule contI2)
  using assms apply auto[1]
  by (simp add: assms)

section \<open>spfApplyInOld\<close>

  (* these lemmas concern the original spfApplyIn definition by Sebastian *)
    (* since both versions are equivalent under the assumption "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b", 
        eventually it does not matter which definition we use.
        HOWEVER: a \<leadsto> based lemma *)
        
lemma spfapplyin_well [simp]: 
  assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) = sbDom\<cdot>sb"
  shows "spf_well (\<Lambda> sb.(Rep_CSPF spf)(f\<cdot>sb))" (is "spf_well ?g")
proof(rule spf_wellI)
  fix sb
  assume as1: "sb\<in>dom (Rep_cfun ?g)"
  obtain y where "?g\<cdot>sb = Some y"
    using as1 by blast
  hence "sbDom\<cdot>(f\<cdot>sb) = spfDom\<cdot>spf" by simp
  show "sbDom\<cdot>sb = spfDom\<cdot>spf"
    using as1 assms by auto
next
  fix sb
  assume as1: "sb\<in>dom (Rep_cfun ?g)"
  hence "f\<cdot>sb\<in>dom (Rep_CSPF spf)"
    by (simp add: domIff)
  hence "sbDom\<cdot>(f\<cdot>sb) = spfDom\<cdot>spf"
    by auto
  thus "sbDom\<cdot>((Rep_cfun ?g)\<rightharpoonup>sb) = spfRan\<cdot>spf" by (simp)
next
  fix sb :: "'a SB"
  assume "sbDom\<cdot>sb = spfDom\<cdot>spf"  
  hence "sbDom\<cdot>(f\<cdot>sb) = spfDom\<cdot>spf" using assms by auto
  hence "f\<cdot>sb \<in> dom (Rep_CSPF spf)"
    by (metis sbleast_sbdom spfLeastIDom spf_sbdom2dom)
  obtain y where "?g\<cdot>sb = Some y"
    using \<open>f\<cdot>sb \<in> dom (Rep_CSPF spf)\<close> \<open>sbDom\<cdot>sb = spfDom\<cdot>spf\<close> by auto
  thus "sb\<in>dom (Rep_cfun ?g)"
    by blast
qed

lemma spfapplyin_dom1 [simp]: 
  assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) = sbDom\<cdot>sb"
  shows "spfDom\<cdot>(Abs_SPF (\<Lambda> sb.(Rep_CSPF spf)(f\<cdot>sb))) = spfDom\<cdot>spf" 
  apply(subst spfDom_def, simp add: assms)
  by (metis (mono_tags, lifting) assms domIff rep_spf_well sbleast_sbdom spfLeastIDom spf_well_def2 tfl_some)

lemma spfapplyin_ran1 [simp]: 
  assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) = sbDom\<cdot>sb"
  shows "spfRan\<cdot>(Abs_SPF (\<Lambda> sb.(Rep_CSPF spf)(f\<cdot>sb))) = spfRan\<cdot>spf" 
  apply(rule ccontr)
  apply(simp add: spfran_insert assms)
  proof -
    assume as1: "sbDom\<cdot>(SOME b. b \<in> ran (\<lambda>sb. Rep_CSPF spf (f\<cdot>sb))) \<noteq> sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF spf))"
    have h1: "ran (Rep_CSPF spf) \<noteq> {}"
      using spf_ran_not_empty by blast
    have h2:"ran  (\<lambda> sb. (Rep_CSPF spf)(f\<cdot>sb)) \<noteq> {}"
    proof -
      have "\<forall>s. spf_well (\<Lambda> sa. Rep_CSPF s (f\<cdot>sa))"
        using assms spfapplyin_well by blast
      then show ?thesis
        by (metis (no_types) Abs_SPF_inverse Abs_cfun_inverse2 cont_Rep_cfun2 cont_compose empty_iff mem_Collect_eq spf_ran_not_empty)
    qed
      
  obtain sb1 sb2 where "sb1\<in>ran (\<lambda> sb. (Rep_CSPF spf)(f\<cdot>sb))" and "sb2\<in>ran (Rep_CSPF spf)"
    and "sbDom\<cdot>sb1 \<noteq> sbDom\<cdot>sb2"
    by (metis as1 h1 h2 some_in_eq)
    thus False
      by (metis (no_types, lifting) ran2exists spfran2sbdom)
  qed
 


lemma spfapplyin_monofun: assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) =  sbDom\<cdot>sb"
  shows "monofun (\<lambda>spf. Abs_CSPF (\<lambda>sb. (Rep_CSPF spf)(f\<cdot>sb)))" (is "monofun ?g")
  apply(rule monofunI, rule spf_belowI)
  apply(auto simp add: assms spfdom_eq)
  by (metis (no_types, hide_lams) below_SPF_def below_option_def cfun_below_iff po_eq_conv)

lemma spf_lub_eq: assumes "chain Y" and "(\<And> i. spf_well (Y i))"
  shows "(\<Squnion>i. Abs_SPF (Y i)) = Abs_SPF (\<Squnion>i. Y i)"
proof -
  have "spf_well (\<Squnion>i. Y i)"
    by (simp add: admD assms(1) assms(2))
  have "chain (\<lambda>i. Abs_SPF (Y i))"
    by (metis (no_types, lifting) Abs_SPF_inverse assms(1) assms(2) below_SPF_def mem_Collect_eq po_class.chain_def)
  thus ?thesis
    by (metis (mono_tags, lifting) Abs_SPF_inverse assms(2) lub_SPF lub_eq mem_Collect_eq)
qed

lemma "adm (\<lambda>x. x\<sqsubseteq>h)"
  by (metis admI lub_below_iff)


 (* inject cont proof of alternative definition in the definition by sebastian *)
lemma spfapplyinOld_cont [simp]: assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) =  sbDom\<cdot>sb"
  shows "cont (\<lambda>spf. Abs_CSPF (\<lambda>sb. (Rep_CSPF spf)(f\<cdot>sb)))"
  apply (subst spfapplyin_eq_pre)
  apply (subst assms(1))
  apply (rule spfapplyin_cont)
  by (simp add: assms(1))

lemma spfapplyinOld_insert: 
  assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) =  sbDom\<cdot>sb"
  shows "spfApplyIn f\<cdot>spf = Abs_CSPF (\<lambda>sb. (Rep_CSPF spf)(f\<cdot>sb))"
  apply(simp add: spfApplyIn_def)
  using assms beta_cfun spfapplyinOld_cont by blast


lemma spfapplyinOld_dom [simp]: assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) =  sbDom\<cdot>sb"
  shows "spfDom\<cdot>(spfApplyIn f\<cdot>spf) = spfDom\<cdot>spf"
  using assms spfapplyinOld_insert by fastforce

lemma spfapplyinOld_ran [simp]: assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) =  sbDom\<cdot>sb"
  shows "spfRan\<cdot>(spfApplyIn f\<cdot>spf) = spfRan\<cdot>spf"
  using assms spfapplyinOld_insert by fastforce

lemma spfapplyinOld_step [simp]: assumes "\<And>sb. sbDom\<cdot>(f\<cdot>sb) =  sbDom\<cdot>sb"
  shows "(spfApplyIn f\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>f\<cdot>sb"
  by(simp add: spfapplyinOld_insert assms)




section \<open>Definitions with spfApplyIn\<close>

definition spfRt :: "'m SPF \<rightarrow> 'm SPF" where
"spfRt \<equiv> spfApplyIn sbRt"

section \<open>Definitions with spfApplyOut\<close>

definition spfConc :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfConc sb = spfApplyOut (sbConc sb)"


subsection \<open>more general lemma\<close>

lemma spfapply_in_out: "spfApplyIn f\<cdot>(spfApplyOut g\<cdot>spf) = spfApplyOut g\<cdot>(spfApplyIn f\<cdot>spf)"
  sorry

subsection \<open>spfRt lemma\<close>
lemma spfrt_step: "(spfRt\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>(sbRt\<cdot>sb)"
  by(simp add: spfRt_def)

subsection \<open>spfConc lemma\<close>
lemma spconc_step: 
  shows "(spfConc sb1\<cdot>spf)\<rightleftharpoons>sb2 = sbConc sb1\<cdot>(spf\<rightleftharpoons>sb)"
  apply(simp add: spfConc_def)
  oops

end