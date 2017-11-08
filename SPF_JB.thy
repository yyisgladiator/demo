(*  Title:        SPF
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Extends "Stream Processing Functions"
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

lemma spfapplyout_mono [simp]:  assumes "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows " monofun (\<lambda>g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x)))"
  apply (rule monofunI)
    apply (rule spfbelowI2)
    apply (simp_all add: assms)
    apply (simp add: spfdom_eq)
    by (metis (full_types) below_SPF_def below_option_def below_refl monofun_cfun_arg 
                                monofun_cfun_fun)

lemma spfapplyout_chain: assumes "chain Y" and "\<And>b. sbDom\<cdot>(k\<cdot>b) = sbDom\<cdot>b" 
  shows "chain (\<lambda> i. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
proof  (rule chainI)
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chainE by auto

  have f2: "\<And> i. spfDom\<cdot>(Y (Suc i)) = spfDom\<cdot>(Y i)"
    using f1 spfdom_eq by blast
 
  have f3: "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> Abs_CSPF (\<lambda>xa. (sbDom\<cdot>xa = spfDom\<cdot>(x))\<leadsto>k\<cdot>(x \<rightleftharpoons> xa)) 
                           \<sqsubseteq> Abs_CSPF (\<lambda>xa. (sbDom\<cdot>xa = spfDom\<cdot>(y))\<leadsto>k\<cdot>(y \<rightleftharpoons> xa))"
    (* this should be a direct result of the monofun property *)
      (* the workaround for this is to definie a function and use it as a proxy, see ABP_TSPS *)
    sorry
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
  have f14: "chain (\<lambda>i::nat. \<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    (* see general process above *)
    sorry

  have f30: "\<And> i .(\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                    =  (\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    by (simp add: f1)
  have f30_rev: "\<And> i .  (\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                       = (\<Lambda> (x::'a SB). (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    by (simp add: f30)

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

   have f50: "Rep_CSPF (Abs_CSPF (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Lub Y \<rightleftharpoons> x))) 
                                  = (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Lub Y \<rightleftharpoons> x))"
     (* alternative approach *)
     sorry

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
      sorry
  have f51: "(\<Squnion>i::nat. (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) = (\<lambda>x::'a SB. (sbDom\<cdot>x = spfDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x)))"
    sorry
  show ?thesis
    apply (subst f30_rev)
    apply (subst f20)
    apply (rule f40, subst f50)
    sorry
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


end