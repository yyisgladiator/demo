(*  Title:        UFun_applyIn

    Description:  Extends "Universal Functions" by ApplyIn/Out etc ...
*)


theory UFun_applyIn
  imports UFun
begin


default_sort ubcl  

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)

  
definition ufApplyOut :: "('m \<rightarrow> 'm ) \<Rightarrow> ('m ufun) \<rightarrow> ('m ufun)" where
"ufApplyOut k \<equiv> (\<Lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"

definition ufApplyIn :: "('m \<rightarrow> 'm ) \<Rightarrow> ('m ufun) \<rightarrow> ('m ufun)" where 
"ufApplyIn k \<equiv> \<Lambda> g. Abs_cufun (\<lambda>x. (Rep_cufun g)(k\<cdot>x))" 

definition ufApplyIn2 :: "('m \<rightarrow> 'm ) \<Rightarrow> ('m ufun) \<rightarrow> ('m ufun)" where
"ufApplyIn2 k \<equiv> (\<Lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>(k\<cdot>x) = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"


subsection \<open>some rules\<close>
  
  
(* unfolding rule  *)
lemma ufapplyin_eq_pre: "(Rep_cufun uf)(f\<cdot>x) = (ubclDom\<cdot>(f\<cdot>x) = ufDom\<cdot>uf) \<leadsto> (uf \<rightleftharpoons>(f\<cdot>x))"
  by (metis domIff option.collapse rep_ufun_well ufWell_def ufdom_2ufundom ufdom_not_empty)

 (* convert between original and proof oriented definition *)
lemma ufapplyin_eq: "ufApplyIn k = ufApplyIn2 k"
  apply (subst ufApplyIn_def, subst ufApplyIn2_def)
  apply (subst ufapplyin_eq_pre)
  by simp


section \<open>ufApplyOut\<close>

subsection \<open>resulting uf\<close>
  

(* function ufapplyout is cont *)
lemma ufapplyout_uf_cont [simp]: "cont (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))"
proof (rule ufun_contI)
  show "\<And>(x::'a) y::'a. ubclDom\<cdot>x = ufDom\<cdot>g \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> k\<cdot>(g \<rightleftharpoons> x) \<sqsubseteq> k\<cdot>(g \<rightleftharpoons> y)"
    by (metis below_option_def below_refl monofun_cfun_arg)
next 
  show "\<And>Y::nat \<Rightarrow> 'a. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i::nat. Y i) = ufDom\<cdot>g 
              \<Longrightarrow> k\<cdot>(g \<rightleftharpoons> (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. k\<cdot>(g \<rightleftharpoons> Y i))"
    by (simp add: contlub_cfun_arg op_the_chain op_the_lub)
qed

 (* intro lemma for uf_well proofs with uf_applyout *)
lemma ufapplyout_uf_wellI [simp]: assumes "\<And>b. ubclDom\<cdot>b = ufDom\<cdot>g \<Longrightarrow> ubclDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))"
  apply (rule ufun_wellI)
    apply (simp_all add: domIff2)
  by (simp add: assms)

(* dom of ufapplyout is the same as dom of function g  *)
lemma ufapplyout_uf_dom [simp]: assumes "\<And>b. ubclDom\<cdot>b = ufDom\<cdot>g \<Longrightarrow> ubclDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "ufDom\<cdot>(Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) = ufDom\<cdot>g"
  by (simp add: assms ufun_ufdom_abs)

(* ran of ufapplyout is the same as the ubclDom of the result after applying k and g on input b *)
lemma ufapplyout_uf_ran [simp]: assumes "\<And>b. ubclDom\<cdot>b = ufDom\<cdot>(g::'m ufun) \<Longrightarrow> ubclDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "ufRan\<cdot>(Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) = cs" (is "ufRan\<cdot>?F = ?cs")
proof -
  obtain x::'m  where x_def: "ubclDom\<cdot>x = ufDom\<cdot>g" 
    using ubcldom_ex by blast
  have f1: "ufDom\<cdot>(Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) = ufDom\<cdot>g"
    using assms ufapplyout_uf_dom by blast
  have f2: "(Abs_cufun ((\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))))\<rightleftharpoons>x = k\<cdot>(g \<rightleftharpoons>x)"
    by (simp add: assms x_def)
  then show ?thesis
    by (metis (no_types, lifting) assms f1 ufran_2_ubcldom2 x_def)
qed


(* unfolding rule when the input has the right domain  *)
lemma ufapplyout_uf_apply: assumes "\<And>b. ubclDom\<cdot>b = ufDom\<cdot>g \<Longrightarrow> ubclDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
                             and "ubclDom\<cdot>ub = ufDom\<cdot>g"
  shows "(Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))) \<rightleftharpoons> ub = k\<cdot>(g \<rightleftharpoons>ub)"
  by (simp add: assms)

 (* show that ufApplyOut is continuous in its second argument *)

  (* put this into Ufun.thy *)
(* below rule with additional assums  *)
lemma ufbelowI: assumes "\<And> x. P x \<Longrightarrow> (f x) \<sqsubseteq> (g x)"
                 and "cont (\<lambda> x. (P x) \<leadsto> (f x))" and "cont (\<lambda> x. (P x) \<leadsto> g x)" 
                 and "ufWell (\<Lambda> x. (P x) \<leadsto> (f x))" and "ufWell (\<Lambda> x. (P x) \<leadsto> g x)"
               shows "Abs_cufun (\<lambda> x. (P x) \<leadsto> (f x)) \<sqsubseteq> Abs_cufun (\<lambda> x. (P x) \<leadsto> (g x))"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) below_option_def below_ufun_def monofun_LAM)

  (* put this into Ufun.thy *)
(* below rule with additional assums  *)
lemma ufbelowI2: assumes "cs1 = cs2"  
                 and "\<And> x. (ubclDom\<cdot>x = cs2) \<Longrightarrow> (f x) \<sqsubseteq> (g x)" 
                 and "cont (\<lambda> x. (ubclDom\<cdot>x = cs1) \<leadsto> (f x))" 
                 and "cont (\<lambda> x. (ubclDom\<cdot>x = cs2) \<leadsto> g x)" 
                 and "ufWell (\<Lambda> x. (ubclDom\<cdot>x = cs1) \<leadsto> (f x))" 
                 and "ufWell (\<Lambda> x. (ubclDom\<cdot>x = cs2) \<leadsto> g x)"
  shows "Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = cs1) \<leadsto> (f x)) \<sqsubseteq> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = cs2) \<leadsto> (g x))"
  proof -
  have f1:  "\<And> f g. (ufWell f) \<and> (ufWell g) \<Longrightarrow> (f \<sqsubseteq> g) \<Longrightarrow> (Abs_ufun f \<sqsubseteq> Abs_ufun g)"
    by (simp add: below_ufun_def)
  have f2: "\<And> f g. (cont f) \<and> (cont g) \<Longrightarrow> (f \<sqsubseteq> g) \<Longrightarrow> (Abs_cfun f \<sqsubseteq> Abs_cfun g)"
    by (simp add: below_cfun_def)
  have f3: "(\<lambda>x. (ubclDom\<cdot>x = cs1)\<leadsto>f x) \<sqsubseteq> (\<lambda>x. (ubclDom\<cdot>x = cs2) \<leadsto>g x)"
    apply (subst assms(1))
    by (simp add: assms(2) below_option_def fun_belowI)
  show ?thesis
    apply (rule f1)
      apply (simp add: assms(5) assms(6))
      apply (rule f2)
        apply (simp add: assms(3) assms(4))
         by (simp add: f3)
     qed

(* rule to proof that function f is below funtion g  *)
lemma ufbelowI3: assumes "\<And> x. (ubclDom\<cdot>x = cs) \<Longrightarrow> (f x) \<sqsubseteq> (g x)"
  shows "(\<lambda> x. (ubclDom\<cdot>x = cs) \<leadsto> (f x)) \<sqsubseteq> (\<lambda> x. (ubclDom\<cdot>x = cs) \<leadsto> (g x))"
  by (simp add: assms below_option_def fun_belowI)

(* ufapplyout is monoton if k doesnt change the dom of the input  *)
lemma ufapplyout_mono [simp]:  assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows " monofun (\<lambda>g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x)))"
  apply (rule monofunI)
  apply (rule ufbelowI2)
       apply (simp_all add: assms)
     apply (simp add: ufdom_below_eq)
    apply (metis below_option_def below_ufun_def cfun_below_iff monofun_cfun_arg po_eq_conv)
  by (simp add: assms ufran_2_ubcldom2) +

(* dont know how it bahaves with ufun *)
(* this is just a proxy definition used to make the simplifier less agressive ;) *)
definition "applyab k \<equiv> (\<lambda>g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x)))"

(* applyab is a monoton function if k doesnt change the dom pf the input  *)
lemma applyab_mono [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows " monofun (applyab k)"
  apply (subst applyab_def)
  by (rule ufapplyout_mono, simp add: assms)

(* substitution rule of applyab with only one arg *)
lemma applyab_rev: "(\<lambda>g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g)\<leadsto>k\<cdot>(g \<rightleftharpoons> x))) = applyab k"
  by (simp add: applyab_def)

(* substitution rule of applyab with only two args *)
lemma applyab_rev2: "Abs_cufun (\<lambda>xa. (ubclDom\<cdot>xa = ufDom\<cdot>x)\<leadsto>k\<cdot>(x \<rightleftharpoons> xa)) = applyab k x"
  by (simp add: applyab_def)

(* ufapplyout builds a chain from a chain Y *)
lemma ufapplyout_chain: assumes "chain Y" and "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows "chain (\<lambda> i. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
proof (rule chainI)
  fix i::nat
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chain_def by auto
  have f2: "ufDom\<cdot>(Y i) = ufDom\<cdot>(Y (Suc i))"
    by (simp add: f1 ufdom_below_eq)
  have f4: "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> Abs_cufun (\<lambda>xa. (ubclDom\<cdot>xa = ufDom\<cdot>(x))\<leadsto>k\<cdot>(x \<rightleftharpoons> xa)) 
                           \<sqsubseteq> Abs_cufun (\<lambda>xa. (ubclDom\<cdot>xa = ufDom\<cdot>(y))\<leadsto>k\<cdot>(y \<rightleftharpoons> xa))"   
    apply (simp add: applyab_rev2)
    by (simp add: assms(2) monofunE)
  show "Abs_cufun (\<lambda>x::'a. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) \<sqsubseteq> Abs_cufun (\<lambda>x::'a. (ubclDom\<cdot>x = ufDom\<cdot>(Y (Suc i)))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
    by (simp add: f1 f4)
qed

(* put this in UFun.thy *)
(* the lub of a chain is also ufWell if all elements of the chain are  *)
lemma uf_well_lub : assumes "chain Y" and "\<And> i. ufWell (Y i)"
  shows "ufWell (\<Squnion> i. Y i)"
  by (simp add: admD assms(1) assms(2) ufWell_adm2)

(* Abs_ufun is cont if all element of the chain are ufWell  *)
lemma abs_uf_lub_chain : assumes "chain Y" and "\<And> i. ufWell (Y i)"
  shows "(\<Squnion> i. Abs_ufun (Y i)) = Abs_ufun (\<Squnion> i. Y i)"
proof -
  have f1: "ufWell (Lub Y)"
    by (simp add: admD assms(1) assms(2) ufWell_adm2)
  have f2: "Rep_ufun (\<Squnion>i::nat. Abs_ufun (Y i)) =  (\<Squnion>i::nat. Rep_ufun (Abs_ufun (Y i)))"
  proof -
    have "\<forall>c. c \<notin> Collect ufWell \<or> Rep_ufun (Abs_ufun c) = c"
      by simp
    then have "\<And> i. Abs_ufun (Y i) \<sqsubseteq> Abs_ufun (Y (Suc i))"
        apply (simp add: below_ufun_def)
        using assms(1) assms(2) po_class.chain_def by auto
    then have "chain (\<lambda>n. Abs_ufun (Y n))"
      by (simp add: po_class.chainI)
    then show ?thesis
      by (simp add: lub_ufun uf_well_lub)
  qed
  show ?thesis
    by (metis (mono_tags, lifting) Rep_ufun_inverse assms(2) f2 lub_eq rep_abs_cufun2)
qed

(*  do we really need this ?  *)
(* Abs_cfun is monoton if x and y are cont  *)
lemma cfun_below: assumes "x \<sqsubseteq> y" and "cont x" and "cont y"
  shows "Abs_cfun x \<sqsubseteq> Abs_cfun y"
  by (simp add: assms(1) assms(2) assms(3) below_cfun_def)

(* Rep_cfun is a cont function  *)
lemma rep_cfun_cont: assumes "chain Y"
  shows "Rep_cfun (\<Squnion>i. (Y i)) = (\<Squnion>i. (Rep_cfun ((Y i))))"
proof -
  have "\<And>f. chain (\<lambda>n. Rep_cfun (f n::'a \<rightarrow> 'b)) \<or> \<not> chain f"
    by (meson below_cfun_def po_class.chain_def)
  then have "\<And>f a. (\<Squnion>n. Rep_cfun (f n)) (a::'a) = (Lub f\<cdot>a::'b) \<or> \<not> chain f"
    by (metis contlub_cfun_fun lub_fun)
  then show ?thesis
    by (metis (no_types) assms fun_belowI po_eq_conv)
qed

(* Abs_cufun is a cont function if k doesnt change the dom of the arg b  *)
lemma ufapplyout_chain_lub [simp]: assumes "chain Y" and "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows "Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(\<Squnion>i. Y i))\<leadsto>k\<cdot>((\<Squnion>i. Y i) \<rightleftharpoons> x)) 
          \<sqsubseteq> (\<Squnion>i. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
proof -
  have f1: "\<And> i. ufDom\<cdot>(\<Squnion>i. Y i) = ufDom\<cdot>(Y i)"
    by (simp add: assms(1) ufdom_lub_eq)

  have f9: "\<And> i. ufDom\<cdot>(Lub Y)= ufDom\<cdot>(Y i)"
    by (simp add: f1)

  have f10: "\<And> i. cont (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    by (metis (no_types) f1 ufapplyout_uf_cont)
  
  have f12: "(\<lambda>i::nat. \<Lambda> (x::'a ). (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
              = (\<lambda>i::nat. \<Lambda> (x::'a ). (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    using f1 by auto

  have f30: "\<And> i .(\<Lambda> (x::'a). (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                    =  (\<Lambda> (x::'a). (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    using f1 by auto

  have f30_rev: "\<And> i .  (\<Lambda> (x::'a ). (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                       = (\<Lambda> (x::'a). (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    by (simp add: f30)

  have f31: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)

  have f14: "chain (\<lambda>i::nat. \<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))"
    (* see general process above *)
  proof (rule chainI)
    fix i::nat
    have f141: "ufDom\<cdot>(Y i) = ufDom\<cdot>(Y (Suc i))"
      using f1 by auto
    show "(\<Lambda> (x::'a). (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) \<sqsubseteq> (\<Lambda> (x::'a). (ubclDom\<cdot>x = ufDom\<cdot>(Y (Suc i)))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
      apply (rule cfun_below)
        apply (simp_all add: f10)       
      apply (subst f141)
      by (smt assms(1) below_option_def below_ufun_def cfun_below_iff cont_pref_eq1I fun_belowI po_class.chainE some_below)
  qed

  have f20: "(\<Squnion>i. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) 
                  = (Abs_cufun (\<Squnion>i.  (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))))"
    apply (subst abs_uf_lub_chain)
    apply (simp_all add: f12, simp add: f14)
     apply (subst f30)
     apply (simp add: ufWell_def, rule)
      apply (simp add: domIff2)
      apply auto[1]
     apply (rule_tac x="ufRan\<cdot>(Y i)" in exI)
     apply (smt assms(2) option.distinct(1) option.sel ran2exists ufran_2_ubcldom2)
    by (metis (mono_tags, lifting) Abs_cfun_inverse2 cfun.lub_cfun f10 f12 f14 lub_eq)
  have f60: "chain (\<lambda>i. (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)))"
  proof (rule chainI)
    have f161: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)
    show "\<And>i::nat. (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x)) 
                       \<sqsubseteq> (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y (Suc i) \<rightleftharpoons> x))"
      apply (rule ufbelowI3)
      by (metis below_ufun_def below_option_def below_refl cfun_below_iff 
                f161 monofun_cfun_arg)
  qed
  have f100: "\<And> x. (\<Squnion>i::nat. (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) x
                          = (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x))) x"
    apply (simp)
    apply rule
     apply auto
    apply (smt ch2ch_fun f60 lub_eq lub_fun option.sel option.simps(3) option_chain_cases some_lub_chain_eq)
    by (smt Abs_cfun_inverse2 below_option_def cfun_below_iff f10 f12 f14 is_ub_thelub lub_eq option.distinct(1) rep_cfun_cont)+
  have f51: "(\<Squnion>i::nat. (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>k\<cdot>(Y i \<rightleftharpoons> x))) 
                      = (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x)))"
    using f100 by auto 
  have f52: "\<And> x. (\<Squnion>i::nat. k\<cdot>(Y i \<rightleftharpoons> x)) = k\<cdot>(Lub Y \<rightleftharpoons> x)"
    proof -
      fix x :: "'a"
      have f1: "chain (\<lambda>n. Rep_ufun (Y n))"
        using assms(1) rep_ufun_chain by blast
      then have f2: "chain (the_abbrv (\<lambda>n. Rep_cufun (Y n) x))"
        using ch2ch_Rep_cfunL op_the_chain by blast
      have f3: "Lub Y = Abs_ufun (\<Squnion>n. Rep_ufun (Y n))"
        by (simp add: assms(1) lub_ufun)
    have "ufWell (\<Squnion>n. Rep_ufun (Y n))"
      by (simp add: f1 uf_well_lub)
    then have "Rep_cufun (Lub Y) = Rep_cfun (\<Squnion>n. Rep_ufun (Y n))"
        using f3 by simp
    then have "Rep_cufun (Lub Y) x = (\<Squnion>n. Rep_cufun (Y n) x)"
        using f1 by (simp add: contlub_cfun_fun)
    then have "Lub Y \<rightleftharpoons> x = (\<Squnion>n. \<lambda>n. Rep_cufun (Y n) x\<rightharpoonup>n)"
      using f1 ch2ch_Rep_cfunL op_the_lub by auto
    then have "(\<Squnion>n. k\<cdot>\<lambda>n. Rep_cufun (Y n) x\<rightharpoonup>n) = k\<cdot>(Lub Y \<rightleftharpoons> x)"
      using f2 by (simp add: cont2contlubE)
      then show "(\<Squnion>n. k\<cdot>(Y n \<rightleftharpoons> x)) = k\<cdot>(Lub Y \<rightleftharpoons> x)"
        by blast
    qed
  show ?thesis
    apply (subst f30_rev)
    apply (subst f20)
    apply (subst f51)
    apply (subst f52)
    by simp
qed

(* ufapplyout is cont if k doesnt change the dom of the input  *)
lemma ufapplyout_cont [simp]:  assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows "cont (\<lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"
  apply (rule contI2)
  using assms apply auto[1]
  by (simp add: assms)

    
(* further properties *)
subsection \<open>ufApplyOut Lemmas\<close>

  
(* insert rules *)
lemma ufapplyout_insert: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows "ufApplyOut k\<cdot>(f::'m ufun) =  Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))"
  by (simp add: ufApplyOut_def assms) 

(* dom of ufApplyOut is the same as the dom of input ufun  *)
lemma ufapplyout_dom [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows "ufDom\<cdot>(ufApplyOut k\<cdot>f) = ufDom\<cdot>f"
proof -
  have f1: "ufApplyOut k\<cdot>f =  Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))"
    by (simp add: assms ufapplyout_insert)
  have "ufDom\<cdot>(Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))) = ufDom\<cdot>f"
    by (simp add: assms ufran_2_ubcldom2)
  then show ?thesis
    by (simp add: f1)
qed

(* ran of ufApplyOut is the same as the ran of input ufun  *)
lemma ufapplyout_ran [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  shows "ufRan\<cdot>(ufApplyOut k\<cdot>f) = ufRan\<cdot>f"
proof -
  have f1: "ufApplyOut k\<cdot>f =  Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))"
    by (simp add: assms ufapplyout_insert)
  have "ufRan\<cdot>(Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))) = ufRan\<cdot>f"
    by (simp add: assms ufran_2_ubcldom2)
  then show ?thesis
    by (simp add: f1)
qed

(* substitution if the arg has the right domain  *)
lemma ufapplyout_apply [simp]:  assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" 
  and "ubclDom\<cdot>ub = ufDom\<cdot>f"
  shows "(ufApplyOut k\<cdot>f) \<rightleftharpoons> ub = k\<cdot>(f\<rightleftharpoons>ub)"
proof -
  have f1: "ufApplyOut k\<cdot>f =  Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))"
    by (simp add: assms ufapplyout_insert)
  have f2: "(ufApplyOut k\<cdot>f) \<rightleftharpoons> ub = (Rep_cufun (Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f) \<leadsto> k\<cdot>(f \<rightleftharpoons>x))))\<rightharpoonup>ub"
    by (simp add: f1)
  then show ?thesis
    apply (subst ufapplyout_insert)
     apply (simp add: assms)
    by (simp add: assms(1) assms(2) ufran_2_ubcldom2)
qed


lemma ufapplyout_inj [simp]:  
  assumes "\<And>b. ubclDom\<cdot>(f\<cdot>b) = ubclDom\<cdot>b" 
  and "inj (Rep_cfun f)"
shows "inj (Rep_cfun (ufApplyOut f))"
  apply rule
  apply(rule ufun_eqI)
  apply (metis assms(1) ufapplyout_dom)
  by (metis (mono_tags, lifting) assms(1) assms(2) inj_def ufapplyout_apply ufapplyout_dom)
  


  
section \<open>ufApplyIn\<close>
(* note that these proofs only really work if k does not change the domain *)

  
(* the ufapplyin function is cont  without lifting to ufun *)
lemma ufapplyin_uf_cont [simp]: "cont (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))"
proof (rule ufun_contI)
  show "\<And> x y. ubclDom\<cdot>x = ufDom\<cdot>g \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> g \<rightleftharpoons> k\<cdot>x \<sqsubseteq> g \<rightleftharpoons> k\<cdot>y"
    by (metis below_option_def below_refl monofun_cfun_arg)
  show "\<And>Y. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i::nat. Y i) = ufDom\<cdot>g 
                \<Longrightarrow> g \<rightleftharpoons> k\<cdot>(\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. g \<rightleftharpoons> k\<cdot>(Y i))"
    by (simp add: contlub_cfun_arg op_the_lub)
qed

(* the ran of ufapply is if the same as ran of the input ufun  *)
lemma ufapplyin_ran: assumes "\<And> x. ubclDom\<cdot>(k\<cdot>x) = ubclDom\<cdot>x" and "ubclDom\<cdot>b = ufDom\<cdot>g"
  shows "ubclDom\<cdot>(g \<rightleftharpoons> k\<cdot>b) = ufRan\<cdot>g"
  by (simp add: assms(1) assms(2) ufran_2_ubcldom2)

(* ufApplyin produces a ufWell function  *)
lemma ufapplyin_uf_wellI [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))"
  apply (simp add: ufWell_def, rule)
   apply (simp add: domIff2)
   apply auto[1]
  apply (rule_tac x= "ufRan\<cdot>g" in exI)
  by (smt assms option.distinct(1) option.sel ran2exists ufran_2_ubcldom2)

(* ufApplyIn has the same dom as the input ufun *)
lemma ufapplyin_uf_dom [simp]:  assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "ufDom\<cdot>(Abs_ufun (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) = ufDom\<cdot>g"
  apply (subst ufun_ufdom_abs, simp_all)
  apply (rule ufapplyin_uf_wellI)
  by (simp add: assms)

(* ufApplyIn has the same ran as the input ufun *)
lemma ufapplyin_uf_ran [simp]: assumes "\<And>b. ubclDom\<cdot>((k:: 'm \<rightarrow> 'm)\<cdot>b) = ubclDom\<cdot>b"
  shows "ufRan\<cdot>(Abs_ufun (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) =  ufRan\<cdot>g" (is "ufRan\<cdot>?F = ufRan\<cdot>?g")
proof -
  obtain x::'m  where x_def: "ubclDom\<cdot>x = ufDom\<cdot>g" 
    using ubcldom_ex by blast
  have f1: "ufDom\<cdot>(Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> g \<rightleftharpoons>(k\<cdot>x))) = ufDom\<cdot>g"
    using assms ufapplyin_uf_dom by blast
  have f2: "(Abs_cufun ((\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto>g \<rightleftharpoons>(k\<cdot>x))))\<rightleftharpoons>x = g \<rightleftharpoons>(k\<cdot>x)"
    by (simp add: assms x_def)
  then show ?thesis
    by (metis (no_types, lifting) assms f1 ufran_2_ubcldom2 x_def)
qed

(* substitution rules for ufapplyin  *)
lemma ufapplyin_uf_apply:  assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
                             and "ubclDom\<cdot>ub = ufDom\<cdot>g"
  shows "(Abs_ufun (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) \<rightleftharpoons> ub = g \<rightleftharpoons> (k\<cdot>ub)"
  by (simp add: assms)

(* ufApplyIn is a  monofun   *)
lemma ufapplyin_mono [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "monofun (\<lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"
  apply (rule monofunI)
  apply (rule ufbelowI2)
       apply (simp_all add: assms)
   apply (simp add: ufdom_below_eq)
  by (metis (full_types) below_ufun_def below_option_def below_refl monofun_cfun_fun)

(* this is just a proxy definition used to make the simplifier less agressive ;) *)
definition "applycd k = (\<lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"

(* applycd is a monofun  *)
lemma applycd_mono [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "monofun (applycd k)"
  apply (subst applycd_def)
  by (rule ufapplyin_mono, simp add: assms)

(* applycd substitution and reverse substitution lemmata *)
lemma applycd_rev: "(\<lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x)))) = applycd k"
  by (simp add: applycd_def)

lemma applycd_rev2: "Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))) = applycd k g"
  by (simp add: applycd_def)

(* ufapplyin produces a chain  *)
lemma ufapplyin_chain [simp]: assumes "chain Y" and "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "chain (\<lambda> i. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i)) \<leadsto> ((Y i) \<rightleftharpoons>(k\<cdot>x))))"
proof (rule chainI)
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chainE by auto

  have f2: "\<And> i. ufDom\<cdot>(Y (Suc i)) = ufDom\<cdot>(Y i)"
    using f1 ufdom_below_eq by auto

  have f3: "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> Abs_cufun (\<lambda>xa. (ubclDom\<cdot>xa = ufDom\<cdot>x) \<leadsto> (x \<rightleftharpoons>(k\<cdot>xa)))
                             \<sqsubseteq> Abs_cufun (\<lambda>xa. (ubclDom\<cdot>xa = ufDom\<cdot>y) \<leadsto> (y \<rightleftharpoons>(k\<cdot>xa)))"
    apply (simp add: applycd_rev2)
    using applycd_mono assms(2) monofunE by blast
  show "\<And>i. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x) 
            \<sqsubseteq> Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Y (Suc i)))\<leadsto>Y (Suc i) \<rightleftharpoons> k\<cdot>x)"
    apply (rule f3)
    by (simp add: f1)
qed

(* Abs_cufun is cont function for ufApplyIn  *)
lemma ufapplyin_chain_lub [simp]: assumes "chain Y" and "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows " Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(\<Squnion>i::nat. Y i))\<leadsto>(\<Squnion>i. Y i) \<rightleftharpoons> k\<cdot>x) \<sqsubseteq>
       (\<Squnion>i. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x))"
proof -
  have f1: "\<And> i. ufDom\<cdot>(Y i) = ufDom\<cdot>(\<Squnion>i. Y i)"
    using assms(1) ufdom_lub_eq by auto
  have f11: "\<And> i. ufDom\<cdot>(\<Squnion>i. Y i) = ufDom\<cdot>(Y i)"
    using assms(1) ufdom_lub_eq by auto

  have f10: "\<And> i. cont (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y)) \<leadsto> ((Y i) \<rightleftharpoons>(k\<cdot>x)))"
    apply (subst f11, subst ufapplyin_uf_cont)
    by simp

  (* handy substitution facts *)
  have f12: "(\<lambda> i::nat. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))) 
              = (\<lambda> i::nat. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
    using f1 by auto

  (* like f12 but without the outer lambda function *)
  have f30: "\<And> i. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)) 
                  = (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))"
    by (simp add: f1)
  have f30_rev: "\<And> i. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)) 
                      = (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))"
    by (simp add: f30)

  have f14: "chain (\<lambda> i::nat. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
  proof (rule chainI)
    have f141: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)

    have "\<And> i. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)) 
                \<sqsubseteq> (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y (Suc i)) \<rightleftharpoons> (k\<cdot>x))"
      apply (rule cfun_below)
        apply (simp_all add: f10)
      apply (rule ufbelowI3)
      by (metis (no_types) below_ufun_def below_option_def below_refl cfun_below_iff f141)
    thus "\<And> i. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y i))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x) 
               \<sqsubseteq> (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Y (Suc i)))\<leadsto>Y (Suc i) \<rightleftharpoons> k\<cdot>x)"
     by (simp add: f1)
  qed

  have f20: "(\<Squnion>i. Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))
            = Abs_cufun (\<Squnion>i.(\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
    apply (subst abs_uf_lub_chain)
    apply (simp_all add: f12)
      apply (simp add: f14)
     apply (subst f30)
     apply (rule ufapplyin_uf_wellI, simp add: assms)
    apply (subst f30_rev)
    apply (subst cfun.lub_cfun)
    apply (subst f30, simp add: f14)
    using f10 by auto[1]
    
  have f40: "\<And> f1 f2. Rep_cufun f1 \<sqsubseteq> Rep_cufun f2 \<Longrightarrow> f1 \<sqsubseteq> f2"
    by (meson below_ufun_def below_cfun_def)

  have f52: "\<And> x. (\<Squnion>i. (Y i) \<rightleftharpoons> (k\<cdot>x)) = ((\<Squnion>i. Y i) \<rightleftharpoons> k\<cdot>x)"
  proof -
    fix x :: "'a"
    have f0: "chain (\<lambda>n. Rep_ufun (Y n))"
      by (simp add: assms(1))
    then have f1: "ufWell (\<Squnion>n. Rep_ufun (Y n))"
      by (simp add: uf_well_lub)
    have "\<forall>f s. \<not> chain f \<or> (Lub f\<cdot>(s::'a )::'a option) = (\<Squnion>n. f n\<cdot>s)"
      using contlub_cfun_fun by blast
    then have "(\<Squnion>n. \<lambda>n. Rep_cufun (Y n) (k\<cdot>x)\<rightharpoonup>n) = Lub Y \<rightleftharpoons> k\<cdot>x"
      by (metis (mono_tags, lifting) f1  assms(1) ch2ch_Rep_cfunL contlub_cfun_fun 
            f0 image_cong lub_ufun op_the_lub rep_abs_cufun2)
    then show "(\<Squnion>n. Y n \<rightleftharpoons> k\<cdot>x) = (\<Squnion>n. Y n) \<rightleftharpoons> k\<cdot>x"
      by meson
  qed
  have f60: "chain (\<lambda> i. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x)))"
  proof (rule chainI)
    have f601: "\<And> i. Y i \<sqsubseteq> Y (Suc i)"
      by (simp add: assms(1) po_class.chainE)
    show "\<And>i. (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>Y i \<rightleftharpoons> k\<cdot>x) 
               \<sqsubseteq> (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>Y (Suc i) \<rightleftharpoons> k\<cdot>x)"
      apply (rule cfun_below)
        apply (simp_all add: f10)
        apply (rule ufbelowI3)
      by (metis (no_types) below_ufun_def below_option_def below_refl cfun_below_iff f601)
  qed
          
  have f100: "\<And> x. (\<Squnion>i::nat. (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))) x 
                          = (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i. (Y i) \<rightleftharpoons> (k\<cdot>x))) x"
    apply simp
    apply rule
     apply (smt Abs_cfun_inverse2 assms(2) ch2ch_Rep_cfunL contlub_cfun_fun f10 f11 f60 
                image_cong op_the_lub option.collapse option.discI option_chain_cases 
                rep_cfun_cont some_lub_chain_eq ufapplyin_eq_pre)
     by (smt Abs_cfun_inverse2 below_option_def cfun_below_iff f10 f12 f14 image_cong 
                    is_ub_thelub rep_cfun_cont)
   
   have f101: "(\<Squnion>i::nat. (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(Y i) \<rightleftharpoons> (k\<cdot>x))) 
                = (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>(Lub Y))\<leadsto>(\<Squnion>i. (Y i) \<rightleftharpoons> (k\<cdot>x)))" 
     using f100 by auto
  show ?thesis
    apply (subst f30_rev)
     apply (subst f20)
     apply (subst f101)
     apply (subst f52)
     by simp
 qed

(* ufApplyIn is cont overall*)
lemma ufapplyin_cont [simp]: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "cont (\<lambda> g. Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>g) \<leadsto> (g \<rightleftharpoons>(k\<cdot>x))))"
  apply (rule contI2)
  using assms apply auto[1]
  by (simp add: assms)


section \<open>More Lemmas\<close>


lemma f20: "\<And>g. cont (\<lambda> x. Rep_cufun g (k\<cdot>x))"
  by simp

lemma abs_cfun_cont: assumes "\<And>i. cont (Y i)" and "chain Y"  shows "Abs_cfun (\<Squnion>i::nat. (Y i)) = (\<Squnion>i::nat. Abs_cfun (Y i))"
  by (metis assms(1) assms(2) contlub_lambda fun_chain_iff lub_LAM)

lemma ufapplyin_chain_h: assumes "chain Y" and "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"  and "\<And>i. cont (Y i)"
  shows "(\<Lambda> (x::'a). (\<Squnion>i::nat. (Y i)) (k\<cdot>x)) \<sqsubseteq> (\<Squnion>i::nat. \<Lambda> (x::'a). (Y i) (k\<cdot>x))"
proof -
  have f2051: "cont (\<Squnion>i::nat. (Y i))"
    using assms by (simp add: admD adm_cont)
  have f2052: "\<And>i. cont (\<lambda>x. (Y i) (k\<cdot>x))"
    by (simp add: assms(3) cont_compose)
  have f2053: "cont (\<lambda>x. (Lub Y) (k\<cdot>x))"
    by (simp add: cont_compose f2051)
  have f20531: "cont (\<Squnion>i::nat. (\<lambda>x. (Y i) (k\<cdot>x)))"
  proof -
    have "\<forall>p f. (\<not> adm p \<or> \<not> chain f \<or> (\<exists>n. \<not> p (f n::'a \<Rightarrow> 'c))) \<or> p (Lub f)"
      using admD by blast
    then obtain nn :: "(nat \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow> bool) \<Rightarrow> nat" where
      f1: "\<forall>p f. (\<not> adm p \<or> \<not> chain f \<or> \<not> p (f (nn f p))) \<or> p (Lub f)"
      by meson
    obtain aa :: "(nat \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'a" where
      f2: "\<forall>f. (\<not> chain f \<or> (\<forall>a. chain (\<lambda>n. f n a))) \<and> (chain f \<or> \<not> chain (\<lambda>n. f n (aa f)))"
      by (metis (no_types) fun_chain_iff)
    have "\<forall>b. chain (\<lambda>n. Y n b)"
      using assms(1) fun_chain_iff by fastforce
    then have "chain (\<lambda>n a. Y n (k\<cdot>a))"
      using f2 by meson
    then show ?thesis
      using f1 adm_cont f2052 by blast
  qed
  have f2054: "(\<lambda>x. (Lub Y) (k\<cdot>x)) = (\<Squnion>i::nat. (\<lambda>x. (Y i) (k\<cdot>x))) "
  proof - 
    have f20541: "(\<lambda>x. (Lub Y) (k\<cdot>x)) = (\<lambda>x. (\<Squnion>i::nat. (Y i) (k\<cdot>x)))"
      by (simp add: assms(1) lub_fun)
    show ?thesis
      apply(subst f20541)
      apply(simp add: fun_eq_iff)
      apply(rule)
    proof - 
      fix x
      show "(\<Squnion>i::nat. Y i (k\<cdot>x)) = (\<Squnion>i::nat. (\<lambda>x::'a. Y i (k\<cdot>x))) x"
      proof -
        obtain aa :: "(nat \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> 'a" where
          f1: "\<forall>f. (\<not> chain f \<or> (\<forall>a. chain (\<lambda>n. f n a))) \<and> (chain f \<or> \<not> chain (\<lambda>n. f n (aa f)))"
          by (metis (no_types) fun_chain_iff)
        have "\<forall>b. chain (\<lambda>n. Y n b)"
          using assms(1) fun_chain_iff by fastforce
        then have "chain (\<lambda>n a. Y n (k\<cdot>a))"
          using f1 by meson
        then show ?thesis
          by (simp add: lub_fun)
      qed
    qed
  qed
  show ?thesis
    apply(subst f2054)
    apply(subst abs_cfun_cont)
    using assms(3) cont_Rep_cfun2 cont_compose apply blast
    apply (metis (mono_tags, lifting) assms(1) fun_chain_iff po_class.chain_def)
    by simp
qed

lemma ufapplyin_well_h: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" shows "\<And>g. ufWell (\<Lambda> x. Rep_cufun g (k\<cdot>x))"
  apply(simp add: ufWell_def)
  apply rule
   apply (metis assms(1) domIff rep_ufun_well ufWell_def)
  using assms(1) ufWell_def rep_ufun_well
  by (metis (no_types, lifting) ran2exists ufran_2_ubcldom)

lemma ufapplyin_cont_h: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b" shows "cont (\<lambda> g. Abs_cufun (\<lambda>x::'a. Rep_cufun g (k\<cdot>x)))"    
proof - 
  have f1: "monofun(\<lambda> g. Abs_cufun (\<lambda>x::'a. Rep_cufun g (k\<cdot>x)))"
  proof(rule monofunI)
    fix x :: "'a ufun" 
    fix y::"'a ufun" 
    assume "x \<sqsubseteq> y"
    show " Abs_cufun (\<lambda>xa. Rep_cufun x (k\<cdot>xa)) \<sqsubseteq> Abs_cufun (\<lambda>x. Rep_cufun y (k\<cdot>x))"
      apply(simp add: below_ufun_def)
      apply(subst rep_abs_cufun2, simp add: ufapplyin_well_h assms)
      apply(subst rep_abs_cufun2, simp add: ufapplyin_well_h assms) 
      using f20
      by (metis \<open>(x::'a ufun) \<sqsubseteq> (y::'a ufun)\<close> below_ufun_def cfun_below_iff monofun_LAM)
  qed
  have f2: "\<And>Y. chain Y \<Longrightarrow> Abs_cufun (\<lambda>x::'a. Rep_cufun (\<Squnion>i::nat. Y i) (k\<cdot>x)) \<sqsubseteq> (\<Squnion>i::nat. Abs_cufun (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x)))"
  proof - 
    fix Y ::"nat \<Rightarrow> 'a ufun"
    assume f200: "chain Y"
    have f2000: "\<And>i. cont (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x))"
      by simp
    have f2001: "cont (\<lambda>x::'a. Rep_cufun (Lub Y) (k\<cdot>x))"
      by simp
    have f2002: "\<And>i. ufWell (Abs_cfun (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x)))"
      by (simp add: assms ufapplyin_well_h)
    have f2003: "ufWell (Abs_cfun (\<lambda>x::'a. Rep_cufun (Lub Y) (k\<cdot>x)))"
      by (simp add: assms ufapplyin_well_h)
    (*have f201: "Rep_ufun (\<Squnion>i::nat. Abs_cufun (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x))) = (\<Squnion>i::nat. Abs_cfun (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x)))"
      using f20 f20_1 f20_2 f20_3 f200 f2001 f2002 
      
      sorry*)
    have f2004: "Rep_cufun (\<Squnion>i::nat. Y i) =  (\<Squnion>i::nat. Rep_cufun (Y i))"
      using f200
      by (simp add: lub_ufun rep_cfun_cont uf_well_lub)
    have f2005: "\<And>Y. chain Y \<Longrightarrow> Rep_ufun (\<Squnion>i::nat. Y i) =  (\<Squnion>i::nat. Rep_ufun (Y i))"
      by (metis cont_def lub_eq lub_eqI rep_ufun_cont)

    have f2006: "chain (\<lambda>i::nat. Abs_cufun (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x)))"
      using f200 assms 
      by (simp add: below_ufun_def cfun_below_iff f2002 po_class.chain_def)

    show "Abs_cufun (\<lambda>x::'a. Rep_cufun (\<Squnion>i::nat. Y i) (k\<cdot>x)) \<sqsubseteq> (\<Squnion>i::nat. Abs_cufun (\<lambda>x::'a. Rep_cufun (Y i) (k\<cdot>x)))"
      apply(simp add: below_ufun_def)
      apply(subst rep_abs_cufun2, simp add: ufapplyin_well_h assms)
      (*apply(simp add: f201)*)
      apply(subst f2004 (1))
      apply(subst f2005)
      apply(simp add: f2006)
      apply(simp add: f200 f2002)
      apply(subst ufapplyin_chain_h)
      using f200 assms apply simp_all
      by (simp add: fun_chain_iff)
  qed
  show ?thesis
    apply(rule contI2)
    using f1 apply simp
    using f2 by blast
qed

lemma ufapplyin_dom: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "ufDom\<cdot>(ufApplyIn k\<cdot>f) = ufDom\<cdot>f"
  apply(simp add: ufApplyIn_def)
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 assms ufapplyin_cont_h f20 ufapplyin_well_h rep_abs_cufun2 ubcldom_ex ufapplyin_eq_pre ufdom_2ufundom)

lemma ufapplyin_ran2: assumes "\<And>b. ubclDom\<cdot>(k\<cdot>b) = ubclDom\<cdot>b"
  shows "ufRan\<cdot>(ufApplyIn k\<cdot>f) = ufRan\<cdot>f"
proof - 
 have f20: "\<And>g. cont (\<lambda> x. Rep_cufun g (k\<cdot>x))"
    by simp
  have f21: "\<And>g. ufWell (\<Lambda> x. Rep_cufun g (k\<cdot>x))"
    by (simp add: assms ufapplyin_well_h)
  have f2: "cont (\<lambda> g. Abs_cufun (\<lambda>x::'a. Rep_cufun g (k\<cdot>x)))"   
    by (simp add: assms ufapplyin_cont_h)
  show ?thesis
    apply(simp add: ufApplyIn_def)
    (* times out when using global lemmas f2 f20 f21 *)
    by (smt Abs_cfun_inverse2 assms local.f2 local.f20 local.f21 rep_abs_cufun rep_abs_cufun2 ufapplyin_eq_pre ufapplyin_uf_dom ufdom_insert ufran_2_ubcldom ufran_2_ubcldom2)
qed

lemma ufapply_eq: assumes "\<And>b. ubclDom\<cdot>(f\<cdot>b) = ubclDom\<cdot>b"
              and "\<And>b. ubclDom\<cdot>(g\<cdot>b) = ubclDom\<cdot>b"
            shows "ufApplyIn f\<cdot>(ufApplyOut g\<cdot>h) = ufApplyOut g\<cdot>(ufApplyIn f\<cdot>h)"
proof - 
  have f1: "ufDom\<cdot>(ufApplyIn f\<cdot>h) = ufDom\<cdot>h"
    apply(simp add: ufApplyIn_def)
    by (metis (mono_tags, lifting) Abs_cfun_inverse2 assms(1) ufapplyin_cont_h f20 ufapplyin_well_h rep_abs_cufun ubcldom_ex ufapplyin_eq_pre ufdom_2ufundom)
  
  have f3: "cont (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>h)\<leadsto>g\<cdot>(h \<rightleftharpoons> x))"
    by simp
  have f4: "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>h)\<leadsto>g\<cdot>(h \<rightleftharpoons> x))"
    apply(simp add: ufWell_def)
    apply rule
    using f3 apply (smt domI domIff f1)
    by (smt assms(2) option.inject option.simps(3) ran2exists ufran_2_ubcldom2)
  
  have f50: "cont (\<lambda>x::'a. Rep_cufun h (f\<cdot>x))"
    by simp
  have f51: "ufWell (\<Lambda> x. Rep_cufun h (f\<cdot>x))"
    apply(simp add: ufWell_def)
    apply rule
    apply (metis assms(1) domIff ufdom_not_empty ufun_dom2ufundom ufun_ufundom2dom)
    by (meson ran2exists ranI rep_ufun_well ufWell_def)
  have f5: "\<And>x. (Abs_cufun (\<lambda>x::'a. Rep_cufun h (f\<cdot>x)) \<rightleftharpoons> x) = (h \<rightleftharpoons> f\<cdot>x)"
    by (simp add: f51)

  show ?thesis
    apply(simp add: ufApplyOut_def)
    apply(simp add: ufapplyout_cont assms)
    apply(simp add: f1)
    apply(simp add: ufApplyIn_def)
    apply(simp add: ufapplyin_cont_h assms)
    apply(simp add: f3 f4)
    apply(subst ufApplyIn_def)    
    apply(subst Abs_cfun_inverse2)
     apply(simp add: ufapplyin_cont_h assms)
    apply(subst f5)
    using assms
    by simp
qed

lemma ufapplyin_inj_h: 
  fixes f :: "'a \<rightarrow> 'a"
   assumes "\<And>ub. ubclDom\<cdot>ub = ufDom\<cdot>uf1 \<Longrightarrow> uf1 \<rightleftharpoons> (f\<cdot>ub) = uf2 \<rightleftharpoons> (f\<cdot>ub)"
  and "\<And>ub. ubclDom\<cdot>(f\<cdot>ub) = ubclDom\<cdot>ub" 
  and "surj (Rep_cfun f)"
  and "ubclDom\<cdot>ub = ufDom\<cdot>uf1"
  shows "uf1 \<rightleftharpoons> ub = uf2 \<rightleftharpoons> ub"
proof -
  obtain ub2 where "f\<cdot>ub2 = ub"
    by (metis assms(3) surj_def)
  thus ?thesis
    using assms(1) assms(2) assms(4) by auto
qed

lemma ufapplyin_apply [simp]: assumes "\<And>b. ubclDom\<cdot>(f\<cdot>b) = ubclDom\<cdot>b"
  and "ubclDom\<cdot>ub = ufDom\<cdot>uf"
  shows "ufApplyIn f\<cdot>uf \<rightleftharpoons> ub = uf\<rightleftharpoons>(f\<cdot>ub)"
  by (simp add: assms(1) ufApplyIn_def ufapplyin_cont_h ufapplyin_well_h)

lemma ufapplyin_inj[simp]: assumes "\<And>b. ubclDom\<cdot>(f\<cdot>b) = ubclDom\<cdot>b" and "surj (Rep_cfun f)"
  shows "inj (Rep_cfun (ufApplyIn f))"
  apply rule
  apply simp
  apply(rule ufun_eqI)
  apply (metis assms(1) ufapplyin_dom)
  by (metis assms(1) assms(2) ufapplyin_dom ufapplyin_inj_h ufapplyin_apply)


end