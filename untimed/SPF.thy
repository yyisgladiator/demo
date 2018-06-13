theory SPF
  imports SB "../UFun_Comp" "../UFun_applyIn" "../inc/CPOFix"
begin
default_sort message

type_synonym 'm SPF = "'m SB ufun"


subsection \<open>spfStateFix\<close>

definition spfStateLeast :: "channel set \<Rightarrow> channel set \<Rightarrow>('s1::type \<Rightarrow> 'm SPF)" where
"spfStateLeast In Out \<equiv> (\<lambda> x. ufLeast In Out)"

definition spfStateFix ::"channel set \<Rightarrow> channel set \<Rightarrow>(('s1::type \<Rightarrow>'m SPF) \<rightarrow> ('s1 \<Rightarrow>'m SPF)) \<rightarrow> ('s1 \<Rightarrow> 'm SPF)" where
"spfStateFix In Out \<equiv> (\<Lambda> F.  fixg (spfStateLeast In Out)\<cdot>F)"


section ‹Definitions with ufApplyIn›

(* ToDo: make signature more general, output does not have to be an SB *)
definition spfRtIn :: "('m SB ufun) → ('m SB ufun)" where
"spfRtIn ≡ ufApplyIn sbRt"

definition spfConcIn :: "'m SB ⇒ 'm SPF → 'm SPF" where
"spfConcIn sb = ufApplyIn (ubConcEq sb)"

section ‹Definitions with ufApplyOut›

(* ToDo: make signature more general, input does not have to be an SB *)
definition spfConcOut :: "'m SB ⇒ 'm SPF → 'm SPF" where
"spfConcOut sb = ufApplyOut (ubConcEq sb)"

definition spfRtOut :: "('m SB ufun) → ('m SB ufun)" where
"spfRtOut ≡ ufApplyOut sbRt"


subsection \<open>more general lemma\<close>
subsection \<open>SPF_apply_Lub\<close>

text{* Intro rule for spf well *}
lemma ufwellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (ubDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> ubDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (ubDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  shows "ufWell f"
  by (metis assms(1) assms(2) assms(3) ubclDom_ubundle_def ufun_wellI)



(* move this to ufun *)
lemma spfapply_lub: assumes "chain Y"
  shows "(\<Squnion> i. Y i) \<rightleftharpoons> sb = (\<Squnion> i. ((Y i)  \<rightleftharpoons> sb))"
proof -
  have f1: "chain (\<lambda>n. Rep_ufun (Y n))"
    by (simp add: assms)
  hence "ufWell (\<Squnion>n. Rep_ufun (Y n))"
    by (simp add: admD ufWell_adm2)
  hence "Rep_cufun (Lub Y) = Rep_cfun (\<Squnion>n. Rep_ufun (Y n))"
    by (simp add: assms lub_ufun)
  hence "Rep_cufun (Lub Y) sb = (\<Squnion>n. Rep_cufun (Y n) sb)"
    using f1 contlub_cfun_fun by auto
  hence "(\<Squnion>n. \<lambda>n. Rep_cufun (Y n) sb\<rightharpoonup>n) = Lub Y \<rightleftharpoons> sb"
    using f1 by (simp add: op_the_lub)
  thus ?thesis
    by auto
qed




subsection \<open>spfStateLeast\<close>

lemma spfStateLeast_dom [simp]: "\<forall>x. ufDom\<cdot>(spfStateLeast In Out x) = In"
  by (simp add: spfStateLeast_def)

lemma spfStateLeast_ran[simp]: "\<forall>x. ufRan\<cdot>(spfStateLeast In Out x) = Out"
  by (simp add: spfStateLeast_def)

lemma spfStateLeast_apply[simp]:
  assumes "ubDom\<cdot>sb = In"
  shows "spfStateLeast In Out x \<rightleftharpoons> sb = ubLeast Out"
  apply(auto simp add: spfStateLeast_def ufLeast_def ubclLeast_ubundle_def assms ubclDom_ubundle_def)
  by (metis (no_types) assms option.sel ubclDom_ubundle_def ubclLeast_ubundle_def ufleast_rep_abs)

lemma spfStateLeast_bottom [simp]: assumes "\<forall>x. ufDom\<cdot>(f x) = In" and " \<forall>x. ufRan\<cdot>(f x) = Out"
  shows "(spfStateLeast In Out) \<sqsubseteq> f"
proof -
  have f1: "\<forall>x. (spfStateLeast In Out x) \<sqsubseteq> f x"
    by (simp add: assms(1) assms(2) spfStateLeast_def)
  show ?thesis
    by(simp add: below_fun_def f1)
qed

lemma spfStateLeast_least [simp]: "spfStateLeast In Out \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> spfStateLeast In Out \<sqsubseteq> y"
proof -
  have "(\<exists>a. ufLeast In Out \<notsqsubseteq> z a) \<or> (\<exists>a. y a \<notsqsubseteq> z a) \<or> (spfStateLeast In Out \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> spfStateLeast In Out \<sqsubseteq> y)"
    by (metis (no_types) spfStateLeast_bottom ufdom_below_eq ufleast_ufRan ufleast_ufdom ufran_below)
  then show ?thesis
    by (simp add: fun_below_iff spfStateLeast_def)
qed


subsection \<open>spfStateFix\<close>

lemma spfStateFix_mono[simp]: "monofun (\<lambda> F.  fixg (spfStateLeast In Out)\<cdot>F)"
  by (simp add: monofun_Rep_cfun2)

lemma spfStateFix_cont[simp]: "cont (\<lambda> F.  fixg (spfStateLeast In Out)\<cdot>F)"
  by simp

lemma spfStateFix_apply: "spfStateFix In Out\<cdot>F = fixg (spfStateLeast In Out)\<cdot>F"
  by(simp add: spfStateFix_def )

(*least Fixpoint*)

lemma spfStateFix_fix: assumes "spfStateLeast In Out \<sqsubseteq> F\<cdot>(spfStateLeast In Out)"
                         shows "spfStateFix In Out\<cdot>F = F\<cdot>(spfStateFix In Out\<cdot>F)"
  by (metis (no_types, hide_lams) assms eta_cfun fixg_fix spfStateFix_def spfStateLeast_least)

lemma spfsl_below_spfsf: "spfStateLeast In Out \<sqsubseteq> spfStateFix In Out\<cdot>F"
  proof (simp add: spfStateFix_def, simp add: fixg_def)
    have "\<forall>x0 x1. ((x1::'a \<Rightarrow> ('b stream\<^sup>\<Omega>) ufun) \<sqsubseteq> (if x1 \<sqsubseteq> x0\<cdot>x1 then \<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1 else x1)) = (if x1 \<sqsubseteq> x0\<cdot>x1 then x1 \<sqsubseteq> (\<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1) else x1 \<sqsubseteq> x1)"
      by simp
    then show "spfStateLeast In Out \<sqsubseteq> F\<cdot>(spfStateLeast In Out) \<longrightarrow> spfStateLeast In Out \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>F\<cdot>(spfStateLeast In Out))"
      by (metis (no_types) fixg_pre)
  qed

lemma spfStateFix_least_fix: (* assumes "\<forall>x. ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In"
                             and "\<forall>x. ufRan\<cdot>((F\<cdot>(spfStateLeast In Out))x) = Out"
                             and "F\<cdot>y = y" and "\<forall>x. ufDom\<cdot>(y x) = In" and "\<forall>x. ufRan\<cdot>(y x) = Out"
*)  assumes "spfStateLeast In Out \<sqsubseteq> F\<cdot>(spfStateLeast In Out)"
and "F\<cdot>y = y" and "\<forall>x. ufDom\<cdot>(y x) = In" and "\<forall>x. ufRan\<cdot>(y x) = Out"
shows "spfStateFix In Out\<cdot>F \<sqsubseteq> y"
  apply (simp add: spfStateFix_apply)
  apply (rule fixg_least_fix)
  by ( simp_all add: assms)

lemma spfstatefix_dom:"ufDom\<cdot>((spfStateFix In Out\<cdot> f) s) = In"
  by (metis (mono_tags) below_fun_def spfStateLeast_def spfsl_below_spfsf ufdom_below_eq ufleast_ufdom)
    
lemma spfstatefix_ran:"ufRan\<cdot>((spfStateFix In Out\<cdot> f) s) = Out"
  by (metis below_fun_def spfStateLeast_ran spfsl_below_spfsf ufran_below)

subsection \<open>ufApplyOut and ufApplyIn\<close>

lemma spf_eq: assumes "ufDom\<cdot>uf1 = ufDom\<cdot>uf2"
  and "\<And>ub. ubDom\<cdot>ub = ufDom\<cdot>uf1 \<Longrightarrow> uf1 \<rightleftharpoons> ub = uf2 \<rightleftharpoons> ub"
shows "uf1 = uf2"
  by (metis assms(1) assms(2) ubclDom_ubundle_def ufun_eqI)

lemma ufapply_in_out:
  assumes "\<And>sb. ubDom\<cdot>(f\<cdot>sb) =  ubDom\<cdot>sb"
      and "\<And>sb. ubDom\<cdot>(g\<cdot>sb) =  ubDom\<cdot>sb"
    shows  "ufApplyIn f\<cdot>(ufApplyOut g\<cdot>spf) = ufApplyOut g\<cdot>(ufApplyIn f\<cdot>spf)"
  apply(rule ufun_eqI)
  using assms apply auto
  oops
  
  
subsection ‹spfRtIn lemma›

lemma spfRtIn_step[simp]: "(spfRtIn⋅spf)⇌sb = spf⇌(sbRt⋅sb)"
  apply(simp add: spfRtIn_def ufApplyIn_def)
  apply (subst Abs_cfun_inverse2)
   apply (rule ufapplyin_cont_h)
  by (simp add: ubclDom_ubundle_def ufapplyin_well_h) +

lemma spfRtIn_dom [simp] :"ufDom⋅(spfRtIn⋅spf) = ufDom⋅spf"
  unfolding spfRtIn_def
  by (simp add: ubclDom_ubundle_def ufapplyin_dom)

lemma spfRtIn_ran [simp]:"ufRan⋅(spfRtIn⋅spf) = ufRan⋅spf"
  unfolding spfRtIn_def
  apply(subst ufapplyin_ran2)
   apply (simp add: ubclDom_ubundle_def)
  by blast

lemma spfRtIn_spfConcOut: "(spfRtIn⋅(spfConcOut sb ⋅spf)) = (spfConcOut sb ⋅(spfRtIn⋅spf))"
  unfolding spfConcOut_def
  unfolding spfRtIn_def
  apply(subst ufapply_eq)
  apply (simp add: ubclDom_ubundle_def)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

subsection ‹spfConcIn lemma›

lemma spfConcIn_step[simp]:
  assumes  "ubDom⋅sb = ufDom⋅spf"
  shows "(spfConcIn sb1⋅spf)⇌sb = spf⇌(ubConcEq sb1⋅sb)"
(* "(spfConcIn sb1⋅spf)⇌sb = ubConcEq sb1⋅(spf⇌sb)" *)
  apply(simp only: spfConcIn_def ufApplyIn_def)
(* apply (subst ufapplyin_uf_apply) *)       
  apply (subst Abs_cfun_inverse2)
   apply (rule ufapplyin_cont_h)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
  apply (simp add: assms ubclDom_ubundle_def)+
  sorry

lemma spfConcIn_dom[simp]:"ufDom⋅(spfConcIn sb ⋅spf) = ufDom⋅spf"
  unfolding spfConcIn_def
  apply(subst ufapplyin_dom)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfConcIn_ran [simp]:"ufRan⋅(spfConcIn sb ⋅spf) = ufRan⋅spf"
  unfolding spfConcIn_def
  apply(subst ufapplyin_ran2)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

subsection ‹spfRtOut lemma›

lemma spfRtOut_step[simp]: 
  assumes "ubDom⋅sb = ufDom⋅spf"
  shows "(spfRtOut⋅spf)⇌sb = sbRt⋅(spf⇌sb)"
  apply(simp only: spfRtOut_def)
  apply (subst ufapplyout_apply)
    apply (simp add: ubclDom_ubundle_def)
   apply (simp add: assms ubclDom_ubundle_def)
  by simp

lemma spfRtOut_dom [simp] :"ufDom⋅(spfRtOut⋅spf) = ufDom⋅spf"
  unfolding spfRtOut_def
  by (simp add: ubclDom_ubundle_def ufapplyout_dom)

lemma spfRtOut_ran [simp]:"ufRan⋅(spfRtOut⋅spf) = ufRan⋅spf"
  unfolding spfRtOut_def
  apply(subst ufapplyout_ran)
   apply (simp add: ubclDom_ubundle_def)
  by blast


subsection ‹spfConcOut lemma›

lemma spfConcOut_step[simp]:
  assumes "ubDom⋅sb = ufDom⋅spf"
  shows "(spfConcOut sb1⋅spf)⇌sb = ubConcEq sb1⋅(spf⇌sb)"
  apply(simp only: spfConcOut_def)
  apply (subst ufapplyout_apply)
    apply (metis ubclDom_ubundle_def ubconceq_dom)
   apply (simp add: assms ubclDom_ubundle_def)
  by simp

lemma spfConcOut_dom[simp]:"ufDom⋅(spfConcOut sb ⋅spf) = ufDom⋅spf"
  unfolding spfConcOut_def
  apply(subst ufapplyout_dom)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfConcOut_ran [simp]:"ufRan⋅(spfConcOut sb ⋅spf) = ufRan⋅spf"
  unfolding spfConcOut_def
  apply(subst ufapplyout_ran)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast


end
