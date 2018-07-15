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


section \<open>Definitions with ufApplyIn\<close>

(* ToDo: make signature more general, output does not have to be an SB *)
definition spfRtIn :: "('m SB ufun) \<rightarrow> ('m SB ufun)" where
"spfRtIn \<equiv> ufApplyIn sbRt"

definition spfConcIn :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfConcIn sb = ufApplyIn (ubConcEq sb)"

section \<open>Definitions with ufApplyOut\<close>

(* ToDo: make signature more general, input does not have to be an SB *)
definition spfConcOut :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfConcOut sb = ufApplyOut (ubConcEq sb)"

definition spfRtOut :: "('m SB ufun) \<rightarrow> ('m SB ufun)" where
"spfRtOut \<equiv> ufApplyOut sbRt"


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


subsection \<open>spfRtIn lemma\<close>

lemma spfRtIn_step[simp]: "(spfRtIn\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>(sbRt\<cdot>sb)"
  apply(simp add: spfRtIn_def ufApplyIn_def)
  apply (subst Abs_cfun_inverse2)
   apply (rule ufapplyin_cont_h)
  by (simp add: ubclDom_ubundle_def ufapplyin_well_h) +

lemma spfRtIn_dom [simp] :"ufDom\<cdot>(spfRtIn\<cdot>spf) = ufDom\<cdot>spf"
  unfolding spfRtIn_def
  by (simp add: ubclDom_ubundle_def ufapplyin_dom)

lemma spfRtIn_ran [simp]:"ufRan\<cdot>(spfRtIn\<cdot>spf) = ufRan\<cdot>spf"
  unfolding spfRtIn_def
  apply(subst ufapplyin_ran2)
   apply (simp add: ubclDom_ubundle_def)
  by blast

lemma spfRtIn_spfConcOut: "(spfRtIn\<cdot>(spfConcOut sb \<cdot>spf)) = (spfConcOut sb \<cdot>(spfRtIn\<cdot>spf))"
  unfolding spfConcOut_def
  unfolding spfRtIn_def
  apply(subst ufapply_eq)
  apply (simp add: ubclDom_ubundle_def)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast


lemma spfRt_inj_h: assumes "spfRtIn\<cdot>x = spfRtIn\<cdot>y" and "ubDom\<cdot>ub = ufDom\<cdot>x" 
  shows "x \<rightleftharpoons> ub = y \<rightleftharpoons> ub"
proof - 
  have "ubDom\<cdot>ub = ufDom\<cdot>y"
    by (metis assms(1) assms(2) spfRtIn_dom)
  obtain ubNEW where ubNEW_def: "sbRt\<cdot>ubNEW = ub"
    using sbrt_conc_hd by blast
  thus ?thesis
    by (metis assms(1) spfRtIn_step) 
qed

lemma spfRt_inj: "inj (Rep_cfun spfRtIn)"
  apply rule
  apply simp
  apply(rule spf_eq)
  apply (metis spfRtIn_dom)
  using spfRt_inj_h by blast
  

subsection \<open>spfConcIn lemma\<close>

(*
lemma spfConcIn_step[simp]:
  assumes  "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConcIn sb1\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>(ubConcEq sb1\<cdot>sb)"
(* "(spfConcIn sb1\<cdot>spf)\<rightleftharpoons>sb = ubConcEq sb1\<cdot>(spf\<rightleftharpoons>sb)" *)
  apply(simp only: spfConcIn_def ufApplyIn_def)     
  apply (subst Abs_cfun_inverse2)
   apply (rule ufapplyin_cont_h)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
    apply (subst rep_abs_cufun)
  apply simp_all
  sorry*)


lemma spfConcIn_dom[simp]:"ufDom\<cdot>(spfConcIn sb \<cdot>spf) = ufDom\<cdot>spf"
  unfolding spfConcIn_def
  apply(subst ufapplyin_dom)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfConcIn_ran [simp]:"ufRan\<cdot>(spfConcIn sb \<cdot>spf) = ufRan\<cdot>spf"
  unfolding spfConcIn_def
  apply(subst ufapplyin_ran2)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfConcIn_weak_ublen_strong[simp]:
  assumes "ufIsWeak spf" and "ubLen sb = lnsuc\<cdot>0" and "ufDom\<cdot>spf \<subseteq> ubDom\<cdot>sb"
  shows "ufIsStrong (spfConcIn sb\<cdot>spf)"
  apply (simp add: ufIsStrong_def)
  apply rule+
  proof -
    fix b::"'a stream\<^sup>\<Omega>"
    assume a1: " b \<in> dom (Rep_cufun (spfConcIn sb\<cdot>spf))"
    have dom_empty: "ubclDom\<cdot>b = {} \<Longrightarrow> ufDom\<cdot>spf = {} \<Longrightarrow> lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
      by (smt a1 assms(1) assms(3) inf.absorb_iff2 inf_ub lnat_po_eq_conv spfConcIn_def spfConcIn_dom ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ubconceq_dom ubconceq_insert ubrestrict_id ubrestrict_ubleast2 ufIsWeak_def ufapplyin_apply ufdom_2_dom_ctufun)
    have dom_not_empty: "ubclDom\<cdot>b \<noteq> {} \<Longrightarrow> ufDom\<cdot>spf \<noteq> {} "
      using a1 ufdom_2ufundom by fastforce
    have dom_not_empty2: "ubclDom\<cdot>b \<noteq> {} \<Longrightarrow> lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
      proof -
        assume a2: "ubclDom\<cdot>b \<noteq> {}"
        have h1: "ubclDom\<cdot>b \<subseteq> ubclDom\<cdot>sb"
          by (metis a1 assms(3) domD spfConcIn_dom ubclDom_ubundle_def ufdom_2ufundom)
        have h2: "ubclLen b \<le> ubclLen(ubConcEq sb\<cdot>b)"
          by (metis sbConcEq_Len2 ubclLen_ubundle_def)
        have h3: "ubLen sb = lnsuc\<cdot>0 \<Longrightarrow> \<forall>c \<in> ubclDom\<cdot>sb. lnsuc\<cdot>0 \<le> usclLen\<cdot>(sb . c)"
          by (smt Inf'_neq_0 fold_inf inject_lnsuc mem_Collect_eq ubLen_def ubclDom_ubundle_def wellorder_Least_lemma(2))
        have h4: "\<And>c::channel. c \<in> ubDom\<cdot>b \<Longrightarrow> c \<in> ubDom\<cdot>sb \<Longrightarrow> lnsuc\<cdot>(#(b  .  c)) \<le> #((ubUp\<cdot>sb  .  c) \<bullet> ubUp\<cdot>b  .  c)"
          apply (case_tac "#(b  .  c) = \<infinity>")
          apply (simp add: slen_sconc_snd_inf)
          apply (case_tac "#(sb  .  c) = \<infinity>")
          apply simp
          apply(simp add: ubup_insert ubconc_insert ubgetch_insert)
          proof - 
            fix c
            assume a1: "c \<in> ubDom\<cdot>b"
            assume a2: "c \<in> ubDom\<cdot>sb"
            assume a3: "#Rep_ubundle b\<rightharpoonup>c \<noteq> \<infinity>"
            assume a4: "#Rep_ubundle sb\<rightharpoonup>c \<noteq> \<infinity>"
            obtain k1 where k1_def: "#Rep_ubundle sb\<rightharpoonup>c = Fin k1"
              by (metis a4 lncases)
            obtain k2 where k2_def: "#Rep_ubundle b\<rightharpoonup>c = Fin k2"
              by (metis a3 lncases)
            have f1: "lnsuc\<cdot>0 \<le> Fin k1"
              using h3 k1_def
              by (metis a2 assms(2) ubclDom_ubundle_def ubgetch_insert usclLen_stream_def)
            have f2: "#(Rep_ubundle sb\<rightharpoonup>c \<bullet> Rep_ubundle b\<rightharpoonup>c) = Fin (k1+k2)"
              by (simp add: k1_def k2_def slen_sconc_all_finite)
            have f3: "lnsuc\<cdot>(Fin k2) \<le> Fin (k1+k2)"
              using f1 not_less_eq_eq by fastforce
            show "lnsuc\<cdot>(#Rep_ubundle b\<rightharpoonup>c) \<le> #(Rep_ubundle sb\<rightharpoonup>c \<bullet> Rep_ubundle b\<rightharpoonup>c)"
              using k1_def k2_def
              using f2 f3 by auto
          qed
        have h5: "lnsuc\<cdot>(ubclLen b) \<le> ubclLen(ubConcEq sb\<cdot>b)"
          proof-
            have f1: "\<exists>c \<in> ubDom\<cdot>b.(usclLen\<cdot>(b . c)) = ubclLen b"
              by (metis (no_types, lifting) a2 ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ublen_min_on_channel)
            have f2: "\<forall>c \<in> ubclDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) \<le> (usclLen\<cdot>(ubConcEq sb\<cdot>b . c))"
              apply rule
              proof - 
                fix c
                assume a1: "c \<in> ubclDom\<cdot>b"
                have g1: "ubclDom\<cdot>sb \<noteq> {}"
                  using a2 h1 by blast
                have g2: "c \<in> ubclDom\<cdot>sb"
                  using a1 h1 by auto
                show "lnsuc\<cdot>(usclLen\<cdot>(b  .  c)) \<le> usclLen\<cdot>(ubConcEq sb\<cdot>b  .  c)"
                  by (metis (no_types, lifting) a1 g2 h4 ubConc_usclConc_eq ubclDom_ubundle_def ubconceq_insert ubgetch_ubrestrict ubup_ubgetch usclConc_stream_def usclLen_stream_def)
              qed
            have f5: "\<exists>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) \<le> ubclLen (ubConcEq sb\<cdot>b)"
              by (metis (no_types, lifting) a2 f2 ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ubconceq_dom ublen_min_on_channel)
            have f6: "\<exists>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) = lnsuc\<cdot>(ubclLen b)"
              by (simp add: f1)
            show ?thesis
              sorry
          qed
        show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
          by (smt a1 assms(1) dual_order.trans h5 option.collapse spfConcIn_def spfConcIn_dom ubclDom_ubundle_def ubconceq_dom ufIsWeak_def ufapplyin_apply ufdom_2_dom_ctufun ufdom_2ufundom ufun_ufundom2dom)
      qed
    show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
      using a1 dom_not_empty2 local.dom_empty ufdom_2ufundom by fastforce
  qed

lemma spfConcIn_weak_ublen_strong2[simp]:
  assumes "ufIsWeak spf" and "ubLen sb = lnsuc\<cdot>0" and "ufDom\<cdot>spf \<subseteq> ubDom\<cdot>sb"
  shows "ufIsStrong (spfConcIn sb\<cdot>spf)"
  apply (simp add: ufIsStrong_def)
  apply rule+
  proof -
    fix b::"'a stream\<^sup>\<Omega>"
    have h22: "ubclDom\<cdot>b \<subseteq> ubclDom\<cdot>sb"
      sorry
    have h2: "b \<in> dom (Rep_cfun (Rep_ufun (spfConcIn sb\<cdot>spf)))"
      sorry
    have h3: "ubclLen b \<le> ubclLen(ubConcEq sb\<cdot>b)"
      by (metis sbConcEq_Len2 ubclLen_ubundle_def)
    have h4: "lnsuc\<cdot>(ubclLen b) \<le> ubclLen(ubConcEq sb\<cdot>b)"
      proof -
        have f1: "\<exists>c \<in> ubDom\<cdot>sb.(usclLen\<cdot>(sb . c)) = lnsuc\<cdot>0"
          by (metis (no_types, lifting) Inf'_neq_0 assms(2) fold_inf inject_lnsuc ubLen_def ublen_min_on_channel)
        have f2: "\<exists>c \<in> ubDom\<cdot>b.(usclLen\<cdot>(b . c)) = ubclLen b"
          by (smt Inf'_neq_0 assms(2) fold_inf h22 lnat.sel_rews(2) ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ublen_min_on_channel)
        have f3: "\<forall>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) \<le> (usclLen\<cdot>(ubConcEq sb\<cdot>b . c))"
          apply rule
          by (metis (mono_tags) domIff empty_iff h2 not_None_eq subsetI ubDom_subseteq ubclDom_ubundle_def ubcldom_least_cs ufdom_2ufundom)
        have f4: "\<exists>c \<in> ubDom\<cdot>b.(usclLen\<cdot>(ubConcEq sb\<cdot>b . c)) = ubclLen (ubConcEq sb\<cdot>b)"
          by (metis (no_types, lifting) Inf'_neq_0 h22 assms(2) fold_inf inject_lnsuc ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ubconceq_dom ublen_min_on_channel)
        have f5: "\<exists>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) = ubclLen (ubConcEq sb\<cdot>b)"
          by (metis (no_types, hide_lams) empty_subsetI f2 fold_inf h11 h22 rep_ufun_well ubDom_subseteq ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ubconceq_dom ubundle_ex ufWell_def)
        have f6: "\<exists>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) = lnsuc\<cdot>(ubclLen b)"
          using f2 by auto
        show ?thesis
          apply (simp add: ubclLen_ubundle_def)
          by (metis (mono_tags, hide_lams) all_not_in_conv dual_order.antisym empty_subsetI f2 rep_ufun_well ubDom_subseteq ubcldom_least_cs ubrestrict_ubdom ufRestrict_dom ufWell_def ufunLeastIDom)
      qed
    have equal: "spf \<rightleftharpoons> ubConcEq sb\<cdot>b = (spfConcIn sb\<cdot>spf) \<rightleftharpoons> b"
      by (metis (no_types, lifting) h11 h22 domIff spfConcIn_def ubclDom_ubundle_def ubconceq_dom ufapplyin_apply ufapplyin_eq_pre ufun_ufundom2dom)
    have equal2: "ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b) = ubclLen (spf \<rightleftharpoons> ubConcEq sb\<cdot>b)"
      using local.equal by auto
    have h10: "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spf \<rightleftharpoons> ubConcEq sb\<cdot>b)"
      by (metis (no_types, lifting) h11 h22 assms(1) dual_order.trans h4 ubclDom_ubundle_def ubconceq_dom ufIsWeak_def ufun_ufundom2dom)
    show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
      using h10 local.equal by auto
  qed

subsection \<open>spfRtOut lemma\<close>

lemma spfRtOut_step[simp]: 
  assumes "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfRtOut\<cdot>spf)\<rightleftharpoons>sb = sbRt\<cdot>(spf\<rightleftharpoons>sb)"
  apply(simp only: spfRtOut_def)
  apply (subst ufapplyout_apply)
    apply (simp add: ubclDom_ubundle_def)
   apply (simp add: assms ubclDom_ubundle_def)
  by simp

lemma spfRtOut_dom [simp] :"ufDom\<cdot>(spfRtOut\<cdot>spf) = ufDom\<cdot>spf"
  unfolding spfRtOut_def
  by (simp add: ubclDom_ubundle_def ufapplyout_dom)

lemma spfRtOut_ran [simp]:"ufRan\<cdot>(spfRtOut\<cdot>spf) = ufRan\<cdot>spf"
  unfolding spfRtOut_def
  apply(subst ufapplyout_ran)
   apply (simp add: ubclDom_ubundle_def)
  by blast

lemma spfRtOut_spfConcIn: "(spfRtOut\<cdot>(spfConcIn sb \<cdot>spf)) = (spfConcIn sb \<cdot>(spfRtOut\<cdot>spf))"
  apply (simp add: spfConcIn_def spfRtOut_def)
  apply(subst ufapply_eq)
    apply (metis ubclDom_ubundle_def ubconceq_dom)
   apply (simp add: ubclDom_ubundle_def)
  by blast


subsection \<open>spfConcOut lemma\<close>

lemma spfConcOut_step[simp]:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConcOut sb1\<cdot>spf)\<rightleftharpoons>sb = ubConcEq sb1\<cdot>(spf\<rightleftharpoons>sb)"
  apply(simp only: spfConcOut_def)
  apply (subst ufapplyout_apply)
    apply (metis ubclDom_ubundle_def ubconceq_dom)
   apply (simp add: assms ubclDom_ubundle_def)
  by simp

lemma spfConcOut_dom[simp]:"ufDom\<cdot>(spfConcOut sb \<cdot>spf) = ufDom\<cdot>spf"
  unfolding spfConcOut_def
  apply(subst ufapplyout_dom)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfConcOut_ran [simp]:"ufRan\<cdot>(spfConcOut sb \<cdot>spf) = ufRan\<cdot>spf"
  unfolding spfConcOut_def
  apply(subst ufapplyout_ran)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfconc_surj:
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows "inj (\<lambda>spf. spfConcOut sb\<cdot>spf)"
  apply(simp add: spfConcOut_def)
  using ufapplyin_inj assms
  by (metis sbconc_inj ubclDom_ubundle_def ubconceq_dom ufapplyout_inj) 

lemma spfConcOut_weak_ublen_strong[simp]:
  assumes "ufIsWeak spf" and "ubLen sb = lnsuc\<cdot>0"
  shows "ufIsStrong (spfConcOut sb\<cdot>spf)"
  apply (simp add: ufIsStrong_def)
  proof -
    have dom_equal: "sb \<in> dom (Rep_cfun (Rep_ufun spf)) \<Longrightarrow> lnsuc\<cdot>0 \<le> ubclLen(spf \<rightleftharpoons> sb)"
      by (metis assms(1) assms(2) ubclLen_ubundle_def ufIsWeak_def)
    have h1: "\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun (spfConcOut sb\<cdot>spf))) \<longrightarrow> lnsuc\<cdot>0 \<le> ubclLen(spfConcOut sb\<cdot>spf \<rightleftharpoons> b))"
     
  qed
  sorry




end