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


(*assms*)
lemma sbRtLen: assumes "ubLen x = Fin ( Suc(y))" 
  shows "ubLen (sbRt\<cdot>x) = Fin y"
  sorry
(*nach SB.thy ? *)
lemma sbRt_inf: assumes "ubLen ub = \<infinity>" shows "ubLen (sbRt\<cdot>ub) = \<infinity>"
  proof (cases "ubDom\<cdot>ub = {}")
    case True
    have a1: "ubDom\<cdot>(sbRt\<cdot>ub) = {}"
      by (simp add: True)
    show ?thesis
      unfolding ubLen_def
      apply (simp only: a1)
      by (simp add: ubLen_def)
  next
    case False
    have ch_inf: "\<And> c . c \<in> ubDom\<cdot>ub \<Longrightarrow> usclLen\<cdot>(ub  .  c) = \<infinity>"
    proof -
      fix c :: channel
      assume "c \<in> ubDom\<cdot>ub"
      then have f1: "c \<in> dom (Rep_ubundle ub)"
        by (metis (full_types, lifting) ubdom_insert)
      then have f5: "dom (Rep_ubundle ub) \<noteq> {} \<or> \<not> ({} \<noteq> ubDom\<cdot>(ubLeast (dom (Rep_ubundle ub))::'a stream\<^sup>\<Omega>))"
        by (metis (full_types, lifting) ubleast_ubdom)
      have f7: "\<not> (dom (Rep_ubundle ub) \<noteq> {}) \<or> ({} \<noteq> ubDom\<cdot>(ubLeast (dom (Rep_ubundle ub))::'a stream\<^sup>\<Omega>))"
        using f5 by auto
      have f75: "dom (Rep_ubundle ub) = {} \<or> \<not> ({} = ubDom\<cdot>(ubLeast (dom (Rep_ubundle ub))::'a stream\<^sup>\<Omega>))"
        by (metis ubleast_ubdom)
      then have f8: "\<not> (c \<in> dom (Rep_ubundle ub)) \<or> \<not> ({} = ubDom\<cdot>(ubLeast (dom (Rep_ubundle ub))::'a stream\<^sup>\<Omega>))"
        by blast
      
      have f15: "\<not> (\<infinity> = Fin (sK1 \<infinity>))"
        by (metis (full_types) not_less not_less_iff_gr_or_eq notinfI3)
      have f151: "(\<forall>n p. \<infinity> \<noteq> Least p \<or> \<not> p (Fin n))"
        by (metis (no_types) Least_le notinfI3)
      then have "(\<forall>u n. \<infinity> \<noteq> ubLen u \<or> Fin n \<notin> {usclLen\<cdot>(u . c::'a stream) |c. c \<in> ubDom\<cdot>u} \<or> {} = ubDom\<cdot>u)"
        using ubLen_def by (metis (mono_tags, lifting))
      then have f16: "(\<forall>n c. Fin n \<noteq> usclLen\<cdot>(ub . c) \<or> c \<notin> ubDom\<cdot>ub) \<or> \<not> (dom (Rep_ubundle ub) \<noteq> {})"
        by (metis (mono_tags, lifting) empty_iff f151 ubLen_def assms mem_Collect_eq ubdom_insert)
      have "\<not> (\<infinity> \<noteq> usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c) \<or> \<not> (dom (Rep_ubundle ub) \<noteq> {}) \<or> \<not> (\<exists>ca. usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c = usclLen\<cdot>(ub . ca) \<and> ca \<in> ubDom\<cdot>ub) \<or> \<not> spl107_759"
        using f16 by (metis (no_types) lncases)
      then have "\<infinity> = usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c"
        proof -
          obtain cc :: channel where
            f1: "usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c = usclLen\<cdot>(ub . cc) \<and> cc \<in> ubDom\<cdot>ub"
            by (metis f1 ubdom_insert ubgetch_insert)
          then have f2: "\<exists>c. usclLen\<cdot>(ub . cc) = usclLen\<cdot>(ub . c) \<and> c \<in> ubDom\<cdot>ub"
            by blast
          have f3: "ubLen ub = (LEAST l. l \<in> {usclLen\<cdot>(ub . c) |c. c \<in> ubDom\<cdot>ub})"
            by (simp add: False ubLen_def)
          have "(LEAST l. l \<in> {usclLen\<cdot>(ub . c) |c. c \<in> ubDom\<cdot>ub}) \<le> usclLen\<cdot>(ub . cc)"
            using f2 by (simp add: Least_le)
          then show ?thesis
            using f3 f1 by (simp add: assms)
        qed
      then show "usclLen\<cdot>(ub . c) = \<infinity>"
        by (metis (full_types, lifting) ubgetch_insert)
    qed

    have chrt_inf: "\<And> c . c \<in> ubDom\<cdot>ub \<Longrightarrow> usclLen\<cdot>(sbRt\<cdot>ub  .  c) = \<infinity>"
    proof -
      fix c::channel
      assume a2: "c \<in> ubDom\<cdot>ub"
      then have f1: "c \<in> dom (Rep_ubundle ub)"
        by (metis (full_types, lifting) ubdom_insert)
      have f161: "\<not> (\<infinity> \<noteq> usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c) \<or> \<not> (dom (Rep_ubundle ub) \<noteq> {}) \<or> \<not> (\<exists>ca. usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c = usclLen\<cdot>(ub . ca) \<and> ca \<in> ubDom\<cdot>ub) \<or> \<not> spl107_759"
        using ch_inf by auto
      then have f162: "\<infinity> = usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c"
        proof -
          obtain cc :: channel where
            f1: "usclLen\<cdot>Rep_ubundle ub\<rightharpoonup>c = usclLen\<cdot>(ub . cc) \<and> cc \<in> ubDom\<cdot>ub"
            by (metis f1 ubdom_insert ubgetch_insert)
          then have f2: "\<exists>c. usclLen\<cdot>(ub . cc) = usclLen\<cdot>(ub . c) \<and> c \<in> ubDom\<cdot>ub"
            by blast
          have f3: "ubLen ub = (LEAST l. l \<in> {usclLen\<cdot>(ub . c) |c. c \<in> ubDom\<cdot>ub})"
            by (simp add: False ubLen_def)
          have "(LEAST l. l \<in> {usclLen\<cdot>(ub . c) |c. c \<in> ubDom\<cdot>ub}) \<le> usclLen\<cdot>(ub . cc)"
            using f2 by (simp add: Least_le)
          then show ?thesis
            using f3 f1 by (simp add: assms)
        qed
    show "usclLen\<cdot>(sbRt\<cdot>ub  .  c) = \<infinity>"
      unfolding sbRt_def
      unfolding sbDrop_def
      by (metis f1 fair_sdrop f162 sbDrop_def sbdrop_sbgetch ubdom_insert ubgetch_insert usclLen_stream_def)
  qed


    show ?thesis
      using inf_less_eq chrt_inf sbrt_sbdom ubLen_geI by blast
  qed


lemma spfRtIn_strongF_isweak: assumes "ufIsStrong spf" shows "ufIsWeak (spfRtIn\<cdot>spf)"
  apply (simp add: ufIsWeak_def ubclLen_ubundle_def)
  apply rule+
  proof -
    fix b::"'a stream\<^sup>\<Omega>"
    assume a1: "b \<in> dom (Rep_cufun (spfRtIn\<cdot>spf))"
    show "ubLen b \<le> ubLen (spf \<rightleftharpoons> sbRt\<cdot>b)"
    proof (cases "ubDom\<cdot>b = {}")
      case True
      then show ?thesis
        by (metis (no_types, lifting) a1 assms empty_iff sbrt_sbdom spfRtIn_dom ubgetchI ufIsWeak_def ufdom_2_dom_ctufun ufisstrong_2_ufisweak ubclLen_ubundle_def)
    next
      case False
      have case1: "ubDom\<cdot>(b::'a stream\<^sup>\<Omega>) \<noteq> {}" by (simp add: False)
      show ?thesis
      proof (cases "ubLen b = \<infinity>")
        case True
        have x: "sbRt\<cdot>b \<in> dom (Rep_cufun spf)"
          by (metis (no_types) a1 domI domIff sbrt_conc_hd sbrt_sbdom spfRtIn_dom ubclDom_ubundle_def ufapplyin_eq_pre)
        have f0: "ubLen b = \<infinity>"
          using True by simp
        then have f1: "ubLen (sbRt\<cdot>b) = \<infinity>"
          unfolding sbRt_def
          by (metis sbRt_def sbRt_inf)
        have f01: "(ubLen (sbRt\<cdot>b)) = ubLen b"
          by (simp add: f0 f1)
        show ?thesis
          by (metis assms f01 ubclLen_ubundle_def ufIsWeak_def ufisstrong_2_ufisweak x)
      next
        case False
        have test0: " ubLen b \<noteq> \<infinity>"
          by (simp add: False)
        show ?thesis
        proof (cases "ubLen b = 0")
          case True
          then show ?thesis
            by simp
        next
          case False
          have len1: "lnsuc\<cdot>(ubLen (sbRt\<cdot>b)) = ubLen b"
            unfolding sbRt_def
            using  sbRtLen
            by (metis False Fin_02bot Fin_Suc lncases lnzero_def old.nat.exhaust sbRt_def test0)
          have len2: "(ubLen b) \<le> ubLen (spf \<rightleftharpoons> sbRt\<cdot>b)"
            by (metis (no_types, lifting) assms a1 len1 sbrt_sbdom spfRtIn_dom ubclDom_ubundle_def ubclLen_ubundle_def ufIsStrong_def ufdom_2_dom_ctufun ufun_ufundom2dom)
          then show ?thesis
            by (simp add: len2)
        qed
      qed
    qed
  qed


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

lemma spfRtOut_strongF_isweak: assumes "ufIsStrong spf" shows "ufIsWeak (spfRtOut\<cdot>spf)"
  apply (simp add: ufIsWeak_def ubclLen_ubundle_def)
  apply rule+
  proof -
    fix b::"'a stream\<^sup>\<Omega>"
    assume a1: "b \<in> dom (Rep_cufun (spfRtOut\<cdot>spf))"
    show "ubLen b \<le> ubLen (spfRtOut\<cdot>spf \<rightleftharpoons> b)"
    proof (cases "ubLen b = \<infinity>")
      case True
      have lLen1: "ubLen b = \<infinity>"
        by (simp add: True)
      have eq1: "ubLen b = ubLen (sbRt\<cdot>b)"
        by (simp add: sbRt_inf True ubgetchI)
      have lLen2: "ubLen (sbRt\<cdot>b) = \<infinity>"
        using eq1 lLen1 by auto
      have lLen25: "ubLen (spf \<rightleftharpoons> b) = \<infinity>"
        by (metis assms a1 fold_inf inf_less_eq lLen1 spfRtOut_dom ubclLen_ubundle_def ufIsStrong_def ufdom_2_dom_ctufun)
      have llLen3: "ubLen (spfRtOut\<cdot>spf \<rightleftharpoons> b) = \<infinity>"
        unfolding spfRtOut_def
        by (metis (no_types, lifting) lLen25 spfRtOut_def spfRtOut_dom spfRtOut_step sbRt_inf ubclDom_ubundle_def option.collapse ufdom_2ufundom)
      show ?thesis
        by (simp add: llLen3)
    next
      case False
      have a2: "ubDom\<cdot>b \<noteq> {}"
        by (meson ubLen_def False)
      have a3: "ufDom\<cdot>spf \<noteq> {}"
        by (metis a2 a1 domD spfRtOut_dom ubclDom_ubundle_def ufdom_2ufundom)
      have a4: "ubDom\<cdot>b = ufDom\<cdot>spf"
        by (metis a1 domD spfRtOut_dom ubclDom_ubundle_def ufdom_2ufundom)
      have a5: "b \<in> dom (Rep_cufun spf)"
        using a1 spfRtOut_dom ufdom_2_dom_ctufun by blast
      show ?thesis
      proof (cases "ubLen (spf \<rightleftharpoons> b) = \<infinity>")
        case True
        then show ?thesis
          by (simp add: a4 sbRt_inf)
      next
        case False
        obtain n where n_def: "ubLen b = (Fin n)"
          by (metis False infI a1 assms inf_less_eq spfRtOut_dom ubclLen_ubundle_def ufIsWeak_def ufdom_2_dom_ctufun ufisstrong_2_ufisweak)
        obtain m where m_def: "ubLen (spf \<rightleftharpoons> b) = (Fin m)"
          using False infI by blast
        have f0: "lnsuc\<cdot>(ubLen b) \<le> ubLen (spf \<rightleftharpoons> b)"
          using assms by (simp add: a5 ubclLen_ubundle_def ufIsStrong_def)
        have f1: "m > n"
          using f0 by (simp add: m_def n_def)
        show ?thesis 
          unfolding spfRtOut_def
          by (metis (no_types, lifting) f1 Suc_leI Suc_le_D Suc_le_mono a4 less2nat m_def n_def sbRtLen spfRtOut_def spfRtOut_step)
      qed
    qed
  qed


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


end