theory SPF
  imports bundle.SB UFun_Comp UFun_applyIn inc.CPOFix
begin
default_sort message

type_synonym ('m,'n) SPF = "('m SB, 'n SB) ufun"


subsection \<open>spfStateFix\<close>

definition spfStateLeast :: "channel set \<Rightarrow> channel set \<Rightarrow>('s1::type \<Rightarrow> ('m,'m) SPF)" where
"spfStateLeast In Out \<equiv> (\<lambda> x. ufLeast In Out)"

definition spfStateFix ::"channel set \<Rightarrow> channel set \<Rightarrow>(('s1::type \<Rightarrow> ('m,'m) SPF) \<rightarrow> ('s1 \<Rightarrow> ('m,'m) SPF)) \<rightarrow> ('s1 \<Rightarrow> ('m,'m) SPF)" where
"spfStateFix In Out \<equiv> (\<Lambda> F.  fixg (spfStateLeast In Out)\<cdot>F)"


section \<open>Definitions with ufApplyIn\<close>

(* ToDo: make signature more general, output does not have to be an SB *)
definition spfRtIn :: "(('m,'n) SPF) \<rightarrow> (('m,'n) SPF)" where
"spfRtIn \<equiv> ufApplyIn sbRt"

definition spfConcIn :: "'m SB \<Rightarrow> ('m,'n) SPF \<rightarrow> ('m,'n) SPF" where
"spfConcIn sb = ufApplyIn (ubConcEq sb)"

section \<open>Definitions with ufApplyOut\<close>

(* ToDo: make signature more general, input does not have to be an SB *)
definition spfConcOut :: "'n SB \<Rightarrow> ('m,'n) SPF \<rightarrow> ('m,'n) SPF" where
"spfConcOut sb = ufApplyOut (ubConcEq sb)"

definition spfRtOut :: "(('m,'n) SPF) \<rightarrow> (('m,'n) SPF)" where
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
    have "\<forall>x0 x1. ((x1::'a \<Rightarrow> ('b stream\<^sup>\<Omega>, 'b stream\<^sup>\<Omega>) ufun) \<sqsubseteq> (if x1 \<sqsubseteq> x0\<cdot>x1 then \<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1 else x1)) = (if x1 \<sqsubseteq> x0\<cdot>x1 then x1 \<sqsubseteq> (\<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1) else x1 \<sqsubseteq> x1)"
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

lemma spfrt_ufleast: "spfRtIn\<cdot>(ufLeast In Out) = ufLeast In Out"
  apply (rule ufun_eqI)
   apply (simp_all add: ufclDom_ufun_def ubclDom_ubundle_def)
  by (simp add: ubclDom_ubundle_def ufleast_apply)

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


lemma spfConcIn_step[simp]:
  assumes  "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConcIn sb1\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>(ubConcEq sb1\<cdot>sb)"
  by (metis assms spfConcIn_def ubclDom_ubundle_def ubconceq_dom ufapplyin_apply)


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
    have dom_not_empty: "ubclDom\<cdot>b \<noteq> {} \<Longrightarrow> lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
      proof -
        assume a2: "ubclDom\<cdot>b \<noteq> {}"
        have h1: "ubclDom\<cdot>b \<subseteq> ubclDom\<cdot>sb"
          by (metis a1 assms(3) domD spfConcIn_dom ubclDom_ubundle_def ufdom_2ufundom)
        have h2: "ubLen sb = lnsuc\<cdot>0 \<Longrightarrow> \<forall>c \<in> ubclDom\<cdot>sb. lnsuc\<cdot>0 \<le> usclLen\<cdot>(sb . c)"
          by (smt Inf'_neq_0 fold_inf inject_lnsuc mem_Collect_eq ubLen_def ubclDom_ubundle_def wellorder_Least_lemma(2))
        have h3: "\<And>c::channel. c \<in> ubDom\<cdot>b \<Longrightarrow> c \<in> ubDom\<cdot>sb \<Longrightarrow> lnsuc\<cdot>(#(b  .  c)) \<le> #((ubUp\<cdot>sb  .  c) \<bullet> ubUp\<cdot>b  .  c)"
          apply (case_tac "#(b  .  c) = \<infinity>")
          apply (simp add: slen_sconc_snd_inf)
          apply (case_tac "#(sb  .  c) = \<infinity>")
          apply simp
          apply(simp add: ubup_insert ubconc_insert ubgetch_insert)
          proof - 
            fix c
            assume a3: "c \<in> ubDom\<cdot>b"
            assume a4: "c \<in> ubDom\<cdot>sb"
            assume a5: "#Rep_ubundle b\<rightharpoonup>c \<noteq> \<infinity>"
            assume a6: "#Rep_ubundle sb\<rightharpoonup>c \<noteq> \<infinity>"
            obtain k1 where k1_def: "#Rep_ubundle sb\<rightharpoonup>c = Fin k1"
              by (metis a6 lncases)
            obtain k2 where k2_def: "#Rep_ubundle b\<rightharpoonup>c = Fin k2"
              by (metis a5 lncases)
            have f1: "lnsuc\<cdot>0 \<le> Fin k1"
              using h2 k1_def
              by (metis a4 assms(2) ubclDom_ubundle_def ubgetch_insert usclLen_stream_def)
            have f2: "#(Rep_ubundle sb\<rightharpoonup>c \<bullet> Rep_ubundle b\<rightharpoonup>c) = Fin (k1+k2)"
              by (simp add: k1_def k2_def slen_sconc_all_finite)
            have f3: "lnsuc\<cdot>(Fin k2) \<le> Fin (k1+k2)"
              using f1 not_less_eq_eq by fastforce
            show "lnsuc\<cdot>(#Rep_ubundle b\<rightharpoonup>c) \<le> #(Rep_ubundle sb\<rightharpoonup>c \<bullet> Rep_ubundle b\<rightharpoonup>c)"
              using k1_def k2_def
              using f2 f3 by auto
          qed
        have h4: "lnsuc\<cdot>(ubclLen b) \<le> ubclLen(ubConcEq sb\<cdot>b)"
          proof-
            have f1: "\<forall>c \<in> ubclDom\<cdot>b. lnsuc\<cdot>(usclLen\<cdot>(b . c)) \<le> (usclLen\<cdot>(ubConcEq sb\<cdot>b . c))"
              apply rule
              proof - 
                fix c
                assume a7: "c \<in> ubclDom\<cdot>b"
                have g1: "c \<in> ubclDom\<cdot>sb"
                  using a7 h1 by auto
                show "lnsuc\<cdot>(usclLen\<cdot>(b  .  c)) \<le> usclLen\<cdot>(ubConcEq sb\<cdot>b  .  c)"
                  by (metis (no_types, lifting) a7 g1 h3 ubConc_usclConc_eq ubclDom_ubundle_def ubconceq_insert ubgetch_ubrestrict ubup_ubgetch usclConc_stream_def usclLen_stream_def)
              qed
            have f2: "\<forall>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(LEAST ln. ln\<in>{(usclLen\<cdot>(b. c)) | c. c \<in> ubDom\<cdot>b}) \<le> (usclLen\<cdot>(ubConcEq sb\<cdot>b . c))"
              by (metis (mono_tags, lifting) Least_le f1 lnsuc_lnle_emb mem_Collect_eq trans_lnle ubclDom_ubundle_def)
            have f3: "\<forall>c \<in> ubDom\<cdot>b. lnsuc\<cdot>(ubLen b) \<le> (usclLen\<cdot>(ubConcEq sb\<cdot>b . c))"
              apply (simp add: ubLen_def)
              using f2 by auto   
            show ?thesis
              by (metis f3 ubLen_geI ubclLen_ubundle_def ubconceq_dom)
          qed
        show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
          by (smt a1 assms(1) dual_order.trans h4 option.collapse spfConcIn_def spfConcIn_dom ubclDom_ubundle_def ubconceq_dom ufIsWeak_def ufapplyin_apply ufdom_2_dom_ctufun ufdom_2ufundom ufun_ufundom2dom)
      qed
    show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcIn sb\<cdot>spf \<rightleftharpoons> b)"
      using a1 dom_not_empty local.dom_empty ufdom_2ufundom by fastforce
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

lemma spfConcOut_weak_ublen_strong[simp]:
  assumes "ufIsWeak spf" and "ubLen sb = lnsuc\<cdot>0" and "ufRan\<cdot>spf \<subseteq> ubDom\<cdot>sb"
  shows "ufIsStrong (spfConcOut sb\<cdot>spf)"
  apply (simp add: ufIsStrong_def)
  apply rule+
  proof -
    fix b::"'a stream\<^sup>\<Omega>"
    assume a1: "b \<in> dom (Rep_cufun (spfConcOut sb\<cdot>spf))"
    have dom_empty: "ubclDom\<cdot>b = {} \<Longrightarrow> ufDom\<cdot>spf = {} \<Longrightarrow> lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcOut sb\<cdot>spf \<rightleftharpoons> b)"
      by (smt a1 assms(1) fold_inf sbConcEq_Len2 spfConcOut_dom spfConcOut_step trans_lnle ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ufIsWeak_def ufdom_2_dom_ctufun)
    have dom_not_empty: "ubclDom\<cdot>b \<noteq> {} \<Longrightarrow> lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcOut sb\<cdot>spf \<rightleftharpoons> b)"
      proof -
        assume a2: "ubclDom\<cdot>b \<noteq> {}"
        have test: "ubDom\<cdot>(spf \<rightleftharpoons> b) = ufRan\<cdot>spf"
          by (metis a1 domIff not_None_eq spfConcOut_dom ubclDom_ubundle_def ufdom_2ufundom ufran_2_ubcldom2)
        have h1: "ubDom\<cdot>(spf \<rightleftharpoons> b) \<subseteq> ubDom\<cdot>sb"
          by (metis a1 assms(3) rep_ufun_well spfConcOut_dom ubclDom_ubundle_def ubcldom_least_cs ufWell_def ufran_2_ubcldom2 ufunLeastIDom)
        have h21: "ubLen b \<le> ubLen(spf \<rightleftharpoons> b)"
          by (metis a1 assms(1) spfConcOut_dom ubclLen_ubundle_def ufIsWeak_def ufdom_2_dom_ctufun)
        have h22: "lnsuc\<cdot>(ubLen b) \<le> lnsuc\<cdot>(ubLen(spf \<rightleftharpoons> b))"
          by (simp add: h21)
        have h23: "(spfConcOut sb\<cdot>spf \<rightleftharpoons> b) = ubConcEq sb\<cdot>(spf \<rightleftharpoons> b)"
          by (metis a1 domIff option.collapse spfConcOut_dom spfConcOut_step ubclDom_ubundle_def ufdom_2ufundom)
        have h24: "ubDom\<cdot>(spf \<rightleftharpoons> b) = ubDom\<cdot>(spfConcOut sb\<cdot>spf \<rightleftharpoons> b)"
          using h23 by auto
        have h25: "\<And>c::channel. c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b) \<Longrightarrow> (spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . c = (ubUp\<cdot>sb  .  c) \<bullet> ubUp\<cdot>(spf \<rightleftharpoons> b)  .  c"
          by (smt h1 h23 subsetCE ubConc_usclConc_eq ubconceq_insert ubgetch_ubrestrict ubup_ubgetch usclConc_stream_def)
        have h2: "ubLen sb = lnsuc\<cdot>0 \<Longrightarrow> \<forall>c \<in> ubclDom\<cdot>sb. lnsuc\<cdot>0 \<le> usclLen\<cdot>(sb . c)"
          by (smt equals0D mem_Collect_eq ubLen_def ubclDom_ubundle_def wellorder_Least_lemma(2))
        have h3: "\<And>c::channel. c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b) \<Longrightarrow> c \<in> ubDom\<cdot>sb \<Longrightarrow> lnsuc\<cdot>(#((spf \<rightleftharpoons> b)  .  c)) \<le> #((ubUp\<cdot>sb  .  c) \<bullet> ubUp\<cdot>(spf \<rightleftharpoons> b)  .  c)"
          apply (case_tac "#((spf \<rightleftharpoons> b)   .  c) = \<infinity>")
          apply (simp add: slen_sconc_snd_inf)
          apply (case_tac "#(sb  .  c) = \<infinity>")
          apply simp
          apply(simp add: ubup_insert ubconc_insert ubgetch_insert)
          proof - 
            fix c
            assume a3: "c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)"
            assume a4: "c \<in> ubDom\<cdot>sb"
            assume a5: "#Rep_ubundle (spf \<rightleftharpoons> b)\<rightharpoonup>c \<noteq> \<infinity>"
            assume a6: "#Rep_ubundle sb\<rightharpoonup>c \<noteq> \<infinity>"
            obtain k1 where k1_def: "#Rep_ubundle sb\<rightharpoonup>c = Fin k1"
              by (metis a6 lncases)
            obtain k2 where k2_def: "#Rep_ubundle (spf \<rightleftharpoons> b)\<rightharpoonup>c = Fin k2"
              by (metis a5 lncases)
            have f1: "lnsuc\<cdot>0 \<le> Fin k1"
              using h2 k1_def
              by (metis a4 assms(2) ubclDom_ubundle_def ubgetch_insert usclLen_stream_def)
            have f2: "#(Rep_ubundle sb\<rightharpoonup>c \<bullet> Rep_ubundle (spf \<rightleftharpoons> b)\<rightharpoonup>c) = Fin (k1+k2)"
              by (simp add: k1_def k2_def slen_sconc_all_finite)
            have f3: "lnsuc\<cdot>(Fin k2) \<le> Fin (k1+k2)"
              using f1 not_less_eq_eq by fastforce
            show "lnsuc\<cdot>(#Rep_ubundle (spf \<rightleftharpoons> b)\<rightharpoonup>c) \<le> #(Rep_ubundle sb\<rightharpoonup>c \<bullet> Rep_ubundle (spf \<rightleftharpoons> b)\<rightharpoonup>c)"
              using k1_def k2_def
              using f2 f3 by auto
          qed  
        have h4: "lnsuc\<cdot>(ubLen (spf \<rightleftharpoons> b)) \<le> ubLen (spfConcOut sb\<cdot>spf \<rightleftharpoons> b)"
          proof-
            have f1: "\<forall>c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b). lnsuc\<cdot>(usclLen\<cdot>((spf \<rightleftharpoons> b) . c)) \<le> (usclLen\<cdot>((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . c))"
              apply rule
              proof - 
                fix c
                assume a7: "c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)"
                have g1: "c \<in> ubDom\<cdot>sb"
                  using a7 h1 by auto
                show "lnsuc\<cdot>(usclLen\<cdot>((spf \<rightleftharpoons> b)  .  c)) \<le> (usclLen\<cdot>((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . c))"
                  by (metis a7 g1 h25 h3 usclLen_stream_def)         
              qed
            have f2: "\<forall>c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b). lnsuc\<cdot>(LEAST ln. ln\<in>{(usclLen\<cdot>((spf \<rightleftharpoons> b). c)) | c. c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)}) \<le> (usclLen\<cdot>((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . c))"
              by (smt Least_le antisym_conv f1 le_cases lnsuc_lnle_emb mem_Collect_eq ord_eq_le_trans order.trans)
            have f3: "\<forall>c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b). lnsuc\<cdot>(ubLen(spf \<rightleftharpoons> b)) \<le> (usclLen\<cdot>((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . c))"
              apply (simp add: ubLen_def)
              proof -
                obtain cc :: channel where
                  "(\<exists>v0. v0 \<in> ubDom\<cdot>(spf \<rightleftharpoons> b) \<and> \<not> lnsuc\<cdot> (LEAST uu. \<exists>c. uu = usclLen\<cdot>((spf \<rightleftharpoons> b) . c) \<and> c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)) \<le> usclLen\<cdot> ((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . v0)) = (cc \<in> ubDom\<cdot>(spf \<rightleftharpoons> b) \<and> \<not> lnsuc\<cdot> (LEAST uu. \<exists>c. uu = usclLen\<cdot>((spf \<rightleftharpoons> b) . c) \<and> c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)) \<le> usclLen\<cdot> ((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . cc))"
                  by blast
                moreover
                { assume "\<exists>c. usclLen\<cdot>((spf \<rightleftharpoons> b) . cc) = usclLen\<cdot>((spf \<rightleftharpoons> b) . c) \<and> c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)"
                  then have "(LEAST l. \<exists>c. l = usclLen\<cdot>((spf \<rightleftharpoons> b) . c) \<and> c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)) \<le> usclLen\<cdot>((spf \<rightleftharpoons> b) . cc)"
                    by (simp add: Least_le)
                  then have "cc \<notin> ubDom\<cdot>(spf \<rightleftharpoons> b) \<or> lnsuc\<cdot> (LEAST l. \<exists>c. l = usclLen\<cdot>((spf \<rightleftharpoons> b) . c) \<and> c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)) \<le> usclLen\<cdot> ((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . cc)"
                    by (meson dual_order.trans f1 lnsuc_lnle_emb) }
                ultimately show "ubDom\<cdot>(spf \<rightleftharpoons> b) \<noteq> {} \<longrightarrow> (\<forall>c\<in>ubDom\<cdot>(spf \<rightleftharpoons> b). lnsuc\<cdot> (LEAST l. \<exists>c. l = usclLen\<cdot>((spf \<rightleftharpoons> b) . c) \<and> c \<in> ubDom\<cdot>(spf \<rightleftharpoons> b)) \<le> usclLen\<cdot> ((spfConcOut sb\<cdot>spf \<rightleftharpoons> b) . c))"
                  by blast
              qed
            show ?thesis
              by (simp add: f3 h24 ubLen_geI)
          qed
        show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcOut sb\<cdot>spf \<rightleftharpoons> b)"
          by (metis (no_types, hide_lams) dual_order.trans h22 h4 ubclLen_ubundle_def)
      qed
    show "lnsuc\<cdot>(ubclLen b) \<le> ubclLen (spfConcOut sb\<cdot>spf \<rightleftharpoons> b)"
      by (metis a1 dom_not_empty local.dom_empty rep_ufun_well spfConcOut_dom ubcldom_least_cs ufWell_def ufunLeastIDom)
  qed

end