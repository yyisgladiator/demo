theory SPF
  imports SB "../UFun_Comp" "../UFun_applyIn" "../inc/CPOFix"
begin
default_sort message

type_synonym 'm SPF = "'m SB \<Rrightarrow> 'm SB"

instance ubundle :: (uscl_conc) ubcl_comp
  sorry


subsection \<open>spfStateFix\<close>

definition spfStateLeast :: "channel set \<Rightarrow> channel set \<Rightarrow>('s1::type \<Rightarrow> 'm SPF)" where
"spfStateLeast In Out \<equiv> (\<lambda> x. ufLeast In Out)"

definition spfStateFix ::"channel set \<Rightarrow> channel set \<Rightarrow>(('s1::type \<Rightarrow>'m SPF) \<rightarrow> ('s1 \<Rightarrow>'m SPF)) \<rightarrow> ('s1 \<Rightarrow> 'm SPF)" where
"spfStateFix In Out \<equiv> (\<Lambda> F.  if \<forall>x. (ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = Out) then fixg (spfStateLeast In Out) F else (spfStateLeast In Out))"


section \<open>Definitions with spfApplyIn\<close>

(* ToDo: make signature more general, output does not have to be an SB *)
definition spfRt :: "('m SB \<Rrightarrow> 'a::ubcl) \<rightarrow> ('m SB \<Rrightarrow> 'a)" where
"spfRt \<equiv> ufApplyIn sbRt"

section \<open>Definitions with spfApplyOut\<close>

(* ToDo: make signature more general, input does not have to be an SB *)
definition spfConc :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfConc sb = ufApplyOut (ubConcEq sb)"


subsection \<open>more general lemma\<close>
subsection \<open>SPF_apply_Lub\<close>

text{* Intro rule for spf well *}
lemma ufwellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (ubDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> ubDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (ubDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  shows "ufWell f"
  by (metis assms(1) assms(2) assms(3) ubDom_ubundle_def ufun_wellI)



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

lemma spfStateLeast_mono: "monofun (\<lambda>x. spfLeast In Out)"
  by (simp add: monofunI)

lemma spfStateLeast_cont: "cont (\<lambda>x. spfLeast In Out)"
  by simp

lemma spfStateLeast_dom [simp]: "\<forall>x. ufDom\<cdot>(spfStateLeast In Out x) = In"
  by (simp add: spfStateLeast_def)

lemma spfStateLeast_ran[simp]: "\<forall>x. ufRan\<cdot>(spfStateLeast In Out x) = Out"
  by (simp add: spfStateLeast_def)

lemma spfStateLeast_apply[simp]:
  assumes "ubDom\<cdot>sb = In"
  shows "spfStateLeast In Out x \<rightleftharpoons> sb = ubLeast Out"
  apply(auto simp add: spfStateLeast_def ufLeast_def ubLeast_ubundle_def assms ubDom_ubundle_def)
  by (metis (no_types) assms option.sel ubDom_ubundle_def ubLeast_ubundle_def ufleast_rep_abs)

lemma spfStateLeast_bottom [simp]: assumes "\<forall>x. ufDom\<cdot>(f x) = In" and " \<forall>x. ufRan\<cdot>(f x) = Out"
  shows "(spfStateLeast In Out) \<sqsubseteq> f"
proof -
  have f1: "\<forall>x. (spfStateLeast In Out x) \<sqsubseteq> f x"
    by (simp add: assms(1) assms(2) spfStateLeast_def)
  show ?thesis
    by(simp add: below_fun_def f1)
qed

subsection \<open>spfStateFix\<close>

lemma spfStateFix_mono[simp]: "monofun (\<lambda> F.  if \<forall>x. (ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = Out) then fixg (spfStateLeast In Out) F else (spfStateLeast In Out))"
proof(rule monofunI)
  fix x::"('s1::type \<Rightarrow> 'm SPF) \<rightarrow> ('s1 \<Rightarrow> 'm SPF)" and y::"('s1 \<Rightarrow>'m SPF) \<rightarrow> ('s1 \<Rightarrow>'m SPF)"
  assume a1:"x \<sqsubseteq> y"
  show "(if \<forall>xa. ufDom\<cdot>((x\<cdot>(spfStateLeast In Out)) xa) = In \<and> ufRan\<cdot>((x\<cdot>(spfStateLeast In Out)) xa) = Out then fixg (spfStateLeast In Out) x else spfStateLeast In Out) \<sqsubseteq>
           (if \<forall>x. ufDom\<cdot>((y\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((y\<cdot>(spfStateLeast In Out)) x) = Out then fixg (spfStateLeast In Out) y else spfStateLeast In Out)"
  proof(cases "\<forall>xa. ufDom\<cdot>((x\<cdot>(spfStateLeast In Out)) xa) = In \<and> ufRan\<cdot>((x\<cdot>(spfStateLeast In Out)) xa) = Out")
    case True
    then  have h1:"\<forall>xa. ufDom\<cdot>((y\<cdot>(spfStateLeast In Out)) xa) = In \<and> ufRan\<cdot>((y\<cdot>(spfStateLeast In Out)) xa) = Out"
      by (metis (mono_tags, lifting) a1 cfun_below_iff fun_below_iff ufdom_below_eq ufran_below)
    then have "fixg (spfStateLeast In Out) x \<sqsubseteq> fixg (spfStateLeast In Out) y"
      by(simp add: fixg_def lub_iter_fixg_mono_req a1 True)
    then show ?thesis
      by (simp add: True h1)
  next
    case False
    then have h2: "\<not> (\<forall>xa. ufDom\<cdot>((y\<cdot>(spfStateLeast In Out)) xa) = In \<and> ufRan\<cdot>((y\<cdot>(spfStateLeast In Out)) xa) = Out)"
      by (metis (mono_tags, lifting) a1 cfun_below_iff fun_below_iff ufdom_below_eq ufran_below)
    then show ?thesis
      by (simp add: h2 False)
  qed
qed

lemma spfStateFix_cont[simp]: "cont (\<lambda> F.  if \<forall>x. (ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = Out) then fixg (spfStateLeast In Out) F else (spfStateLeast In Out))"
proof(rule Cont.contI2,simp)
  fix Y:: "nat \<Rightarrow> (('s1::type \<Rightarrow>'m SPF) \<rightarrow> ('s1 \<Rightarrow>'m SPF))"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. if \<forall>x. ufDom\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = Out then fixg (spfStateLeast In Out) (Y i)
                    else spfStateLeast In Out)"
  show "(if \<forall>x. ufDom\<cdot>(((\<Squnion>i. Y i)\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>(((\<Squnion>i. Y i)\<cdot>(spfStateLeast In Out)) x) = Out then fixg (spfStateLeast In Out) (\<Squnion>i. Y i)
          else spfStateLeast In Out) \<sqsubseteq>
         (\<Squnion>i. if \<forall>x. ufDom\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = Out then fixg (spfStateLeast In Out) (Y i) else spfStateLeast In Out)"
  proof(cases "\<forall>x. ufDom\<cdot>(((\<Squnion>i. Y i)\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>(((\<Squnion>i. Y i)\<cdot>(spfStateLeast In Out)) x) = Out")
    case True
      have "\<forall>i. Y i \<sqsubseteq> Y (Suc i)"
        by (simp add: a1 po_class.chainE)
      have f0:"\<forall>x. chain (\<lambda>i. (Y i\<cdot>(spfStateLeast In Out)) x)"
        using a1 ch2ch_Rep_cfunL ch2ch_fun by fastforce
      then have h1:"\<forall>x i. ufDom\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = Out"
        by (smt True a1 cfun_below_iff fun_below_iff is_ub_thelub ufdom_below_eq ufran_below)
    then show ?thesis
      by(simp add: True h1 fixg_def chain_lub_lub_iter_fixg a1)
  next
    case False
    have f0:"\<forall>x. chain (\<lambda>i. (Y i\<cdot>(spfStateLeast In Out)) x)"
      using a1 ch2ch_Rep_cfunL ch2ch_fun by fastforce
    then have f1: "\<forall>x. ufDom\<cdot>((Y elem_6\<cdot>(spfStateLeast In Out)) x) = ufDom\<cdot>((\<Squnion>i. (Y i \<cdot>(spfStateLeast In Out)))x)"
      proof -
        have "chain (\<lambda>n. Y n\<cdot>(spfStateLeast In Out))"
          by (metis a1 ch2ch_Rep_cfunL)
        then show ?thesis
          using ch2ch_fun lub_fun ufdom_lub_eq by fastforce
      qed
    have f2:"\<forall>x. ufRan\<cdot>((Y elem_6\<cdot>(spfStateLeast In Out)) x) = ufRan\<cdot>((\<Squnion>i. Y i\<cdot>(spfStateLeast In Out)) x)"
      proof -
        have "\<And>f n s. \<not> chain f \<or> ufRan\<cdot>(f n (s::'s1)::'m SPF) = ufRan\<cdot>(Lub f s)"
          by (metis ch2ch_fun is_ub_thelub lub_fun ufran_below)
        then show ?thesis
          using a1 ch2ch_Rep_cfunL by blast
      qed
    have f3:"\<forall>i. \<not>(\<forall>x. ufDom\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = In \<and> ufRan\<cdot>((Y i\<cdot>(spfStateLeast In Out)) x) = Out)"
      by (smt False a1 fun_belowD is_ub_thelub monofun_cfun_fun ufdom_below_eq ufran_below)
    have f4: "\<And>s n. ufRan\<cdot>(\<Squnion>n. (Y n\<cdot>(spfStateLeast In Out)) s) = ufRan\<cdot>((Y n\<cdot>(spfStateLeast In Out)) s)"
      using f0 is_ub_thelub ufran_below by blast
      have f5: "\<And>s n. ufDom\<cdot>(\<Squnion>n. (Y n\<cdot>(spfStateLeast In Out)) s) = ufDom\<cdot>((Y n\<cdot>(spfStateLeast In Out)) s)"
        using f0 ufdom_lub_eq by fastforce
    show ?thesis
      by(simp add: f3 False)
    qed
qed


lemma spfStateFix_apply[simp]: assumes "\<forall>x. ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In" and "\<forall>x. ufRan\<cdot>((F\<cdot>(spfStateLeast In Out))x) = Out" shows "spfStateFix In Out\<cdot>F = fixg (spfStateLeast In Out) F"
  by(simp add: spfStateFix_def assms)

(*least Fixpoint*)

lemma spfStateFix_fix: assumes "\<forall>x. ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In" and "\<forall>x. ufRan\<cdot>((F\<cdot>(spfStateLeast In Out))x) = Out" shows "spfStateFix In Out\<cdot>F = F\<cdot>(spfStateFix In Out\<cdot>F)"
proof(simp add: assms,rule fixg_fix, simp add: assms)
  show "\<forall>y. y \<sqsubseteq> spfStateLeast In Out \<longrightarrow> spfStateLeast In Out = y"
    by (smt fun_below_iff po_eq_conv spfStateLeast_def ufLeast_bottom ufdom_below_eq ufleast_ufRan ufleast_ufdom ufran_below)
qed

lemma spfStateFix_least_fix: assumes "\<forall>x. ufDom\<cdot>((F\<cdot>(spfStateLeast In Out)) x) = In"
                             and "\<forall>x. ufRan\<cdot>((F\<cdot>(spfStateLeast In Out))x) = Out"
                             and "F\<cdot>y = y" and "\<forall>x. ufDom\<cdot>(y x) = In" and "\<forall>x. ufRan\<cdot>(y x) = Out"
                           shows "spfStateFix In Out\<cdot>F \<sqsubseteq> y"
proof(simp add: assms, rule fixg_least_fix, simp_all add: assms)
  show "\<forall>y. y \<sqsubseteq> spfStateLeast In Out \<longrightarrow> spfStateLeast In Out = y"
    by (smt fun_below_iff po_eq_conv spfStateLeast_def ufLeast_bottom ufdom_below_eq ufleast_ufRan ufleast_ufdom ufran_below)
qed



lemma spf_eq: assumes "ufDom\<cdot>uf1 = ufDom\<cdot>uf2"
  and "\<And>ub. ubDom\<cdot>ub = ufDom\<cdot>uf1 \<Longrightarrow> uf1 \<rightleftharpoons> ub = uf2 \<rightleftharpoons> ub"
shows "uf1 = uf2"
  by (metis assms(1) assms(2) ubDom_ubundle_def ufun_eqI)

lemma ufapply_in_out:
  assumes "\<And>sb. ubDom\<cdot>(f\<cdot>sb) =  ubDom\<cdot>sb"
      and "\<And>sb. ubDom\<cdot>(g\<cdot>sb) =  ubDom\<cdot>sb"
    shows  "ufApplyIn f\<cdot>(ufApplyOut g\<cdot>spf) = ufApplyOut g\<cdot>(ufApplyIn f\<cdot>spf)"
  apply(rule ufun_eqI)
  using assms apply auto
  oops

subsection \<open>spfRt lemma\<close>
lemma spfrt_step[simp]: "(spfRt\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>(sbRt\<cdot>sb)"
  apply(simp add: spfRt_def ufApplyIn_def)
  oops

subsection \<open>spfConc lemma\<close>
lemma spconc_step[simp]:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConc sb1\<cdot>spf)\<rightleftharpoons>sb = ubConcEq sb1\<cdot>(spf\<rightleftharpoons>sb)"
  apply(simp add: spfConc_def assms)
  oops







end
