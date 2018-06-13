theory SPF
  imports SB "../UFun_Comp" "../UFun_applyIn" "../inc/CPOFix"
begin
default_sort message

type_synonym 'm SPF = "'m SB ufun"


subsection ‹spfStateFix›

definition spfStateLeast :: "channel set ⇒ channel set ⇒('s1::type ⇒ 'm SPF)" where
"spfStateLeast In Out ≡ (λ x. ufLeast In Out)"

definition spfStateFix ::"channel set ⇒ channel set ⇒(('s1::type ⇒'m SPF) → ('s1 ⇒'m SPF)) → ('s1 ⇒ 'm SPF)" where
"spfStateFix In Out ≡ (Λ F.  fixg (spfStateLeast In Out)⋅F)"


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


subsection ‹more general lemma›
subsection ‹SPF_apply_Lub›

text{* Intro rule for spf well *}
lemma ufwellI:  assumes "⋀b. (b ∈ dom (Rep_cfun f)) ⟹ (ubDom⋅b = In)"
  and "(⋀b. b ∈ dom (Rep_cfun f) ⟹ ubDom⋅((Rep_cfun f)⇀b) = Out)"
  and "⋀b2. (ubDom⋅b2 = In) ⟹ (b2 ∈ dom (Rep_cfun f))"
  shows "ufWell f"
  by (metis assms(1) assms(2) assms(3) ubclDom_ubundle_def ufun_wellI)



(* move this to ufun *)
lemma spfapply_lub: assumes "chain Y"
  shows "(⨆ i. Y i) ⇌ sb = (⨆ i. ((Y i)  ⇌ sb))"
proof -
  have f1: "chain (λn. Rep_ufun (Y n))"
    by (simp add: assms)
  hence "ufWell (⨆n. Rep_ufun (Y n))"
    by (simp add: admD ufWell_adm2)
  hence "Rep_cufun (Lub Y) = Rep_cfun (⨆n. Rep_ufun (Y n))"
    by (simp add: assms lub_ufun)
  hence "Rep_cufun (Lub Y) sb = (⨆n. Rep_cufun (Y n) sb)"
    using f1 contlub_cfun_fun by auto
  hence "(⨆n. λn. Rep_cufun (Y n) sb⇀n) = Lub Y ⇌ sb"
    using f1 by (simp add: op_the_lub)
  thus ?thesis
    by auto
qed




subsection ‹spfStateLeast›

lemma spfStateLeast_dom [simp]: "∀x. ufDom⋅(spfStateLeast In Out x) = In"
  by (simp add: spfStateLeast_def)

lemma spfStateLeast_ran[simp]: "∀x. ufRan⋅(spfStateLeast In Out x) = Out"
  by (simp add: spfStateLeast_def)

lemma spfStateLeast_apply[simp]:
  assumes "ubDom⋅sb = In"
  shows "spfStateLeast In Out x ⇌ sb = ubLeast Out"
  apply(auto simp add: spfStateLeast_def ufLeast_def ubclLeast_ubundle_def assms ubclDom_ubundle_def)
  by (metis (no_types) assms option.sel ubclDom_ubundle_def ubclLeast_ubundle_def ufleast_rep_abs)

lemma spfStateLeast_bottom [simp]: assumes "∀x. ufDom⋅(f x) = In" and " ∀x. ufRan⋅(f x) = Out"
  shows "(spfStateLeast In Out) ⊑ f"
proof -
  have f1: "∀x. (spfStateLeast In Out x) ⊑ f x"
    by (simp add: assms(1) assms(2) spfStateLeast_def)
  show ?thesis
    by(simp add: below_fun_def f1)
qed

lemma spfStateLeast_least [simp]: "spfStateLeast In Out ⊑ z ∧ y ⊑ z ⟶ spfStateLeast In Out ⊑ y"
proof -
  have "(∃a. ufLeast In Out \<notsqsubseteq> z a) ∨ (∃a. y a \<notsqsubseteq> z a) ∨ (spfStateLeast In Out ⊑ z ∧ y ⊑ z ⟶ spfStateLeast In Out ⊑ y)"
    by (metis (no_types) spfStateLeast_bottom ufdom_below_eq ufleast_ufRan ufleast_ufdom ufran_below)
  then show ?thesis
    by (simp add: fun_below_iff spfStateLeast_def)
qed


subsection ‹spfStateFix›

lemma spfStateFix_mono[simp]: "monofun (λ F.  fixg (spfStateLeast In Out)⋅F)"
  by (simp add: monofun_Rep_cfun2)

lemma spfStateFix_cont[simp]: "cont (λ F.  fixg (spfStateLeast In Out)⋅F)"
  by simp

lemma spfStateFix_apply: "spfStateFix In Out⋅F = fixg (spfStateLeast In Out)⋅F"
  by(simp add: spfStateFix_def )

(*least Fixpoint*)

lemma spfStateFix_fix: assumes "spfStateLeast In Out ⊑ F⋅(spfStateLeast In Out)"
                         shows "spfStateFix In Out⋅F = F⋅(spfStateFix In Out⋅F)"
  by (metis (no_types, hide_lams) assms eta_cfun fixg_fix spfStateFix_def spfStateLeast_least)

lemma spfsl_below_spfsf: "spfStateLeast In Out ⊑ spfStateFix In Out⋅F"
  proof (simp add: spfStateFix_def, simp add: fixg_def)
    have "∀x0 x1. ((x1::'a ⇒ ('b stream⇧Ω) ufun) ⊑ (if x1 ⊑ x0⋅x1 then ⨆uub. iterate uub⋅x0⋅x1 else x1)) = (if x1 ⊑ x0⋅x1 then x1 ⊑ (⨆uub. iterate uub⋅x0⋅x1) else x1 ⊑ x1)"
      by simp
    then show "spfStateLeast In Out ⊑ F⋅(spfStateLeast In Out) ⟶ spfStateLeast In Out ⊑ (⨆n. iterate n⋅F⋅(spfStateLeast In Out))"
      by (metis (no_types) fixg_pre)
  qed

lemma spfStateFix_least_fix: (* assumes "∀x. ufDom⋅((F⋅(spfStateLeast In Out)) x) = In"
                             and "∀x. ufRan⋅((F⋅(spfStateLeast In Out))x) = Out"
                             and "F⋅y = y" and "∀x. ufDom⋅(y x) = In" and "∀x. ufRan⋅(y x) = Out"
*)  assumes "spfStateLeast In Out ⊑ F⋅(spfStateLeast In Out)"
and "F⋅y = y" and "∀x. ufDom⋅(y x) = In" and "∀x. ufRan⋅(y x) = Out"
shows "spfStateFix In Out⋅F ⊑ y"
  apply (simp add: spfStateFix_apply)
  apply (rule fixg_least_fix)
  by ( simp_all add: assms)

lemma spfstatefix_dom:"ufDom⋅((spfStateFix In Out⋅ f) s) = In"
  by (metis (mono_tags) below_fun_def spfStateLeast_def spfsl_below_spfsf ufdom_below_eq ufleast_ufdom)
    
lemma spfstatefix_ran:"ufRan⋅((spfStateFix In Out⋅ f) s) = Out"
  by (metis below_fun_def spfStateLeast_ran spfsl_below_spfsf ufran_below)

subsection ‹ufApplyOut and ufApplyIn›

lemma spf_eq: assumes "ufDom⋅uf1 = ufDom⋅uf2"
  and "⋀ub. ubDom⋅ub = ufDom⋅uf1 ⟹ uf1 ⇌ ub = uf2 ⇌ ub"
shows "uf1 = uf2"
  by (metis assms(1) assms(2) ubclDom_ubundle_def ufun_eqI)

lemma ufapply_in_out:
  assumes "⋀sb. ubDom⋅(f⋅sb) =  ubDom⋅sb"
      and "⋀sb. ubDom⋅(g⋅sb) =  ubDom⋅sb"
    shows  "ufApplyIn f⋅(ufApplyOut g⋅spf) = ufApplyOut g⋅(ufApplyIn f⋅spf)"
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
