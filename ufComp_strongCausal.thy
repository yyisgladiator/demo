theory ufComp_strongCausal
  imports UFun_Comp UBundle_Pcpo
begin

(* setup_lifting type_definition_ufun
setup_lifting type_definition_ubundle *)

(* default_sort uscl *)
default_sort uscl_pcpo
(* default_sort ubcl *)
(* default_sort ubcl_comp *)

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]





lemma ufComp_strongCausal: assumes "ufRan⋅f1 ∩ ufRan⋅f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2"
  shows "ufIsStrong (ufComp f1 (f2::'m ubundle ufun))"
  apply (simp add: ufIsStrong_def ufComp_def ubclLen_ubundle_def)
  apply rule+
proof -

  fix b::"'m ubundle"
  assume a0: "b ∈ dom (Rep_cufun (Abs_cufun (λx . (ubclDom⋅x = ufCompI f1 f2)↝ubFix (ufCompH f1 f2 x) (ufRan⋅f1 ∪ ufRan⋅f2))))"

(*
lemma ufcomp_well[simp]: assumes "ufRan⋅f1 ∩ ufRan⋅f2 = {}" 
  shows "ufWell (Abs_cfun (λ x. (ubclDom⋅x = ufCompI f1 f2) ↝ ubFix (ufCompH f1 f2 x) (ufRan⋅f1 ∪ ufRan⋅f2)))"
*)

  have z2: "ufWell (Λ(x::'m⇧Ω). (ubclDom⋅x = ufCompI f1 f2)↝ubFix (ufCompH f1 f2 x) (ufRan⋅f1 ∪ ufRan⋅f2))"
    apply (rule ufun_wellI)
    apply (simp_all  )
    apply (simp_all add: domIff2)
    apply (simp_all add: ubclDom_ubundle_def)
    apply auto

    sledgehammer
  proof -
    fix b::"'m⇧Ω"
    assume a1: "ubDom⋅(b::'m⇧Ω) = ufCompI f1 f2"
    fix x::"channel"

    show "x ∈ ubDom⋅(ubFix (ufCompH f1 f2 b) (ufRan⋅f1 ∪ ufRan⋅f2))"
      using assms
      sorry
  qed

  have y98: "b ∈ dom (λu. (ubclDom⋅u = ufCompI f1 f2)↝ubFix (ufCompH f1 f2 u) (ufRan⋅f1 ∪ ufRan⋅f2))"
    using a0 z2 by auto
  have y99: "ubDom⋅b = ufCompI f1 f2"
    using  y98 by (simp add: domIff2 ubclDom_ubundle_def)
  have chain_def: "chain (λa::nat. iter_ubfix2 (ufCompH f1 f2) a (ufRan⋅f1 ∪ ufRan⋅f2) b)"
    by (simp add: ubclDom_ubundle_def y99)

  have y0: "ubLen (iter_ubfix2 (ufCompH f1 f2) 0 (ufRan⋅f1 ∪ ufRan⋅f2) b) = Fin 0"
    apply (simp add: ufCompH_def ubclLeast_ubundle_def)
    apply (simp add: ubLeast_def)

      sorry    (*wird (noch?) nicht genutzt*)

  have y1: "chain (λi. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
    using ch2ch_monofun local.chain_def ublen_monofun by auto

  have y2: "⋀i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b) < lnsuc⋅(ubLen b) ⟹ 
    ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b) ≥ lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
    proof -
      fix i
      assume y21: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b) < lnsuc⋅(ubLen b)"

      have minOr: "⋀ x y. lnmin⋅x⋅y = x ∨ lnmin⋅x⋅y = y"
        sorry (*siehe TStream.thy, muss noch nach lnat*)
      have sucmin_minsuc: "⋀ x y . lnsuc⋅(lnmin⋅x⋅y) = lnmin⋅(lnsuc⋅x)⋅(lnsuc⋅y)"
        by simp

      have y22: "lnmin⋅(ubLen b)⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)) = (ubLen b) ∨
                 lnmin⋅(ubLen b)⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)) = (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
        by (simp add: minOr)

      have y23: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b) = lnmin⋅(ubLen b)⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
        apply (case_tac "(ubLen b) = ∞")
        apply simp
        proof -
          have "lnmin⋅(ubLen b) ⊑ lnmin⋅∞"
            by (meson inf_ub lnle_def monofun_cfun_arg)
          then show ?thesis
            by (metis (no_types) leD lnle2le lnless_def lnmin_fst_inf monofun_cfun_fun y21 y22)
        qed
      have y25: "lnmin⋅(lnsuc⋅(ubLen b))⋅(lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))) = lnsuc⋅(ubLen b) ∨
lnmin⋅(lnsuc⋅(ubLen b))⋅(lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))) = (lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)))"
        using minOr by blast

      have y99: "(lnmin⋅(lnsuc⋅(ubLen b))⋅(lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))) ≤ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b)
  = ((lnsuc⋅(ubLen b)) ≤ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b))) ∨
(lnmin⋅(lnsuc⋅(ubLen b))⋅(lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))) ≤ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b)
 = ((lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)))≤ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b)))"
        using y25 by auto

      have y98: "(lnsuc⋅(ubLen b)) ≤ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b) ∨ 
               (lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)))≤ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b)"
        
        apply rule (*? ? ? ? ? ? ? ? ? ?*)
        
        apply auto
        apply (case_tac "(ubLen b) = ∞")
        
        sorry



    show "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b) ≥ lnsuc⋅(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
      
      apply (subst y23)
      apply (simp add: ufCompH_def)
      apply (simp only: sucmin_minsuc)
      using lnle2le y21 y23 y98 by auto   
    qed

  have y3: "⋀i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b) ≥ lnsuc⋅(ubLen b) ⟹ 
  ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b) ≥ ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)"
    using y1 assms by (meson lnle_def po_class.chain_def)

  have z98: "ubLen (⨆i::nat. iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b) 
          = (⨆i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"

    sorry

  have z99: "lnsuc⋅(ubLen b) ≤ (⨆i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
    proof (cases "ubLen b = ∞")
      case True
      have "⋀i.  ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan⋅f1 ∪ ufRan⋅f2) b) ≥ lnsuc⋅( ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
        by (metis True fold_inf inf_ub less_le y2 y3)
      then have "(⨆i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b)) = ∞"
        by (metis (mono_tags, lifting) y1 inf_less_eq is_ub_thelub l42 le2lnle leI less_irrefl po_class.chainE po_eq_conv unique_inf_lub)
      then show ?thesis
        by (metis True fold_inf lnat_po_eq_conv)
    next
      case False
      obtain n where z991: "Fin n = ubLen b" by (metis False infI)
  
      have "lnsuc⋅(Fin n) ≤ (⨆i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan⋅f1 ∪ ufRan⋅f2) b))"
         proof -
          obtain nn :: "(nat ⇒ lnat) ⇒ nat" where
            f1: "∀f. (¬ chain f ∨ ¬ finite_chain f) ∨ Lub f = f (nn f)"
            by (metis l42)
          have "∀f. ¬ chain f ∨ finite_chain f ∨ Lub f = ∞"
            by (metis (full_types) unique_inf_lub)
          then have f2: "(⨆n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b)) ≠ ∞ ⟶ (⨆n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b)) = ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (λn. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b))) (ufRan⋅f1 ∪ ufRan⋅f2) b)"
            using f1 y1 by blast
          have f3: "ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (λn. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b))) (ufRan⋅f1 ∪ ufRan⋅f2) b) ⊑ ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc (nn (λn. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b)))) (ufRan⋅f1 ∪ ufRan⋅f2) b)"
            using po_class.chainE y1 by blast
          have "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc (nn (λn. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b)))) (ufRan⋅f1 ∪ ufRan⋅f2) b) ⊑ (⨆n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan⋅f1 ∪ ufRan⋅f2) b))"
            using is_ub_thelub y1 by blast
        then show ?thesis
          using f3 f2 by (metis inf_less_eq inf_ub le2lnle less_irrefl not_le_imp_less po_eq_conv y2 z991)
        qed
    thus ?thesis 
      by (simp add: z991)
    qed

  show "lnsuc⋅(ubLen b) ≤ ubLen (Abs_cufun (λx::'m⇧Ω. (ubclDom⋅x = ufCompI f1 f2)↝ubFix (ufCompH f1 f2 x) (ufRan⋅f1 ∪ ufRan⋅f2)) ⇌ b)"
    apply (simp add: z2)
    apply (simp add: ubclDom_ubundle_def)
    apply (simp_all add: assms y99)
    apply (simp add: ubFix_def)
    by (simp add: z98 z99)
qed