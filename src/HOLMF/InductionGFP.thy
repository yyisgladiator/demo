theory InductionGFP

imports Induction GLB

begin


lemma gfp_induction: assumes "goodFormed C f" and "C \<in> DIV" and "monofun f"
  and "longAdm_glb C P"
  and "P (div_top C)"
  and "\<And>x. x\<in>C \<Longrightarrow> P x \<Longrightarrow> P (f x)"
shows "P (gfp C f)"
  apply(simp add: gfp_def)
  apply(rule lfp_induction)
  using assms(1) rev_goodformed apply blast
  apply (simp add: assms(2) rev_division)
  using assms(3) rev_monofun apply blast
  using assms(4) longadm2glb apply blast
  apply (simp add: assms(2) assms(5))
  apply (metis assms(6) imageE rev.inject rev_invrev reverseFun_def)
  done



lemma gfp_gfp_below2:
    assumes "monofun g1" 
    and "monofun g2"
    and "goodFormed C1 g1" 
    and "goodFormed C2 g2"
    and "C1 \<in> DIV" 
    and "C2 \<in> DIV"
    and "\<And>x. x\<in>C1 \<Longrightarrow> g2 (f x) \<sqsubseteq> f (g1 x)"
    and "\<And>x. x\<in>C1 \<Longrightarrow> f x \<in>C2"
    and "div_top C2 \<sqsubseteq> f (div_top C1)"
    and "longAdm_glb C1 (\<lambda>a. GFP.gfp C2 g2 \<sqsubseteq> f a)"
  shows "(gfp C2 g2) \<sqsubseteq> f (gfp C1 g1)"
  apply(rule gfp_induction [of "C1" "g1"])
       apply( auto simp add: assms)
  using assms(2) assms(4) assms(6) assms(9) div_top gfp_div rev_below_trans apply blast
  by (metis (mono_tags, lifting) assms(2) assms(4) assms(6) assms(7) below_trans gfp_fix monofun_def)

lemma gfp_gfp_eq:
    assumes "monofun g1" 
    and "monofun g2"
    and "goodFormed C1 g1" 
    and "goodFormed C2 g2"
    and "C1 \<in> DIV" 
    and "C2 \<in> DIV"
    and "\<And>x. x\<in>C1 \<Longrightarrow> g2 (f x) = f (g1 x)"
    and "\<And>x. x\<in>C1 \<Longrightarrow> f x \<in>C2"
    and "div_top C2 \<sqsubseteq> f (div_top C1)"
    and "longAdm_glb C1 (\<lambda>a. GFP.gfp C2 g2 \<sqsubseteq> f a)"
  shows "(gfp C2 g2) = f (gfp C1 g1)"
proof - 
  have  "(gfp C2 g2) \<sqsubseteq> f (gfp C1 g1)" by(rule gfp_gfp_below2, auto simp add: assms)
  moreover have  "f (gfp C1 g1)\<sqsubseteq> (gfp C2 g2)" by(rule gfp_gfp_below, auto simp add: assms)
  ultimately show ?thesis
    using below_antisym by blast 
qed



end
