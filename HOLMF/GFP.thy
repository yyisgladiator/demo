theory GFP

imports LFP

begin
default_sort po


datatype 'a rev = Rev 'a

(* rev simply reverses the order of the original type *)
instantiation rev :: (po) po
begin
  fun below_rev:: "'a rev \<Rightarrow> 'a rev \<Rightarrow> bool" where
  "below_rev (Rev b1) (Rev b2) = (b2\<sqsubseteq>b1)"

  (* Show that the ordering definition defines a correct partial order. *)
  instance
    apply intro_classes
    using below_rev.elims(3) apply fastforce
    apply (metis GFP.below_rev.elims(3) GFP.rev.inject below_trans local.below_rev.elims(2))
    by (metis GFP.below_rev.elims(2) GFP.rev.inject below_antisym)

end


instantiation rev :: (division) division
begin
definition DIV_rev :: "'a rev set set" where
"DIV_rev = image (image Rev) DIV"

instance
  by intro_classes
end


class rev_div_cpo = division + po +

  assumes rev_div_non_empty: "DIV \<noteq> {}"

  assumes rev_div_inner_non_empty: "\<And>a. a\<in>DIV  \<Longrightarrow> a \<noteq> {}"


    (* every set is a cpo *)
  assumes rev_div_cpo: "\<And>S a. a\<in>DIV \<Longrightarrow> \<not>finite S \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. (Rev ` S) <<| Rev x"

begin
end


instantiation rev :: (rev_div_cpo) div_cpo
begin
lemma rev_bot_top: "x\<sqsubseteq>(Rev \<bottom>)"
  using below_rev.elims(3) by blast

lemma longchain_rev: "longChain S \<longleftrightarrow> longChain (Rev ` S)"
  apply auto
  apply(rule longchainI)
  apply (metis GFP.below_rev.elims(3) GFP.below_rev.simps GFP.rev.exhaust GFP.rev.inject imageE image_iff longChain_def)
  apply (simp add: longChain_def)
  apply(rule longchainI)
  apply (meson GFP.below_rev.simps image_iff longChain_def)
  by (simp add: longChain_def)

lemma rev_obtains: fixes S::"'a GFP.rev set"
  obtains A where "Rev ` A = S"
  by (metis GFP.rev.exhaust UNIV_I subset_iff subset_image_iff surj_def that)

instance
  apply(intro_classes)
  apply (simp add: DIV_rev_def rev_div_non_empty)
  using DIV_rev_def rev_div_inner_non_empty apply fastforce
  sorry
end







class div_upcpo = div_cpo +  
    (* every division has its own top element *)
  assumes div_upcpo: "\<And>a. a\<in>DIV \<Longrightarrow> \<exists>top\<in>a. \<forall>b\<in>a. b\<sqsubseteq>top"
begin

definition div_top::"'b::div_upcpo set \<Rightarrow> 'b" where
"div_top C = (THE topp.  topp\<in>C \<and> (\<forall>x\<in>C. x\<sqsubseteq>topp))"

lemma div_upcpo_top: assumes "C\<in>DIV" shows "\<exists>!top. top\<in>C \<and> (\<forall>x\<in>C. x\<sqsubseteq>top)"
  by (meson assms local.div_upcpo po_eq_conv)

lemma div_top: 
  fixes C ::"'b::div_upcpo set"
  assumes "C\<in>DIV" shows "(div_top C)\<in>C \<and> (\<forall>x\<in>C. x\<sqsubseteq>(div_top C))"
  apply(simp add: div_top_def)
  apply(rule theI' [of _ ])
  by (simp add: assms div_upcpo_class.div_upcpo_top)

end

class rev_div_upcpo = div_upcpo + rev_div_cpo

instantiation rev :: (rev_div_upcpo) div_pcpo
begin
instance 
  apply(intro_classes)
  sorry
end





definition reverseFun::"('a::po \<Rightarrow> 'b::po) \<Rightarrow> ('a rev \<Rightarrow> 'b rev)"where
"reverseFun f = (\<lambda>a. Rev (f ((inv Rev) a)))"

lemma reversefun_below: "f x \<sqsubseteq> f y \<longleftrightarrow> (reverseFun f) (Rev y) \<sqsubseteq>  (reverseFun f) (Rev x)"
  apply auto
  apply (metis (no_types, lifting) GFP.below_rev.elims(3) GFP.rev.inject f_inv_into_f rangeI reverseFun_def)
  by (metis (full_types) GFP.below_rev.simps GFP.rev.map UNIV_I dual_order.refl eq_iff f_inv_into_f imageI order_refl reverseFun_def)

definition gfp:: "'a::rev_div_upcpo set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"gfp A f = (inv Rev) (lfp (Rev ` A) (reverseFun f))"

lemma rev_bij: "bij Rev"
  by (metis GFP.rev.exhaust GFP.rev.inject bijI')

lemma rev_division: "C\<in>DIV \<Longrightarrow> (Rev ` C)\<in>DIV"
  by (simp add: DIV_rev_def)

lemma rev_goodformed: "goodFormed C f \<longleftrightarrow> goodFormed (Rev`C) (reverseFun f)"
  apply(auto simp add: goodFormed_def)
  apply (metis GFP.rev.inject f_inv_into_f image_iff rangeI reverseFun_def)
  by (smt GFP.rev.inject f_inv_into_f inv_into_into rangeI reverseFun_def)

lemma rev_monofun: "monofun f \<longleftrightarrow> monofun (reverseFun f)"
  apply auto
  apply(rule monofunI)
  apply (smt GFP.below_rev.elims(2) monofun_def reversefun_below)
  by (meson GFP.below_rev.simps monofun_def reversefun_below)

lemma rev_invrev: "Rev ((inv Rev) a) = a"
  by (meson GFP.rev.exhaust surj_def surj_f_inv_f)

lemma gfp_fix_h: 
    assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "Rev (gfp C f) = (reverseFun f  (Rev (gfp C f))) "
  unfolding gfp_def
  apply (simp add: rev_invrev)
  apply(rule lfp_fix)
  using assms(1) rev_monofun apply blast
  using assms(2) rev_goodformed apply blast
  using assms(3) rev_division by blast

lemma gfp_fix: 
    assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "(gfp C f) = (f  ((gfp C f))) "
  by (metis (no_types, lifting) GFP.rev.inject assms(1) assms(2) assms(3) gfp_fix_h rev_invrev reverseFun_def)

lemma gfp_div: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "(gfp C f) \<in> C"
proof - 
  have "(Rev (gfp C f) \<in> (Rev ` C))"
    by (metis GFP.gfp_def assms(1) assms(2) assms(3) lfp_div rev_division rev_goodformed rev_invrev rev_monofun)
  thus ?thesis
    by blast 
qed

lemma gfp_greatest: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
    and "y \<sqsubseteq> f y"
    and "y \<in> C"
  shows "y \<sqsubseteq> (gfp C f)"
proof - 
  have "Rev (gfp C f) \<sqsubseteq> Rev y"  
  apply (simp add: rev_invrev gfp_def)
    by (smt GFP.below_rev.simps GFP.rev.map assms imageI lfp_all rev_division rev_goodformed rev_invrev rev_monofun reverseFun_def)
  thus ?thesis
    by simp 
qed

end