theory GFP

imports LFP

begin
default_sort po


datatype 'a rev = Rev 'a

lemma inv_rev [simp]: "(inv Rev) (Rev a) = a"
  by (meson GFP.rev.inject f_inv_into_f range_eqI)

lemma inv_rev2 [simp]: "(Rev) ((inv Rev) a) = a"
  by (metis GFP.rev.exhaust inv_rev)

lemma rev_bij: "bij Rev"
  by (metis GFP.rev.exhaust GFP.rev.inject bijI')

(* rev simply reverses the order of the original type *)
instantiation rev :: (po) po
begin
  fun below_rev:: "'a rev \<Rightarrow> 'a rev \<Rightarrow> bool" where
  "below_rev (Rev b1) (Rev b2) = (b2\<sqsubseteq>b1)"

  lemma below_rev_def: "b1 \<sqsubseteq> b2 = (((inv Rev) b2) \<sqsubseteq> ((inv Rev) b1))"
  by (metis (no_types, hide_lams) GFP.rev.exhaust UNIV_I f_inv_into_f local.below_rev.simps surj_def)

  (* Show that the ordering definition defines a correct partial order. *)
  instance
    apply intro_classes
    using below_rev.elims(3) apply fastforce
    apply (metis GFP.below_rev.elims(3) GFP.rev.inject below_trans local.below_rev.elims(2))
    by (metis GFP.below_rev.elims(2) GFP.rev.inject below_antisym)

end


lemma longchain_rev: "longChain S \<longleftrightarrow> longChain (Rev ` S)"
  apply auto
  apply(rule longchainI)
  apply (metis GFP.below_rev.elims(3) GFP.below_rev.simps GFP.rev.exhaust GFP.rev.inject imageE image_iff longChain_def)
  apply (simp add: longChain_def)
  apply(rule longchainI)
  apply (meson GFP.below_rev.simps image_iff longChain_def)
  by (simp add: longChain_def)

instantiation rev :: (division) division
begin
definition DIV_rev :: "'a rev set set" where
"DIV_rev = image (image Rev) DIV"


lemma div_rev_inv: "a\<in>DIV \<Longrightarrow> ((inv Rev)`a) \<in> DIV"
  by (smt DIV_rev_def GFP.rev.inject image_iff image_inv_f_f inj_def)

lemma div_rev: "C\<in>DIV \<Longrightarrow> (Rev ` C) \<in> DIV"
  by (simp add: DIV_rev_def)

instance
  apply intro_classes
  apply (simp add: DIV_rev_def div_non_empty)
  using GFP.div_rev_inv div_inner_non_empty by blast
end


class rev_div_cpo = division + po +

(*   assumes rev_div_non_empty: "DIV \<noteq> {}" *)

 (*  assumes rev_div_inner_non_empty: "\<And>a. a\<in>DIV  \<Longrightarrow> a \<noteq> {}" *)


    (* every set is a cpo *)
  assumes rev_div_cpo: "\<And>S a. a\<in>DIV \<Longrightarrow> \<not>finite  S \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. (Rev ` S) <<| Rev x"

begin
lemma rev_div_lub_ex: assumes "C\<in>DIV" and "longChain S" and "S\<subseteq>C" shows "\<exists>x\<in>C. (Rev ` S) <<| Rev x"
proof(cases "finite S")
  case True
  hence "finite (Rev ` S)"
    by simp
  have "longChain (Rev ` S)"
    using assms(2) longchain_rev by blast
  hence "lub (Rev ` S) \<in> (Rev `S)"
    using assms(2) lc_finite_lub True by blast
  hence "(Rev ` S) <<| lub (Rev ` S)"
    using \<open>finite (GFP.rev.Rev ` (S::'a set))\<close> \<open>longChain (GFP.rev.Rev ` (S::'a set))\<close> is_lub_lub lc_finite_lub_ex by blast 
  then show ?thesis
    using assms(3) \<open>lub (GFP.rev.Rev ` (S::'a set)) \<in> GFP.rev.Rev ` S\<close> by auto
next
  case False
  then show ?thesis
    by (simp add: assms(1) assms(2) assms(3) local.rev_div_cpo) 
qed
end


instantiation rev :: (rev_div_cpo) div_cpo
begin
lemma rev_bot_top: "x\<sqsubseteq>(Rev \<bottom>)"
  using below_rev.elims(3) by blast

lemma rev_obtains: fixes S::"'a GFP.rev set"
  obtains A where "Rev ` A = S"
  by (metis GFP.rev.exhaust UNIV_I subset_iff subset_image_iff surj_def that)

lemma rev_lub_ex: 
  fixes S::"'a rev set"
    assumes "a \<in> DIV" and "infinite S" and "longChain S"
  and "S \<subseteq> a"
shows  "\<exists>x\<in>a. S <<| x"
proof -
  obtain b where b_rev: "Rev ` b = a" and b_div:"b\<in>DIV"
    by (metis DIV_rev_def assms(1) imageE)
  from this obtain D where "longChain D" and "S = Rev ` D" and "infinite D" and "D\<subseteq>b"
    by (metis assms(2) assms(3) assms(4) finite_imageI longchain_rev subset_image_iff)
  thus ?thesis
    by (metis b_rev b_div assms(2) assms(3) rev_div_cpo rev_image_eqI)
qed

instance
  apply(intro_classes)
  apply (simp add: DIV_rev_def div_non_empty)
  by (simp add: DIV_rev_def GFP.rev_lub_ex)

  
end


lemma div_rev_adm_h:fixes C::"'a::rev_div_cpo set"
    assumes "C\<in>DIV" and "longChain Y" and "Y \<subseteq> C" and "y \<in> Y"
  shows "Rev y\<sqsubseteq>lub (Rev ` Y)"
  by (metis assms(1) assms(2) assms(3) assms(4) is_lub_def lub_eqI rev_div_lub_ex ub_imageD)


lemma div_cpo_adm_below: fixes C::"'a::rev_div_cpo set"
  shows "C\<in>DIV \<Longrightarrow> longAdm (Rev`C) (\<lambda>x. K\<sqsubseteq>x)"
  by (simp add: div_cpo_adm_less div_rev)

lemma div_cpo_adm_less: fixes C::"'a::rev_div_cpo set"
  shows "C\<in>DIV \<Longrightarrow> longAdm (Rev`C) (\<lambda>x. x\<sqsubseteq>K)"
  by (simp add: div_cpo_class.div_cpo_adm_below div_rev)

lemma rev_div_cpo_adm_below: fixes C::"'a::rev_div_cpo set"
  assumes "C\<in>DIV"
  shows "longAdm (Rev ` C) (\<lambda>a. K \<sqsubseteq> (inv Rev a))"
  apply(auto simp add: longAdm_def)
  by (metis assms below_rev.simps div_cpo_lub_least div_rev inv_rev2)

lemma rev_div_cpo_adm_less: fixes C::"'a::rev_div_cpo set"
  assumes "C\<in>DIV"
  shows "longAdm (Rev ` C) (\<lambda>a. (inv Rev a) \<sqsubseteq>K)"
  apply(auto simp add: longAdm_def)
proof -
  fix Y :: "'a rev set"
  assume a1: "\<forall>y\<in>Y. inv Rev y \<sqsubseteq> K"
  assume a2: "longChain Y"
  assume a3: "Y \<subseteq> Rev ` C"
have f4: "Y \<noteq> {} \<and> (\<forall>r ra. r \<notin> Y \<or> ra \<notin> Y \<or> r \<sqsubseteq> ra \<or> ra \<sqsubseteq> r)"
  using a2 by (simp add: longChain_def)
  have "Rev ` C \<in> DIV"
by (simp add: assms div_rev)
  then show "inv Rev (lub Y) \<sqsubseteq> K"
    using f4 a3 a2 a1 by (metis (no_types) all_not_in_conv below_rev.simps box_below div_cpo_lub_ub inv_rev2)
qed

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

lemma div_topI: assumes "\<And>x. x\<in>C \<Longrightarrow> x\<sqsubseteq>y" and "y\<in>C" and "C\<in>DIV"
  shows "y=div_top C"
  by (simp add: assms below_antisym div_top)

lemma div_top_below: "x\<in>C \<Longrightarrow> C\<in>DIV \<Longrightarrow> x\<sqsubseteq>div_top C"
  using div_top by blast

lemma div_top_in: "C\<in>DIV \<Longrightarrow> div_top C \<in>C"
  using div_top by blast


end

class rev_div_upcpo = div_upcpo + rev_div_cpo

instantiation rev :: (rev_div_upcpo) div_pcpo
begin

lemma div_top_bot:"\<And>x. x\<in>a \<Longrightarrow> a\<in>DIV \<Longrightarrow> (Rev (div_top a)) \<sqsubseteq> Rev x"
  by (simp add: div_top)

lemma div_top_rev_in: "\<And>a::'a GFP.rev set. a \<in> DIV \<Longrightarrow> (Rev (div_top ((inv Rev)`a))) \<in> a"
proof -
  fix a :: "'a GFP.rev set"
  assume a1: "a \<in> DIV"
  have f2: "\<forall>R a f. \<exists>r. ((a::'a) \<notin> f ` R \<or> (r::'a GFP.rev) \<in> R) \<and> (a \<notin> f ` R \<or> f r = a)"
    by blast
have "\<And>r. GFP.rev.Rev (inv GFP.rev.Rev r::'a) = r"
  by (metis GFP.below_rev.elims(1) f_inv_into_f range_eqI)
  then show "GFP.rev.Rev (div_top (inv GFP.rev.Rev ` a)) \<in> a"
using f2 a1 by (metis (no_types) div_rev_inv div_top)
qed

lemma div_top_rev: "\<And>a::'a GFP.rev set. a \<in> DIV \<Longrightarrow> \<forall>b::'a GFP.rev\<in>a. (Rev (div_top ((inv Rev)`a))) \<sqsubseteq> b"
  by (metis (no_types, lifting) GFP.below_rev.elims(3) div_rev_inv div_top_bot f_inv_into_f image_eqI range_eqI)

instance
  apply(intro_classes)
  using GFP.div_top_rev div_top_rev_in by blast

end





definition reverseFun::"('a::po \<Rightarrow> 'b::po) \<Rightarrow> ('a rev \<Rightarrow> 'b rev)"where
"reverseFun f = (\<lambda>a. Rev (f ((inv Rev) a)))"

lemma reversefun_below: "f x \<sqsubseteq> f y \<longleftrightarrow> (reverseFun f) (Rev y) \<sqsubseteq>  (reverseFun f) (Rev x)"
  apply auto
  apply (metis (no_types, lifting) GFP.below_rev.elims(3) GFP.rev.inject f_inv_into_f rangeI reverseFun_def)
  by (metis (full_types) GFP.below_rev.simps GFP.rev.map UNIV_I dual_order.refl eq_iff f_inv_into_f imageI order_refl reverseFun_def)

definition gfp:: "'a::rev_div_upcpo set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"gfp A f = (inv Rev) (lfp (Rev ` A) (reverseFun f))"

lemma rev_division: "C\<in>DIV \<Longrightarrow> (Rev ` C)\<in>DIV"
  by (simp add: DIV_rev_def)


lemma rev_bot2top[simp]:"C\<in>DIV \<Longrightarrow> (inv Rev (div_bot (Rev ` C))) = div_top C"
  apply(rule div_topI)
  using div_bot rev_division apply fastforce
  using div_bot rev_division apply force
  by simp


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
  shows "(gfp C f) = (f  (gfp C f)) "
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

lemma gfp_greatest_eq: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
    and "\<And>x. x\<in>C \<Longrightarrow> x \<sqsubseteq> f x \<Longrightarrow> x\<sqsubseteq>y"
    and "y \<sqsubseteq> f y"
    and "y \<in> C"
  shows "(gfp C f) = y"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) below_antisym below_refl gfp_div gfp_fix gfp_greatest)

lemma gfp_smaller: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
    and "\<And>x. x\<in>C \<Longrightarrow>f x = x \<Longrightarrow> x\<sqsubseteq>y"
  shows "(gfp C f) \<sqsubseteq> y"
  using assms(1) assms(2) assms(3) assms(4) gfp_div gfp_fix by fastforce


lemma gfp_monofun: assumes "f\<sqsubseteq>g"
    and "monofun f" and "monofun g"
    and "goodFormed C f" and "goodFormed C g"
    and "C \<in> DIV"
  shows "gfp C f \<sqsubseteq> gfp C g"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) below_fun_def gfp_div gfp_fix gfp_greatest)

lemma gfp_lfp:
  assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "(lfp C f) \<sqsubseteq> (gfp C f)"
  using assms(1) assms(2) assms(3) gfp_greatest lfp_div lfp_fix by fastforce

lemma gfp_gfp_below:
    assumes "monofun g1" 
    and "monofun g2"
    and "goodFormed C1 g1" 
    and "goodFormed C2 g2"
    and "C1 \<in> DIV" 
    and "C2 \<in> DIV"
    and "\<And>x. x\<in>C1 \<Longrightarrow>  f (g1 x)\<sqsubseteq>g2 (f x)"
    and "\<And>x. x\<in>C1 \<Longrightarrow> f x \<in>C2"
  shows "f (gfp C1 g1) \<sqsubseteq> (gfp C2 g2)"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) gfp_div gfp_fix gfp_greatest)

end