theory SetRev
  imports UnivClasses
begin

default_sort ufuncl

definition setrevFilter::  "('m \<Rightarrow> bool) \<Rightarrow> 'm set rev \<rightarrow> 'm set rev"
  where  "setrevFilter P \<equiv> \<Lambda> S. Rev (Set.filter P (inv Rev S))"


(* order is exactly reversed subset *)
lemma revBelowNeqSubset: "\<And>A:: 'a::ufuncl set rev. \<forall>B:: 'a set rev. A \<sqsubseteq> B \<longleftrightarrow> (inv Rev B \<subseteq> inv Rev A)"
  by (smt SetPcpo.less_set_def below_rev.elims(2) below_rev.elims(3) inv_rev_rev)

lemma SLEI_help1:  "\<And>Y::nat \<Rightarrow> 'a::ufuncl set rev. 
  chain Y \<Longrightarrow> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)}) \<sqsubseteq> (\<Squnion>i. Y i)" 
proof -
fix Y :: "nat \<Rightarrow> 'a set rev"
  assume a1: "chain Y"
  obtain AA :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x0 \<and> \<not> x1 \<subseteq> v2) = (AA x0 x1 \<in> x0 \<and> \<not> x1 \<subseteq> AA x0 x1)"
  by moura
  then have f2: "(\<not> inv Rev (Lub Y) \<subseteq> \<Inter>{A. \<exists>n. A = inv Rev (Y n)} \<or> 
    (\<forall>A. A \<notin> {A. \<exists>n. A = inv Rev (Y n)} \<or> inv Rev (Lub Y) \<subseteq> A)) \<and> (inv Rev (Lub Y) \<subseteq> 
    \<Inter>{A. \<exists>n. A = inv Rev (Y n)} \<or> AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) \<in> 
    {A. \<exists>n. A = inv Rev (Y n)} \<and> \<not> inv Rev (Lub Y) \<subseteq> AA {A. \<exists>n. A = inv Rev (Y n)} 
    (inv Rev (Lub Y)))"
  by (meson le_Inf_iff)
  obtain nn :: "'a set \<Rightarrow> nat" where
    f3: "((\<nexists>n. AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) = inv Rev (Y n)) \<or> 
    AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) = inv Rev (Y (nn (AA {A. \<exists>n. A = inv Rev (Y n)} 
    (inv Rev (Lub Y)))))) \<and> ((\<exists>n. AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) = inv Rev (Y n)) \<or> 
    (\<forall>n. AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) \<noteq> inv Rev (Y n)))"
    by meson
  { assume "AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) \<noteq> 
    inv Rev (Y (nn (AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)))))"
    then have "inv Rev (Lub Y) \<subseteq> \<Inter>{A. \<exists>n. A = inv Rev (Y n)}"
  using f3 f2 by auto }
  then have "inv Rev (Lub Y) \<subseteq> \<Inter>{A. \<exists>n. A = inv Rev (Y n)}"
using a1 is_ub_thelub revBelowNeqSubset by blast
  then show "Rev (\<Inter>{A. \<exists>n. A = inv Rev (Y n)}) \<sqsubseteq> (\<Squnion>n. Y n)"
    by (simp add: inv_rev_rev revBelowNeqSubset)
qed

lemma SLEI_help2:  "\<And>Y::nat \<Rightarrow> 'a::ufuncl set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
proof -
  have a0: "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow>{y} \<subseteq> (\<Inter>{x. \<exists>i. x = inv Rev (Y i)}) \<longrightarrow> (\<forall>z. (Y z) \<sqsubseteq> Rev {y})"
    by (metis (mono_tags, lifting) CollectI revBelowNeqSubset insert_subset inv_rev_rev mem_simps(11)
      rev_bot_top set_cpo_simps(3))
  have a1:  "\<And>Y::nat \<Rightarrow> 'a set rev. chain Y \<Longrightarrow> (\<forall>z. (Y z) \<sqsubseteq> Rev {y}) \<longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev {y}"
    by (simp add: lub_below)
  show  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
    by (smt CollectI below_rev.elims(3) inv_rev_rev le_Inf_iff lub_below order_refl set_cpo_simps(1))
qed

(* lub = inter *)
lemma setrevLubEqInter:  "\<And>Y::nat \<Rightarrow> 'a::ufuncl set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) = Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  using SLEI_help1 SLEI_help2 po_eq_conv by blast   

(* sometime this form is more useful *)
lemma setrevLubEqInterII: "\<And>Y::nat \<Rightarrow> 'a::ufuncl set rev. 
  chain Y \<Longrightarrow> inv Rev (\<Squnion>i. Y i) = (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  by (metis (mono_tags, lifting) Collect_cong inv_rev_rev setrevLubEqInter) 


(* setrevFilter fulfills the 2nd subgoal for contI2 *)
lemma setrevFilter_chain: "\<And>Y::nat \<Rightarrow> 'a::ufuncl set rev. chain Y \<Longrightarrow>
       chain (\<lambda>i::nat. Rev (Set.filter P (inv Rev (Y i)))) \<Longrightarrow>
       Rev (Set.filter P (inv Rev (\<Squnion>i::nat. Y i))) \<sqsubseteq> (\<Squnion>i::nat. Rev (Set.filter P (inv Rev (Y i))))"
proof - 
  fix Y::"nat \<Rightarrow> 'a::ufuncl set rev"
  assume "chain Y"
  assume "chain (\<lambda>i::nat. Rev (Set.filter P (inv Rev (Y i))))"
  have a0: "\<forall>y \<in> \<Inter>{x. \<exists>i. x = Set.filter P (inv Rev (Y i))}. P y"
    by (simp add: full_SetCompr_eq)
  have a1: "\<forall>y \<in> \<Inter>{x. \<exists>i. x = Set.filter P (inv Rev (Y i))}. (\<forall>i. y \<in> (inv Rev (Y i)))"
    by (simp add: full_SetCompr_eq)
  then have a2: "\<forall>y \<in> \<Inter>{x. \<exists>i. x = Set.filter P (inv Rev (Y i))}. y \<in> (inv Rev (\<Squnion>i::nat. Y i))"
    by (smt Inter_iff \<open>chain (Y::nat \<Rightarrow> 'a set rev)\<close> inv_rev_rev mem_Collect_eq setrevLubEqInter)
  then have a3: "Rev (Set.filter P (inv Rev (\<Squnion>i::nat. Y i))) \<sqsubseteq>
    Rev (\<Inter>{x. \<exists>i. x = Set.filter P (inv Rev (Y i))})"
    by (simp add: a0 SetPcpo.less_set_def subset_eq)
  moreover have a4: "Rev (\<Inter>{x. \<exists>i. x = inv Rev (Rev (Set.filter P (inv Rev (Y i))))}) =
    (\<Squnion>i::nat. Rev (Set.filter P (inv Rev (Y i))))"
    apply (subst setrevLubEqInter)
    apply (simp add: \<open>chain (\<lambda>i::nat. Rev (Set.filter (P::'a \<Rightarrow> bool)
      (inv Rev ((Y::nat \<Rightarrow> 'a set rev) i))))\<close>)
    by auto
  moreover have a5: "Rev (\<Inter>{x. \<exists>i. x = inv Rev (Rev (Set.filter P (inv Rev (Y i))))}) = 
    Rev (\<Inter>{x. \<exists>i. x = Set.filter P (inv Rev (Y i))})"
    by (metis Collect_cong inv_rev_rev)
  ultimately show "Rev (Set.filter P (inv Rev (\<Squnion>i::nat. Y i))) \<sqsubseteq> 
    (\<Squnion>i::nat. Rev (Set.filter P (inv Rev (Y i))))"
    by presburger
qed


end