theory SetRev
  imports "inc/SetPcpo"
begin

default_sort type

definition setrevFilter::  "('m \<Rightarrow> bool) \<Rightarrow> 'm set rev \<rightarrow> 'm set rev"
  where  "setrevFilter P \<equiv> \<Lambda> S. Rev (Set.filter P (inv Rev S))"
    
definition setify::"('m \<Rightarrow> ('n set rev)) \<rightarrow> ('m \<Rightarrow> 'n) set rev" where
"setify \<equiv> \<Lambda> f. Rev {g. \<forall>m. g m \<in> (inv Rev(f m))}"

(* order is exactly reversed subset *)
lemma revBelowNeqSubset: "\<And>A:: 'a set rev. \<forall>B:: 'a set rev. A \<sqsubseteq> B \<longleftrightarrow> (inv Rev B \<subseteq> inv Rev A)"
  by (smt SetPcpo.less_set_def below_rev.elims(2) below_rev.elims(3) inv_rev_rev)

lemma SLEI_help1:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
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
    by (metis (no_types, lifting) a1 f2 is_ub_thelub revBelowNeqSubset)
  then show "Rev (\<Inter>{A. \<exists>n. A = inv Rev (Y n)}) \<sqsubseteq> (\<Squnion>n. Y n)"
    by (simp add: inv_rev_rev revBelowNeqSubset)
qed

lemma SLEI_help2:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  by (metis (mono_tags, lifting) Inter_lower inv_rev_rev lub_below mem_Collect_eq revBelowNeqSubset)

(* lub = inter *)
lemma setrevLubEqInter:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) = Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  using SLEI_help1 SLEI_help2 po_eq_conv by blast   

(* sometimes this form is more useful *)

lemma setrevLubEqInterII: "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> inv Rev (\<Squnion>i. Y i) = (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  by (metis (mono_tags, lifting) inv_rev_rev setrevLubEqInter) 


(* setrevFilter fulfills the 2nd subgoal for contI2 *)
lemma setrevFilter_chain: "\<And>Y::nat \<Rightarrow> 'a set rev. chain Y \<Longrightarrow>
       chain (\<lambda>i::nat. Rev (Set.filter P (inv Rev (Y i)))) \<Longrightarrow>
       Rev (Set.filter P (inv Rev (\<Squnion>i::nat. Y i))) \<sqsubseteq> (\<Squnion>i::nat. Rev (Set.filter P (inv Rev (Y i))))"
proof - 
  fix Y::"nat \<Rightarrow> 'a set rev"
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
    by (metis inv_rev_rev)
  ultimately show "Rev (Set.filter P (inv Rev (\<Squnion>i::nat. Y i))) \<sqsubseteq> 
    (\<Squnion>i::nat. Rev (Set.filter P (inv Rev (Y i))))"
    by presburger
qed

lemma setrevfilter_mono: "monofun (\<lambda> S::'a set rev. Rev (Set.filter P (inv Rev S)))"
  apply (rule monofunI)
  by (metis (full_types) SetPcpo.less_set_def below_rev.elims(2) below_rev.simps inv_rev_rev 
    member_filter subset_iff)

lemma setrevfilter_cont[simp]:  "cont (\<lambda> S::'a set rev. Rev (Set.filter P (inv Rev S)))"
  apply (rule Cont.contI2)
  apply (simp add: setrevfilter_mono)
  by (simp add: setrevFilter_chain)

(*setify*)
    

lemma setify_mono[simp]:"monofun (\<lambda>f. Rev {g. \<forall>m. g m \<in> (inv Rev(f m))})"
proof(rule rev_monoI)
  fix f y::"'a \<Rightarrow> 'b set rev"
  assume a1:"f\<sqsubseteq>y"
  show "{g::'a \<Rightarrow> 'b. \<forall>m::'a. g m \<in> inv Rev (y m)} \<sqsubseteq> {g::'a \<Rightarrow> 'b. \<forall>m::'a. g m \<in> inv Rev (f m)}"
    by (smt Collect_mono SetPcpo.less_set_def a1 below_rev.elims(2) contra_subsetD fun_below_iff inv_rev_rev)
qed

lemma setify_cont[simp]:"cont (\<lambda>f. Rev {g. \<forall>m. g m \<in> (inv Rev(f m))})"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> 'a \<Rightarrow> 'b set rev"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Rev {g::'a \<Rightarrow> 'b. \<forall>m::'a. g m \<in> inv Rev (Y i m)})"
  have a3:"\<forall>m. chain (\<lambda>i. Y i m)"
    by (simp add: a1 ch2ch_fun)
  then have "\<forall>m.((\<Squnion>i::nat. Y i) m) = (\<Squnion>i::nat. Y i m)"
    by (simp add: a1 lub_fun)
  then show "Rev {g::'a \<Rightarrow> 'b. \<forall>m::'a. g m \<in> inv Rev ((\<Squnion>i::nat. Y i) m)} \<sqsubseteq> (\<Squnion>i::nat. Rev {g::'a \<Rightarrow> 'b. \<forall>m::'a. g m \<in> inv Rev (Y i m)})"
    by(simp add: setrevLubEqInter a2 setrevLubEqInterII a1 a3 lub_fun inv_rev_rev less_set_def,auto)
qed

lemma setify_insert:"setify\<cdot>f = Rev {g. \<forall>m. g m \<in> (inv Rev(f m))}"
  by(simp add: setify_def)
  
  
lemma setify_empty:"f m = Rev {} \<Longrightarrow> setify\<cdot>f = Rev {}"
  apply(simp add: setify_def)
  by (metis empty_iff inv_rev_rev)
    
lemma setify_notempty:assumes "\<forall>m. f m \<noteq> Rev {}" shows" setify\<cdot>f \<noteq> Rev {}"
proof(simp add: setify_def)
  have "\<forall>m. \<exists>x. x\<in>(inv Rev (f m))"
    by (metis all_not_in_conv assms inv_rev_rev rev.exhaust)
  have "\<forall>m. (\<lambda>e. SOME x. x\<in> inv Rev (f e)) m \<in> inv Rev (f m)"
    by (metis assms inv_rev_rev rev.exhaust some_in_eq)
  then show "\<exists>x::'a \<Rightarrow> 'b. \<forall>m::'a. x m \<in> inv Rev (f m)"
    by(rule_tac x="(\<lambda>e. SOME x. x\<in> inv Rev (f e))" in exI, auto)
qed
  
lemma setify_notempty_ex:"setify\<cdot> f \<noteq> Rev {} \<Longrightarrow> \<exists>g.(\<forall>m. g m \<in> inv Rev (f m))"
  by(simp add: setify_def)
  
lemma setify_final:assumes "\<forall>m. f m \<noteq> Rev {}" and "x \<in> inv Rev (f m)" shows"\<exists>g\<in>(inv Rev (setify\<cdot>f)). g m = x"
proof(simp add: setify_def inv_rev_rev)
  have "\<exists>g.(\<forall>m. g m \<in> inv Rev (f m))"
    by(simp add: setify_notempty setify_notempty_ex assms(1))
  then obtain g where g_def:"(\<forall>m. g m \<in> inv Rev (f m))"
    by auto
  have g2_def:"\<forall>n. (\<lambda>e. if e = m then x else g e) n \<in> inv Rev (f n)"
    by (simp add: assms(2) g_def)
  then show "\<exists>g::'a \<Rightarrow> 'b. (\<forall>m::'a. g m \<in> inv Rev (f m)) \<and> g m = x"     
    by(rule_tac x="(\<lambda>e. if e = m then x else g e)" in exI, auto) 
qed

  
end