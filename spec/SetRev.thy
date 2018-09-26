theory SetRev
  imports inc.SetPcpo inc.Reversed
begin

default_sort type


  section \<open>Instantiation\<close>

instance set :: (type) revcpo
proof(intro_classes)
  fix S:: "nat \<Rightarrow> 'a set"
  assume "chain (\<lambda>i::nat. Rev (S i))"
  have rev_below:"\<And>a b:: 'a set . Rev a \<sqsubseteq> Rev b \<longleftrightarrow> b \<subseteq> a"
    by (simp add: SetPcpo.less_set_def)
  hence "range (\<lambda>i::nat. Rev (S i)) <<| Rev (\<Inter> range S)" 
    apply(auto simp add: is_lub_def is_ub_def)
    by (metis below_rev.elims(2) le_INF_iff rev_below)
  thus "\<exists>x::'a set. range (\<lambda>i::nat. Rev (S i)) <<| Rev x"
    by blast
qed

instance set :: (type) uprevcpo
  apply(intro_classes)
  by (meson UNIV_I Union_is_lub is_lub_def is_ub_def)




(* TODO Wohin damit *)
lemma easy_cont: assumes "(\<lambda>x y. (f x y)) = (\<lambda>x y. (f y x))"
                     and "\<And>y. cont (\<lambda>x. (f x y))"
                   shows "\<And>x. cont (\<lambda>y. (f x y))"
  proof -
    fix x
    have h1: "\<And>x y. (f x y) = (f y x)"
      by (meson assms(1))
    show "cont (\<lambda>y. (f x y))"
      apply(simp add: h1)
      by (simp add: assms(2))
  qed

section \<open>Definitions\<close>

definition setrevFilter::  "('m \<Rightarrow> bool) \<Rightarrow> 'm set rev \<rightarrow> 'm set rev"
  where  "setrevFilter P \<equiv> \<Lambda> S. Rev (Set.filter P (inv Rev S))"

definition setrevInter:: "'m set rev \<rightarrow> 'm set rev \<rightarrow> 'm set rev" where
"setrevInter \<equiv> \<Lambda> S1 S2. Rev (inv Rev S1 \<inter> inv Rev S2)"

definition setify::"('m \<Rightarrow> ('n set rev)) \<rightarrow> ('m \<Rightarrow> 'n) set rev" where
"setify \<equiv> \<Lambda> f. Rev {g. \<forall>m. g m \<in> (inv Rev(f m))}"

definition invsetify::"('m \<Rightarrow> 'n) set rev \<rightarrow> ('m \<Rightarrow> 'n set rev)" where
"invsetify \<equiv> \<Lambda> f. (\<lambda>m. Rev {g m |g.  g\<in> (inv Rev f)})"

definition setrevUnion:: "'m set rev \<rightarrow> 'm set rev \<rightarrow> 'm set rev" where
"setrevUnion \<equiv> (\<Lambda> A B. Rev((inv Rev A) \<union> (inv Rev B)))"

definition setrevImage:: "('m \<Rightarrow> 'n) \<Rightarrow> 'm set rev \<Rightarrow> 'n set rev" where
"setrevImage f \<equiv> \<lambda> S.  Rev (f ` (inv Rev S))"

definition setrevForall:: "('m \<Rightarrow> bool) \<Rightarrow> 'm set rev \<Rightarrow> bool" where
"setrevForall P S \<equiv> \<forall>x\<in> (inv Rev S). P x"

definition setrevExists:: "('m \<Rightarrow> bool) \<Rightarrow> 'm set rev \<Rightarrow> bool" where
"setrevExists P S \<equiv> \<exists>x\<in> (inv Rev S). P x"

definition setrevSize :: "'a set rev \<Rightarrow> lnat" where
 "setrevSize X = setSize (inv Rev X)"

section \<open>Lemmas\<close>

subsection \<open>General\<close>

lemma setrev_eqI: "inv Rev a = inv Rev b \<Longrightarrow> a = b"
  by (metis rev_inv_rev)

lemma setrev_eqI2: "inv Rev a \<subseteq> inv Rev b \<Longrightarrow> inv Rev b \<subseteq> inv Rev a \<Longrightarrow> a = b"
  by (simp add: setrev_eqI)

(* order is exactly reversed subset *)
lemma revBelowNeqSubset: "\<And>A:: 'a set rev. \<forall>B:: 'a set rev. A \<sqsubseteq> B \<longleftrightarrow> (inv Rev B \<subseteq> inv Rev A)"
  by (metis SetPcpo.less_set_def below_rev.simps inv_rev_rev rev.exhaust)

lemma setrev_belowI: "inv Rev a \<subseteq> inv Rev b \<Longrightarrow> b \<sqsubseteq> a"
  by (simp add: revBelowNeqSubset)

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

lemma SLEI_help3:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) = Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  using SLEI_help1 SLEI_help2 po_eq_conv by blast 


(* lub = inter *)
lemma setrevLubEqInter: "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) = Rev (\<Inter>{inv Rev (Y i) | i . True})"
  by (simp add: SLEI_help3)

(* sometimes this form is more useful *)
lemma setrevLubEqInterII: "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> inv Rev (\<Squnion>i. Y i) = (\<Inter>{inv Rev (Y i) | i . True})"
  by (metis (mono_tags, lifting) inv_rev_rev setrevLubEqInter) 

lemma setrevLub_lub_eq_all:
  assumes "chain (Y:: nat \<Rightarrow> 'a set rev)"
    shows "\<And>x. (x \<in> inv Rev (Lub Y) \<longleftrightarrow> (\<forall>i. x \<in> inv Rev (Y i)))"
  apply(simp only: setrevLubEqInter assms)
  apply(simp only: inv_rev_rev)
  by auto


lemma setrev_lub_emptyI: assumes "chain Y" and "\<And> x. \<exists> i. x \<notin> inv Rev (Y i)"
  shows "Lub Y = Rev {}"
  by (metis all_not_in_conv assms(1) assms(2) inv_rev_rev rev.exhaust setrevLub_lub_eq_all)

lemma setrev_lub_emptyD: assumes "chain Y" and "Lub Y = Rev {}"
  shows "\<And> x. \<exists> i. x \<notin> inv Rev (Y i)"
  by (metis assms(1) assms(2) emptyE inv_rev_rev setrevLub_lub_eq_all)

text {* The least upper bound on sets corresponds to the @{text "Intersection"} operator. *}
lemma setrev_inter_lub: "A <<| Rev (\<Inter> ((inv Rev) ` A))"
apply (simp add: is_lub_def)
apply (simp add: is_ub_def)
  by (simp add: INF_greatest INF_lower inv_rev_rev revBelowNeqSubset)

text {* Another needed variant of the fact that lub on sets corresponds to intersection. *}
lemma setrev_lub_eq_inter: "lub = (\<lambda>A. Rev (\<Inter> ((inv Rev) ` A)))"
apply (rule ext)
apply (rule lub_eqI [OF setrev_inter_lub])
done



subsection \<open>setrevFilter\<close>

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
    by (simp add: \<open>chain (Y::nat \<Rightarrow> 'a set rev)\<close> setrevLub_lub_eq_all)
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

lemma setrevfilter_condition: "\<And>x. x \<in> (inv Rev (setrevFilter P\<cdot>A)) \<Longrightarrow> P x"
  by (simp add: inv_rev_rev setrevFilter_def)

lemma setrevfilter_included: "\<And>x. x \<in> (inv Rev (setrevFilter P\<cdot>A)) \<Longrightarrow> x \<in> inv Rev A"
  by (simp add: inv_rev_rev setrevFilter_def)

lemma setrevfilter_reversed: "\<And>x. P x \<and> x \<in> inv Rev A \<Longrightarrow> x \<in> (inv Rev (setrevFilter P\<cdot>A))"
  apply(simp add: setrevFilter_def)
  by(simp add: Set.filter_def inv_rev_rev)

lemma setrevFilter_gdw: "\<And>x. x \<in> (inv Rev (setrevFilter P\<cdot>A)) \<longleftrightarrow> P x \<and> x \<in> inv Rev A"
  by (meson setrevfilter_condition setrevfilter_included setrevfilter_reversed)

lemma setrevfilter_insert: "setrevFilter P\<cdot>S = Rev (Set.filter P (inv Rev S))"
  by (simp add: setrevFilter_def)

(*inter*)

lemma sr_inter_as_filter1: "(\<lambda> S1. Rev (inv Rev S1 \<inter> inv Rev S2)) =
  (\<lambda> S1. Rev (Set.filter (\<lambda>a. a \<in> inv Rev S2) (inv Rev S1)))"
  by (metis (no_types) Int_def Set.filter_def inf_commute)

lemma sr_inter_as_filter2: "(\<lambda> S2. Rev (inv Rev S1 \<inter> inv Rev S2)) =
  (\<lambda> S2. Rev (Set.filter (\<lambda>a. a \<in> inv Rev S1) (inv Rev S2)))"
  by (metis (no_types) Int_def Set.filter_def inf_commute)

lemma sr_UIC_arg1: "cont (\<lambda> S1. Rev (inv Rev S1 \<inter> inv Rev S2))"
  by (simp add: sr_inter_as_filter1)

lemma setrevInter_cont1[simp]: "cont (\<lambda> S2. Rev (inv Rev S1 \<inter> inv Rev S2))"
  by (simp add: sr_inter_as_filter2)

lemma setrevInter_cont2[simp]: "cont (\<lambda> S1. \<Lambda> S2. Rev (inv Rev S1 \<inter> inv Rev S2))"
  apply (rule cont2cont_LAM)
  apply simp
  by (simp add: sr_UIC_arg1)

lemma setrevinter_insert: "setrevInter\<cdot>S1\<cdot>S2 = Rev (inv Rev S1 \<inter> inv Rev S2)"
  by (simp add: setrevInter_def)

lemma setrevInter_sym: "(\<lambda>A B. Rev((inv Rev A) \<inter> (inv Rev B))) =
                        (\<lambda>A B. Rev((inv Rev B) \<inter> (inv Rev A)))"
  by (simp add: inf_commute)

lemma setrevInter_sym2: "\<And>A B. setrevInter\<cdot>A\<cdot>B = setrevInter\<cdot>B\<cdot>A"
  proof -
    fix A :: "'a set rev" and B :: "'a set rev"
    have "\<And>r. (\<Lambda> ra. Rev ((inv Rev r::'a set) \<inter> inv Rev ra)) = setrevInter\<cdot>r"
      by (simp add: setrevInter_def)
    then show "setrevInter\<cdot>A\<cdot>B = setrevInter\<cdot>B\<cdot>A"
      by (metis (no_types) beta_cfun setrevInter_cont1 setrevInter_sym)
  qed

lemma setrevInter_gdw: "\<And>A B x. x \<in> inv Rev (setrevInter\<cdot>A\<cdot>B) \<longleftrightarrow> (x \<in> inv Rev A \<and> x \<in> inv Rev B)"
  by (metis IntD1 IntD2 IntI inv_rev_rev setrevinter_insert)

subsection \<open>setify\<close>

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
 
lemma invsetify_mono[simp]:"monofun (\<lambda> f. (\<lambda>m. Rev {g m |g.  g\<in> (inv Rev f)}))"
proof(rule monofunI)
  fix x y::"('a \<Rightarrow> 'b) set rev"
  assume a1:"x\<sqsubseteq>y"
  show "(\<lambda>m. Rev {g m |g. g \<in> inv Rev x}) \<sqsubseteq> (\<lambda>m. Rev {g m |g. g \<in> inv Rev y})"
    apply(simp add: below_fun_def)
    by (smt Collect_mono SetPcpo.less_set_def a1 revBelowNeqSubset subsetCE)
qed
(*
lemma invsetify_cont[simp]:"cont(\<lambda> f. (\<lambda>m. Rev {g m |g.  g\<in> (inv Rev f)}))"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> ('a \<Rightarrow> 'b) set rev"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>(i::nat) m::'a. Rev {g m |g::'a \<Rightarrow> 'b. g \<in> inv Rev (Y i)})"
  show "(\<lambda>m::'a. Rev {g m |g::'a \<Rightarrow> 'b. g \<in> inv Rev (\<Squnion>i::nat. Y i)}) \<sqsubseteq> (\<Squnion>i::nat. (\<lambda>m::'a. Rev {g m |g::'a \<Rightarrow> 'b. g \<in> inv Rev (Y i)}))"
  proof(simp add:lub_fun a2  below_fun_def, auto)
    fix x::'a
    show"Rev {g x |g. g \<in> inv Rev (Lub Y)} \<sqsubseteq> (\<Squnion>i::nat. Rev {g x |g. g \<in> inv Rev (Y i)})"
      apply(subst setrevLubEqInterII, simp add: a1)
      apply(subst setrevLubEqInter)
      apply (smt Collect_mono a1 inv_rev_rev po_class.chain_def revBelowNeqSubset subsetCE)
      apply(simp add: less_set_def inv_rev_rev, auto)
        sorry
qed*)
  
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


subsection \<open>setrevUnion\<close>

lemma setrevUnion_sym: "(\<lambda>A B. Rev((inv Rev A) \<union> (inv Rev B))) =
                        (\<lambda>A B. Rev((inv Rev B) \<union> (inv Rev A)))"
  by (simp add: sup_commute)

lemma setrevUnion_chain: assumes "chain Y"
                        shows "\<And>A. chain (\<lambda>i. Rev (inv Rev A \<union> inv Rev (Y i)))"
  apply(rule chainI)
  apply(simp add: less_set_def)
  by (metis SetPcpo.less_set_def assms below_rev.simps le_supI2 po_class.chainE rev_inv_rev)

lemma setrevUnion_mono[simp]: "\<And>A. monofun (\<lambda>x. Rev((inv Rev A) \<union> (inv Rev x)))"
  apply(rule monofunI)
  by (metis SetPcpo.less_set_def Un_mono below_rev.simps order_refl revBelowNeqSubset)

lemma setrevUnion_cont1[simp]: "cont (\<lambda>x. Rev((inv Rev A) \<union> (inv Rev x)))"
  apply(rule Cont.contI2)
  apply simp
  apply(simp add: setrevUnion_chain)
  proof -
    fix A::"'a set rev" and Y::"nat \<Rightarrow> 'a set rev"
    assume a1: "chain Y"
    have h1: "\<And>x. x \<in> \<Inter>{x::'a set. \<exists>i::nat. x = inv Rev (Rev (inv Rev A \<union> inv Rev (Y i)))} 
               \<Longrightarrow> x \<in> inv Rev A \<union> inv Rev (Lub Y)"
      proof -
        fix x
        assume a11: "x \<in> \<Inter>{x::'a set. \<exists>i::nat. x = inv Rev (Rev (inv Rev A \<union> inv Rev (Y i)))}"
        have g1: "\<And>i. x \<in> inv Rev (Rev (inv Rev A \<union> inv Rev (Y i)))"
          using a11 by fastforce
        have g2: "\<And>i. x \<in>  (inv Rev A \<union> inv Rev (Y i))"
          by (metis g1 inv_rev_rev)
        then show "x \<in> inv Rev A \<union> inv Rev (Lub Y)"
          proof (cases "x \<in> inv Rev A")
            case True
            then show ?thesis
              by simp
          next
            case f: False
            have f1: "\<forall>i. x \<in> inv Rev (Y i)"
              using f g2 by auto
            show ?thesis
              using a1 f1 setrevLubEqInterII by auto
          qed
      qed
    show "Rev (inv Rev A \<union> inv Rev (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. Rev (inv Rev A \<union> inv Rev (Y i)))"
      apply(simp add: setrevLubEqInter setrevUnion_chain a1 inv_rev_rev less_set_def)
      by auto
  qed

lemma setrevUnion_cont2[simp]: "cont (\<lambda>A. \<Lambda> B. Rev((inv Rev A) \<union> (inv Rev B)))"
  apply(rule cont2cont_LAM)
  apply simp
  apply(rule easy_cont)
  apply(simp only: setrevUnion_sym)
  by simp

lemma setrevUnion_sym2: "\<And>A B. setrevUnion\<cdot>A\<cdot>B = setrevUnion\<cdot>B\<cdot>A"
  proof -
    fix A :: "'a set rev" and B :: "'a set rev"
    have "\<And>r. (\<Lambda> ra. Rev ((inv Rev r::'a set) \<union> inv Rev ra)) = setrevUnion\<cdot>r"
      by (simp add: setrevUnion_def)
    then show "setrevUnion\<cdot>A\<cdot>B = setrevUnion\<cdot>B\<cdot>A"
      by (metis (no_types) beta_cfun setrevUnion_cont1 setrevUnion_sym)
  qed

lemma setrevUnion_gdw: "\<And>A B x. x \<in> inv Rev (setrevUnion\<cdot>A\<cdot>B) \<longleftrightarrow> (x \<in> inv Rev A \<or> x \<in> inv Rev B)"
  by (simp add: inv_rev_rev setrevUnion_def)


subsection \<open>setrevImage\<close>
lemma image_mono_rev:  "monofun (setrevImage f)"
  apply (rule monofunI)
  by (simp add: image_mono inv_rev_rev revBelowNeqSubset setrevImage_def)

lemma image_cont_rev: assumes "inj f" 
  shows "cont (setrevImage f)"
  apply (rule Cont.contI2)
   apply (simp add: image_mono_rev)
  unfolding setrevImage_def
proof -
  fix Y::"nat \<Rightarrow> 'a set rev"
  assume a1: "chain Y"
  have f0: "chain (\<lambda>i::nat. Rev (f ` inv Rev (Y i)))"
    apply (rule chainI)
    by (metis Set.image_mono SetPcpo.less_set_def a1 below_rev.simps po_class.chainE revBelowNeqSubset)
  have f1: "(\<Squnion>i::nat. Rev (f ` inv Rev (Y i))) =  Rev (\<Inter>{x. \<exists>i. x = f ` inv Rev (Y i)})"
    apply (simp add: f0 setrevLubEqInter)
    by (simp add: inv_rev_rev)
  have f2: "\<And>i. \<forall> a \<in> inv Rev (Lub Y). a \<in> inv Rev (Y i)"
    by (metis (mono_tags, hide_lams) a1 below_rev.simps contra_subsetD is_ub_thelub rev_inv_rev set_cpo_simps(1))
  have f3: "\<And>i. \<forall> a \<in> inv Rev (Lub Y). f a \<in> f ` inv Rev (Y i)"
    by (simp add: f2)
  have f4: "\<forall> b \<in> \<Inter>{x::'b set. \<exists>i::nat. x = f ` inv Rev (Y i)}. (\<forall> i. b \<in> f ` inv Rev (Y i))"
    by blast

  have f5: "\<forall> b \<in> \<Inter>{x::'b set. \<exists>i::nat. x = f ` inv Rev (Y i)}. \<forall> x y. f x = b \<and> f y = b \<longrightarrow> x = y"
    by (metis UNIV_I assms inv_into_f_f)
  have f6: "\<And>x::'b. x \<in> \<Inter>{x::'b set. \<exists>i::nat. x = f ` inv Rev (Y i)} \<Longrightarrow> x \<in> f ` \<Inter>{x::'a set. \<exists>i::nat. x = inv Rev (Y i)}"
  proof -
    fix x :: 'b
    assume a1: "x \<in> \<Inter>{x. \<exists>i. x = f ` inv Rev (Y i)}"
    obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
      f2: "\<forall>b f A. aa A f b \<in> A \<and> f (aa A f b) = b \<or> b \<notin> f ` A"
      by (metis f_inv_into_f inv_into_into)
    have f4: "\<forall>n. x \<in> f ` inv Rev (Y n)"
      using a1 by blast
    then have bla: "\<forall>n. f (aa (inv Rev (Y n)) f x) = x"
      using f2 by meson
    then obtain aaa :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
      f5: "f (aaa f x) = x"
      by blast
    show "x \<in> f ` \<Inter>{A. \<exists>n. A = inv Rev (Y n)}"
      by (smt Inter_iff bla assms f2 f4 f5 image_iff injD mem_Collect_eq rangeI)
  qed
  show "Rev (f ` inv Rev (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. Rev (f ` inv Rev (Y i)))"
    apply (subst f1)
    apply (simp add: a1 setrevLubEqInterII)
    by (metis (no_types, lifting) SetPcpo.less_set_def f6 subsetI)
qed 

lemma setrevimage_inj_inj:
  assumes "inj f"
  shows "inj (setrevImage f)"
  unfolding setrevImage_def
  by (metis (no_types, lifting) assms injI inj_image_eq_iff rev.inject setrev_eqI)

lemma setrevimage_mono_obtain: assumes "f \<sqsubseteq> g" and "a\<in>((inv Rev) (setrevImage f S))"
  obtains b where "b\<in>((inv Rev) (setrevImage g S))" and "a\<sqsubseteq>b"
proof -
  obtain s where s_in: "s\<in> (inv Rev)S" and s_a: "f s = a"
    by (metis assms(2) image_iff inv_rev_rev setrevImage_def)
  have "g s \<in> ((inv Rev) (setrevImage g S))"
    by (simp add: s_in inv_rev_rev setrevImage_def)
  thus ?thesis
    using assms(1) fun_belowD s_a that by fastforce
qed

lemma setrevimage_mono_obtain2: assumes "f \<sqsubseteq> g" and "a\<in>((inv Rev) (setrevImage g S))"
  obtains b where "b\<in>((inv Rev) (setrevImage f S))" and "b\<sqsubseteq>a"
proof -
  obtain s where s_in: "s\<in> (inv Rev)S" and s_a: "g s = a"
    by (metis assms(2) image_iff inv_rev_rev setrevImage_def)
  have "f s \<in> ((inv Rev) (setrevImage f S))"
    by (simp add: s_in inv_rev_rev setrevImage_def)
  thus ?thesis
    using assms(1) fun_belowD s_a that by fastforce
qed

lemma setrevimage_mono_obtain3: assumes "a\<in>((inv Rev) (setrevImage g S))"
  obtains b where "b\<in>((inv Rev) S)" and "a = g b"
  by (metis assms image_iff inv_rev_rev setrevImage_def)

lemma setrevimage_image: "setrevImage f (setrevImage g S) = setrevImage (\<lambda> h. f (g h)) S"
  by (simp add: image_image inv_rev_rev setrevImage_def)

lemma setreImage_lub_inj_on: assumes"chain Y" and "\<forall>i. inj_on f (inv Rev (Y i))" 
  shows "setrevImage f (\<Squnion>i. Y i) = (\<Squnion>i. setrevImage f (Y i))" (*main lemma for cont proof spsStep*)
proof (cases "(\<Squnion>i. Y i) = Rev {}")
  case True
  have "(\<Squnion>i::nat. Rev (f ` inv Rev (Y i))) = Rev (f ` {})"
    apply simp
    apply (rule setrev_lub_emptyI)
     apply (metis (mono_tags, lifting) assms(1) image_mono inv_rev_rev po_class.chainI po_class.chain_def revBelowNeqSubset)
    apply (simp add: inv_rev_rev)
    apply (case_tac "x \<notin> f ` inv Rev (Y 0)")
     apply auto[1]
    apply simp
  proof - 
    fix y::'b
    assume a1: " y \<in> f ` inv Rev (Y (0::nat))"
    obtain x where y_def_1: "y = f x "  and y_def_2: "x \<in> inv Rev (Y (0::nat))"
      using a1 by blast
    obtain da_i where "x \<notin> inv Rev (Y da_i)"
      by (meson True assms(1) setrev_lub_emptyD)
    have "y \<notin> f ` inv Rev (Y da_i)"
    proof (rule ccontr, simp)
      assume a2: "y \<in> f ` inv Rev (Y da_i)"
      then obtain da_x where "y =  f da_x" and "da_x \<in> inv Rev (Y da_i)"
        by blast
      have "Y 0 \<sqsubseteq> Y da_i"
        by (simp add: assms(1) po_class.chain_mono)
      then have "\<And>x. x \<in> inv Rev (Y da_i) \<Longrightarrow> x \<in> inv Rev (Y 0)"
        by (meson revBelowNeqSubset subsetCE)
      then have "da_x \<in> inv Rev (Y 0)"
        using \<open>(da_x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by auto
      then have "x = da_x"
        using \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (da_x::'a)\<close> assms(2) inj_onD y_def_1 y_def_2 by fastforce
      show "False"
        using \<open>(da_x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> \<open>(x::'a) = (da_x::'a)\<close> \<open>(x::'a) \<notin> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by auto
    qed
    then show "\<exists>i::nat. y \<notin> f ` inv Rev (Y i)"
      by blast
  qed
  then show ?thesis 
    apply (simp add: setrevImage_def)
    by (simp add: True inv_rev_rev)
next
  case False
  have f1: "(\<Squnion>i::nat. Rev (f ` inv Rev (Y i))) = 
    Rev (\<Inter>{uu::'b set. \<exists>i::nat. uu = f ` inv Rev (Y i)})"
    apply (subst setrevLubEqInter)
     apply (metis (mono_tags, lifting) assms(1) image_mono inv_rev_rev po_class.chain_def revBelowNeqSubset)
    by (simp add: inv_rev_rev)
  show ?thesis
    apply (simp add: setrevImage_def)
    apply (subst po_eq_conv, rule)
     apply (simp add: f1) defer
     apply (simp add: f1) 
    apply (simp_all add: less_set_def)
    using assms(1) setrevLub_lub_eq_all apply fastforce
  proof 
    fix y::'b 
    assume a11: "y \<in> \<Inter>{uu::'b set. \<exists>i::nat. uu = f ` inv Rev (Y i)}"
    then have "\<And>i. y \<in> f ` inv Rev (Y i)"
      by blast
    then have " y \<in> f ` inv Rev (Y 0)"
      by simp
    then obtain x where "y = f x" and "x \<in> inv Rev (Y 0)"
      by blast
    have "\<forall> i. x \<in> inv Rev (Y i)"
    proof (rule ccontr, simp)
      assume a111: "\<exists>i::nat. x \<notin> inv Rev (Y i) "
      obtain da_i where "x \<notin> inv Rev (Y da_i)"
        using a111 by auto
      have "y \<in> f ` inv Rev (Y da_i)"
        by (simp add: \<open>\<And>i::nat. (y::'b) \<in> (f::'a \<Rightarrow> 'b) ` inv Rev ((Y::nat \<Rightarrow> 'a set rev) i)\<close>)
      obtain da_x where "y = f da_x" and "da_x \<in> inv Rev (Y da_i)"
        using \<open>(y::'b) \<in> (f::'a \<Rightarrow> 'b) ` inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by blast
      then have "da_x \<in> inv Rev (Y 0)"
        by (meson assms(1) contra_subsetD po_class.chain_mono revBelowNeqSubset zero_le)
      then have "x = da_x"
        using \<open>(x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (0::nat))\<close> \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (da_x::'a)\<close> \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (x::'a)\<close> assms(2) inj_on_eq_iff by fastforce
      show False
        using \<open>(da_x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> \<open>(x::'a) = (da_x::'a)\<close> \<open>(x::'a) \<notin> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by auto
    qed
    show "y \<in> f ` inv Rev (Lub Y)"
      by (simp add: \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (x::'a)\<close> 
          \<open>\<forall>i::nat. (x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) i)\<close> assms(1) setrevLub_lub_eq_all)
  qed
qed

lemma setrevimage_empty: assumes "H = Rev {}"
  shows " setrevImage f H = Rev {}"
  apply (simp add: setrevImage_def)
  by (simp add: assms inv_rev_rev)
                                                    
lemma setrevimage_not_empty: assumes "f \<in> inv Rev (setrevImage g H)"
  shows "H \<noteq>  Rev {}"
  by (metis assms ex_in_conv inv_rev_rev setrevimage_empty)

section \<open>set flat rev\<close>
(* ToDo: Copy to SetPcpo *)

subsection \<open>set flat rev def N lemmas\<close>
definition setflat_rev :: "'a set set rev \<rightarrow> 'a set rev" where
"setflat_rev = (\<Lambda> S. Rev {K  | Z K. K\<in>Z \<and> Z \<in> (inv Rev S)} )"

lemma setflat_rev_mono: "monofun (\<lambda>S. Rev {K  | Z K. K\<in>Z \<and> Z \<in> (inv Rev S)} )"
  apply(rule monofunI)
  apply auto
  apply (simp add: less_set_def)
  using revBelowNeqSubset by fastforce

(*
lemma setflat_rev_cont: "cont (\<lambda>S. Rev {K  | Z K. K\<in>Z \<and> Z \<in> (inv Rev S)} )"
    apply (rule contI2)
  using setflat_rev_mono apply blast
proof -
  fix Y:: "nat \<Rightarrow> 'a set set rev"
  assume a1: "chain Y"
  have "\<And>i. Y i \<sqsubseteq> Lub Y"
    by (simp add: a1 is_ub_thelub)

  have f0: "\<And>i. inv Rev (Y (Suc i)) \<subseteq> inv Rev (Y i)"
    by (meson a1 po_class.chainE revBelowNeqSubset)
  have f1: "inv Rev (Rev {uu::'a. \<exists>(Z::'a set) K::'a. uu = K \<and> K \<in> Z \<and> Z \<in> inv Rev (Lub Y)}) = 
              {uu::'a. \<exists>(Z::'a set) K::'a. uu = K \<and> K \<in> Z \<and> Z \<in> inv Rev (Lub Y)}"
    by (simp add: inv_rev_rev)
  have f2: "chain (\<lambda>i::nat. Rev {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Y i)})"
    apply (rule chainI)
    apply (subst revBelowNeqSubset)      
    apply (simp add: inv_rev_rev)
    apply rule
    using f0 by fastforce
  have f3: "inv Rev (\<Squnion>i. Y i) = (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
    using a1 setrevLubEqInterII by fastforce

  have f4: "\<Inter>{x::'a set. \<exists>i::nat. x = {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Y i)}} 
    \<subseteq> {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Lub Y)}" (is "?L \<subseteq> ?R")
  proof (rule subsetI)
    fix x
    assume a1: "x \<in> ?L"
    have "chain (\<lambda> i. Rev {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Y i)})"
    proof  (rule chainI)
      fix i
      show "Rev {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Y i)} 
            \<sqsubseteq> Rev {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Y (Suc i))}"
        apply auto
        apply (simp add: less_set_def)
        sorry
    qed
    have "\<forall> i. x \<in> {uu::'a. \<exists>Z::'a set. uu \<in> Z \<and> Z \<in> inv Rev (Y i)}"
      by (metis (mono_tags, lifting) CollectI Inter_iff a1)
    then have "\<forall> i. \<exists> Z. (x \<in> Z \<and> Z \<in> inv Rev (Y i))"
      by simp
    then show "x \<in> ?R"
      sorry
  qed
  show "Rev {uu::'a. \<exists>(Z::'a set) K::'a. uu = K \<and> K \<in> Z \<and> Z \<in> inv Rev (\<Squnion>i::nat. Y i)} 
      \<sqsubseteq> (\<Squnion>i::nat. Rev {uu::'a. \<exists>(Z::'a set) K::'a. uu = K \<and> K \<in> Z \<and> Z \<in> inv Rev (Y i)})"
    apply (subst revBelowNeqSubset)
    apply (simp add: inv_rev_rev)
    apply (simp add: f2 setrevLubEqInterII inv_rev_rev)
    apply (subst f3)
    using f3 f4 by auto
qed
*)

subsection \<open>ForAll Exists\<close>

lemma setrev_for_all_ex:
  assumes "setrevForall P S"
  assumes "setrevExists (\<lambda>x. True) S"
  shows "setrevExists P S"
  by (meson assms(1) assms(2) setrevExists_def setrevForall_def)

lemma setrev_subsetforall: 
  assumes "setrevForall P S"
  and "inv Rev T \<subseteq> inv Rev S"
  shows "setrevForall P T"
  by (metis assms(1) assms(2) setrevForall_def subset_eq)

lemma setrev_ballI: "(\<And>x. x \<in> inv Rev S \<Longrightarrow> P x) \<Longrightarrow> setrevForall P S"
  by (simp add: setrevForall_def)

lemma setrev_bexCI: "setrevForall (\<lambda>x. \<not> P x \<longrightarrow> P a) S \<Longrightarrow> a \<in> inv Rev S \<Longrightarrow> setrevExists P S"
  apply (simp add: setrevExists_def setrevForall_def)
  by auto

lemma setrev_bex_triv_one_point1: "setrevExists (\<lambda>x. x = a) S \<longleftrightarrow> a \<in> inv Rev S"
  by (simp add: setrevExists_def)

lemma setrev_bex_triv_one_point2: "setrevExists (\<lambda>x. a = x) S \<longleftrightarrow> a \<in> inv Rev S"
  by (simp add: setrevExists_def)

lemma setrev_bex_one_point1: "setrevExists (\<lambda>x. x = a \<and> P x) S \<longleftrightarrow> a \<in> inv Rev S \<and> P a"
  by (simp add: setrevExists_def)

lemma setrev_bex_one_point2: "setrevExists (\<lambda>x. a = x \<and> P x) S \<longleftrightarrow> a \<in> inv Rev S \<and> P a"
  by (simp add: setrevExists_def)

lemma setrev_ball_one_point1: "setrevForall (\<lambda>x. x = a \<longrightarrow> P x) S \<longleftrightarrow> (a \<in> inv Rev S \<longrightarrow> P a)"
  by (simp add: setrevForall_def)

lemma setrev_ball_one_point2: "setrevForall (\<lambda>x. a = x \<longrightarrow> P x) S \<longleftrightarrow> (a \<in> inv Rev S \<longrightarrow> P a)"
  by (simp add: setrevForall_def)

lemma setrev_subset_eq: "inv Rev A \<subseteq> inv Rev B \<longleftrightarrow> setrevForall (\<lambda>x. x \<in> inv Rev B) A"
  by (simp add: setrevForall_def subset_eq)

lemma setrev_union_forall: 
  "setrevForall P (setrevUnion\<cdot>A\<cdot>B) \<longleftrightarrow> setrevForall P A \<and> setrevForall P B"
  by (metis (mono_tags, lifting) setrevForall_def setrevUnion_gdw)

lemma setrev_union_exists: 
  "setrevExists P (setrevUnion\<cdot>A\<cdot>B) \<longleftrightarrow> setrevExists P A \<or> setrevExists P B"
  by (metis (mono_tags, lifting) setrevExists_def setrevUnion_gdw)

lemma setrev_union_l1:
  assumes "setrevExists (\<lambda>x. x = a) A \<or> setrevExists (\<lambda>x. x = a) B"
  shows "setrevExists (\<lambda>x. x = a) (setrevUnion\<cdot>A\<cdot>B)"
  using assms by (simp add: setrevExists_def setrevUnion_gdw)

lemma setrev_inter_forall: 
  assumes "setrevForall P A \<and> setrevForall P B"
  shows "setrevForall P (setrevInter\<cdot>A\<cdot>B)"
  by (metis (no_types, lifting) IntD1 assms inv_rev_rev setrevForall_def setrevinter_insert)

lemma setrev_inter_exists: 
  assumes "setrevExists P (setrevInter\<cdot>A\<cdot>B)"
  shows "setrevExists P A \<and> setrevExists P B"
  by (metis (no_types, lifting) IntD1 IntD2 assms inv_rev_rev setrevExists_def setrevinter_insert)

lemma setrev_inter_l1:
  assumes "setrevExists  (\<lambda>x. x = a) A \<and> setrevExists (\<lambda>x. x = a) B"
  shows "setrevExists  (\<lambda>x. x = a) (setrevInter\<cdot>A\<cdot>B)"
  using assms by (simp add: setrevExists_def setrevInter_gdw)

lemma setrev_filter_forall: "setrevForall P (setrevFilter P\<cdot>A)"
  by (metis (no_types) setrevFilter_gdw setrev_ballI)

lemma setrevforall_image:
"setrevForall (\<lambda>x. setrevExists (\<lambda>y. f y = x) S) (setrevImage f S)"
proof -
obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set rev \<Rightarrow> 'a" where
  "\<forall>x0 x1. (\<exists>v2. v2 \<in> inv Rev x1 \<and> \<not> x0 v2) = (aa x0 x1 \<in> inv Rev x1 \<and> \<not> x0 (aa x0 x1))"
    by moura
  then have f1: "\<forall>r p. aa p r \<in> inv Rev r \<and> \<not> p (aa p r) \<or> setrevForall p r"
    by (metis setrev_ballI)
  have f2: "f ` inv Rev S = inv Rev (setrevImage f S)"
    by (simp add: inv_rev_rev setrevImage_def)
  obtain bb :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b" where
    "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (bb x0 x1 x2 \<in> x0 \<and> x2 = x1 (bb x0 x1 x2))"
    by moura
  then have f3: "(aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S) \<notin> f ` inv Rev S \<or>
    bb (inv Rev S) f (aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S)) \<in> inv Rev S \<and>
    aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S) = f (bb (inv Rev S) f (aa 
    (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S)))) \<and> (aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) 
    (setrevImage f S) \<in> f ` inv Rev S \<or> (\<forall>b. b \<notin> inv Rev S \<or> aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) 
    (setrevImage f S) \<noteq> f b))"
    by blast
  have "f (bb (inv Rev S) f (aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S))) = aa 
    (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S) \<or> bb (inv Rev S) f (aa (\<lambda>a. setrevExists 
    (\<lambda>b. f b = a) S) (setrevImage f S)) \<notin> inv Rev S \<or> aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) 
    (setrevImage f S) \<noteq> f (bb (inv Rev S) f (aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S)))"
    by auto
  then have "setrevForall (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S) \<or> bb (inv Rev S) f 
    (aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) (setrevImage f S)) \<notin> inv Rev S \<or> aa (\<lambda>a. setrevExists 
    (\<lambda>b. f b = a) S) (setrevImage f S) \<noteq> f (bb (inv Rev S) f (aa (\<lambda>a. setrevExists (\<lambda>b. f b = a) S) 
    (setrevImage f S)))"
    using f1 by (meson setrevExists_def)
  then show ?thesis
    using f3 f2 f1 by (metis (no_types))
qed

subsection \<open>Size\<close>

lemma setrev_size_suc: 
  assumes "finite X" and "z \<notin> X" 
  shows "setrevSize (Rev (insert z X)) = lnsuc\<cdot>(setSize X)"
  by (simp add: assms(1) assms(2) inv_rev_rev setSizeSuc setrevSize_def)

lemma setrev_size_empty: "setrevSize (Rev {}) = Fin 0"
  by (simp add: inv_rev_rev setSizeEmpty setrevSize_def)

lemma setrev_size_singleton: "setrevSize (Rev {x}) = lnsuc\<cdot>(Fin 0)"
  by (simp add: inv_rev_rev setSizeSingleton setrevSize_def)

lemma setrev_size_union: 
  "setrevSize (setrevUnion\<cdot>X\<cdot>Y) + setrevSize (setrevInter\<cdot>X\<cdot>Y) = setrevSize X + setrevSize Y"
  apply (simp add: setrevUnion_def setrevInter_def)
  by (simp add: inv_rev_rev setrevSize_def setsize_union)

lemma setrev_size_union_disjoint: assumes "setrevInter\<cdot>X\<cdot>Y = Rev {}"
  shows "setrevSize (setrevUnion\<cdot>X\<cdot>Y) = setrevSize X + setrevSize Y"
  apply (insert assms)
  by (simp add: setrevUnion_def setrevInter_def setrevSize_def inv_rev_rev setsize_union_disjoint)

lemma setrev_size_mono_union: "setrevSize X \<le> setrevSize (setrevUnion\<cdot>X\<cdot>Y)"
  by (simp add: setrevSize_def setrevUnion_def inv_rev_rev setsize_mono_union)

lemma setrev_size_mono: 
  assumes "F \<sqsubseteq> G"
  shows "setrevSize G \<le> setrevSize F"
  apply (insert assms)
  by (simp add: setrevSize_def revBelowNeqSubset setsize_mono)


end