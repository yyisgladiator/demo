theory SetRev
  imports "inc/SetPcpo"
begin

default_sort type

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
    
definition setify::"('m \<Rightarrow> ('n set rev)) \<rightarrow> ('m \<Rightarrow> 'n) set rev" where
"setify \<equiv> \<Lambda> f. Rev {g. \<forall>m. g m \<in> (inv Rev(f m))}"

definition setrevUnion:: "'m set rev \<rightarrow> 'm set rev \<rightarrow> 'm set rev" where
"setrevUnion \<equiv> (\<Lambda> A B. Rev((inv Rev A) \<union> (inv Rev B)))"


section \<open>Lemmas\<close>

subsection \<open>General\<close>

lemma setrev_eqI: "inv Rev a = inv Rev b \<Longrightarrow> a = b"
  by (metis rev_inv_rev)

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

lemma setrevLub_lub_eq_all:
  assumes "chain (Y:: nat \<Rightarrow> 'a set rev)"
    shows "\<And>x. (x \<in> inv Rev (Lub Y) \<longleftrightarrow> (\<forall>i. x \<in> inv Rev (Y i)))"
  apply(simp only: setrevLubEqInter assms)
  apply(simp only: inv_rev_rev)
  by auto


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

lemma setrevfilter_condition: "\<And>x. x \<in> (inv Rev (setrevFilter P\<cdot>A)) \<Longrightarrow> P x"
  by (simp add: inv_rev_rev setrevFilter_def)

lemma setrevfilter_included: "\<And>x. x \<in> (inv Rev (setrevFilter P\<cdot>A)) \<Longrightarrow> x \<in> inv Rev A"
  by (simp add: inv_rev_rev setrevFilter_def)

lemma setrevfilter_reversed: "\<And>x. P x \<and> x \<in> inv Rev A \<Longrightarrow> x \<in> (inv Rev (setrevFilter P\<cdot>A))"
  apply(simp add: setrevFilter_def)
  by(simp add: Set.filter_def inv_rev_rev)

lemma setrevFilter_gdw: "\<And>x. x \<in> (inv Rev (setrevFilter P\<cdot>A)) \<longleftrightarrow> P x \<and> x \<in> inv Rev A"
  by (meson setrevfilter_condition setrevfilter_included setrevfilter_reversed)


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
  apply(rule contI2)
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


lemma image_mono_rev:  "monofun (\<lambda> S::'a set rev.  Rev (f ` (inv Rev S)))"
  apply (rule monofunI)
  by (simp add: image_mono inv_rev_rev revBelowNeqSubset)

lemma image_cont_rev: assumes "inj f" 
  shows "cont (\<lambda> S::'a set rev.  Rev (f ` (inv Rev S)))"
  apply (rule contI2)
   apply (simp add: image_mono_rev)
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
  
end