theory LFP

imports KnasterTarski Division

begin

default_sort div_pcpo

(* There exists a division in which f is complete *)
definition goodFormed :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"goodFormed C f \<equiv> \<forall>aa\<in>C. f aa \<in>C"

definition lfp:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp A f = (THE x. f x = x \<and> x\<in>A \<and> (\<forall>y\<in>A. f y \<sqsubseteq> y \<longrightarrow> x\<sqsubseteq>y))"

lemma lfp_condition: 
  assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "\<exists>!x. (f x = x \<and> x\<in>C \<and> (\<forall>y\<in>C. f y \<sqsubseteq> y \<longrightarrow> x\<sqsubseteq>y))"
  apply(subst knaster_tarski)
  using assms goodFormed_def by (auto simp add: div_cpo_g div_pcpo)
  


lemma lfp_all: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "(f (lfp C f) = (lfp C f) \<and>  (lfp C f)\<in>C \<and> (\<forall>y\<in>C. f y \<sqsubseteq> y \<longrightarrow> (lfp C f)\<sqsubseteq>y))"
  unfolding lfp_def
  apply(rule theI')
  by (simp add: assms(1) assms(2) assms(3) lfp_condition)


lemma lfp_fix: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "(lfp C f) = f (lfp C f)"
  by (simp add: assms(1) assms(2) assms(3) lfp_all)

lemma lfp_div: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
  shows "(lfp C f) \<in> C"
  by (simp add: assms(1) assms(2) assms(3) lfp_all)

lemma lfp_least: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
    and "f y \<sqsubseteq> y"
    and "y \<in> C"
  shows "(lfp C f) \<sqsubseteq> y"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) lfp_all)


lemma lfp_monofun: assumes "f\<sqsubseteq>g"
    and "monofun f" and "monofun g"
    and "goodFormed C f" and "goodFormed C g"
    and "C \<in> DIV"
  shows "lfp C f \<sqsubseteq> lfp C g"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) below_fun_def lfp_div lfp_fix lfp_least)






section\<open>ToDo: induction\<close>


(* similar to iterate, but no longer countable *)
definition longIterate :: "'a::div_pcpo set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
"longIterate C f = lfp (Pow C) (\<lambda> (S::'a set).  insert (div_bot C) (f `S))"

lemma longiterate_mono: assumes "C\<in>DIV" shows "monofun (\<lambda> (S::'a set).  insert (div_bot C) (f `S))"
  apply(rule monofunI)
  apply(simp add: less_set_def)
  by blast

lemma longiterate_good: 
  fixes C ::" 'a ::div_pcpo set"
  assumes "C\<in>DIV" and "goodFormed C f"
  shows "goodFormed (Pow C) (\<lambda>S. insert (div_bot C) (f ` S))"
  apply(auto simp add: goodFormed_def)
  apply (simp add: assms(1) div_bot)
  using assms(2) goodFormed_def by auto


lemma longiterate_step: assumes  "C\<in>DIV" and "goodFormed C f"
  shows "longIterate C f =  insert (div_bot C) (f ` (longIterate C f)) "
  apply(subst longIterate_def)
  apply(subst lfp_fix)
  apply (simp add: assms(1) longiterate_mono)
  apply (simp add: assms(1) assms(2) longiterate_good)
  apply (simp add: DIV_set_def assms(1))
  by (simp add: longIterate_def)

lemma longiterate_bot: assumes "C\<in>DIV" and "goodFormed C f"
    shows "div_bot C \<in> (longIterate C f)"
  by(subst longiterate_step, auto simp add: assms)


lemma longiterate_subset: assumes "C\<in>DIV" and "goodFormed C f" shows "longIterate C f \<subseteq> C"
  using DIV_set_def assms(1) assms(2) lfp_div longIterate_def longiterate_good longiterate_mono by fastforce

lemma longiterate_chain: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "longChain (longIterate C f)"
  apply(rule longchainI)
  oops


lemma longiterate_lfp: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "lub (longIterate C f) = lfp C f"
  oops


lemma lfp_induction: assumes "goodFormed C f" and "C \<in> DIV"
  and "longAdm P"
  and "monofun f"
  and "\<And>x. x\<in>C \<Longrightarrow> bott\<sqsubseteq>x" and "bott\<in>C"
  and "P bott"
  and "\<And>x. x\<in>C \<Longrightarrow> P x \<Longrightarrow> P (f x)"
  shows "P (lfp C f)"
  oops


end