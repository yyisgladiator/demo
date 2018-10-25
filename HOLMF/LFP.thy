theory LFP

imports KnasterTarski Division

begin

default_sort div_pcpo

(* There exists a division in which f is complete *)
definition goodFormed :: "'a::division set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"goodFormed C f \<equiv> \<forall>aa\<in>C. f aa \<in>C"

definition lfp:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp A f = (THE x. f x = x \<and> x\<in>A \<and> (\<forall>y\<in>A. f y \<sqsubseteq> y \<longrightarrow> x\<sqsubseteq>y))"

lemma lfp_condition:
  fixes f::"'a::div_pcpo \<Rightarrow> 'a"
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


lemma lfp_greater: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
    and "\<And>x. x\<in>C \<Longrightarrow>f x = x \<Longrightarrow> y\<sqsubseteq>x"
  shows "y \<sqsubseteq> (lfp C f)"
  by (simp add: assms(1) assms(2) assms(3) assms(4)  lfp_all)

lemma lfp_least_eq: assumes "monofun f"
    and "goodFormed C f"
    and "C \<in> DIV"
    and "\<And>x. x\<in>C \<Longrightarrow> f x \<sqsubseteq> x \<Longrightarrow> y\<sqsubseteq>x"
    and "f y \<sqsubseteq> y"
    and "y \<in> C"
  shows "(lfp C f) = y"
  by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) below_antisym lfp_all)


lemma lfp_monofun: assumes "f\<sqsubseteq>g"
    and "monofun f" and "monofun g"
    and "goodFormed C f" and "goodFormed C g"
    and "C \<in> DIV"
  shows "lfp C f \<sqsubseteq> lfp C g"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) below_fun_def lfp_div lfp_fix lfp_least)


end