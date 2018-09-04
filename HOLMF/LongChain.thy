theory LongChain

imports HOLCF

begin

default_sort po

definition longChain :: "'a set \<Rightarrow> bool" where
"longChain S \<equiv> \<forall>a b. (a\<in>S \<and> b\<in>S) \<longrightarrow> (a\<sqsubseteq>b \<or> b\<sqsubseteq>a)"




lemma longchainI: "(\<And>a b. a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> (a\<sqsubseteq>b \<or> b\<sqsubseteq>a)) \<Longrightarrow> longChain S"
  by (simp add: longChain_def)

lemma longchain_mono: assumes "longChain S" and "monofun f"
  shows "longChain (f`S)"
  apply(rule longchainI)
  by (metis (no_types, lifting) assms(1) assms(2) image_iff longChain_def monofunE)

lemma holmf_below_lub: "\<lbrakk>longChain S;\<exists>x. S <<| x; s\<in>S;x \<sqsubseteq> s\<rbrakk> \<Longrightarrow> x \<sqsubseteq> lub S"
  using box_below is_ub_thelub_ex by blast

lemma holmf_below_iff: "longChain S \<Longrightarrow> \<exists>x. S <<| x \<Longrightarrow> lub S \<sqsubseteq> x \<longleftrightarrow> (\<forall>s\<in>S. s \<sqsubseteq> x)"
  using is_lub_below_iff is_ub_def lub_eqI by blast



thm max_in_chain_def
lemma lc_finite: assumes "S\<noteq>{}" and "longChain S" and "finite S"
  obtains l where "l\<in>S" and "\<And>x. x\<in>S \<Longrightarrow> x\<sqsubseteq>l"
  sorry

lemma  "S\<noteq>{} \<Longrightarrow> longChain S \<Longrightarrow> finite S \<Longrightarrow> lub S \<in>S"
  by (metis is_ub_def lc_finite lub_maximal)


lemma assumes  "s\<in>S" and "\<exists>x\<in>C. S <<| x"
  shows "s \<sqsubseteq> lub S"
  using assms(1) assms(2) is_ub_thelub_ex by blast

lemma assumes "S\<noteq>{}" and "S \<subseteq> C" and "\<exists>x. S <<| x"
  shows "lub S \<in> C"
  oops

end
