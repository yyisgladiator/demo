theory LongChain

imports HOLCF

begin

default_sort po

definition longChain :: "'a set \<Rightarrow> bool" where
"longChain S \<equiv> S\<noteq>{} \<and> (\<forall>a b. (a\<in>S \<and> b\<in>S) \<longrightarrow> (a\<sqsubseteq>b \<or> b\<sqsubseteq>a))"

definition longAdm :: "'a set \<Rightarrow> ('a::po \<Rightarrow> bool) \<Rightarrow> bool"
  where "longAdm C P \<longleftrightarrow> (\<forall>Y. longChain Y \<longrightarrow> Y \<subseteq> C \<longrightarrow> (\<forall>y\<in>Y. P y) \<longrightarrow> P (lub Y))"


lemma longchainI: "(\<And>a b. a\<in>S \<Longrightarrow> b\<in>S \<Longrightarrow> (a\<sqsubseteq>b \<or> b\<sqsubseteq>a)) \<Longrightarrow> S\<noteq>{} \<Longrightarrow> longChain S"
  by (simp add: longChain_def)

lemma longchain_mono: assumes "longChain S" and "monofun f"
  shows "longChain (f`S)"
  apply(rule longchainI)
  apply (metis (no_types, lifting) assms(1) assms(2) image_iff longChain_def monofunE)
  using assms(1) longChain_def by auto

lemma longchain_subset: "longChain S \<Longrightarrow> C \<subseteq> S \<Longrightarrow> C\<noteq>{} \<Longrightarrow> longChain C"
  by (simp add: longChain_def set_mp)

lemma mono_lub_below: assumes "monofun f" and "longChain S"
      and cpo: "\<And>S. longChain S \<Longrightarrow> S\<noteq>{} \<Longrightarrow> S\<subseteq>C \<Longrightarrow> \<exists>x\<in>C. S <<| x"
      and goodf: "\<And>a. a\<in>C \<Longrightarrow> f a\<in>C" 
      and "S \<subseteq> C"
  shows "lub (f`S) \<sqsubseteq> f (lub S)"
proof -
  have "longChain (f`S)"
    by (simp add: assms(1) assms(2) longchain_mono)
  have "\<And>s. s\<in>S \<Longrightarrow> s\<sqsubseteq>lub S"
    using assms(2) assms(5) is_ub_thelub_ex local.cpo by fastforce
  hence "\<And>s. s\<in>S \<Longrightarrow> f s\<sqsubseteq> f(lub S)"
    by (simp add: assms(1) monofunE)
  hence "f ` S <| f (lub S)"
    using ub_imageI by blast
  thus ?thesis
    by (metis \<open>longChain (f ` S)\<close> assms(5) goodf image_mono image_subsetI is_lub_thelub_ex local.cpo longChain_def subset_trans)
qed


lemma holmf_below_lub: "\<lbrakk>longChain S;\<exists>x. S <<| x; s\<in>S;x \<sqsubseteq> s\<rbrakk> \<Longrightarrow> x \<sqsubseteq> lub S"
  using box_below is_ub_thelub_ex by blast

lemma holmf_below_iff: "longChain S \<Longrightarrow> \<exists>x. S <<| x \<Longrightarrow> lub S \<sqsubseteq> x \<longleftrightarrow> (\<forall>s\<in>S. s \<sqsubseteq> x)"
  using is_lub_below_iff is_ub_def lub_eqI by blast



lemma lc_finite: assumes  "finite S"
  shows  "S\<noteq>{} \<longrightarrow> longChain S\<longrightarrow> (\<exists>l. l\<in>S \<and> (\<forall>x\<in>S. x\<sqsubseteq>l))"
  apply(rule finite_induct [of S])
  apply (simp add: assms(1))
   apply blast
  apply rule
proof 
  fix x F
  assume f_fin: "finite F" and x_f: "x \<notin> F"  and f_max: "F \<noteq> {} \<longrightarrow> longChain F \<longrightarrow> (\<exists>l. l \<in> F \<and> (\<forall>x\<in>F. x \<sqsubseteq> l))" 
      and "insert x F \<noteq> {}" and f_chain: "longChain (insert x F)"
  let ?P = "(\<exists>l. l \<in> insert x F \<and> (\<forall>x\<in>insert x F. x \<sqsubseteq> l))"

  have "F \<noteq> {} \<Longrightarrow> longChain F"
    by (meson \<open>longChain (insert x F)\<close> insertCI longChain_def)
  hence "F \<noteq> {} \<Longrightarrow> ?P"
    by (metis f_chain f_max insertE longChain_def rev_below_trans set_rev_mp subset_insertI)
  thus "?P"
    by blast
qed
  

lemma lc_finite_lub: "longChain S \<Longrightarrow> finite S \<Longrightarrow> lub S \<in>S"
  by (metis is_ubI lc_finite longChain_def lub_maximal)
  
lemma lc_finite_lub_ex: "longChain S \<Longrightarrow> finite S \<Longrightarrow> \<exists>x \<in> S. S <<| x"
  by (metis is_lub_maximal is_ubI lc_finite longChain_def)

lemma chain2longchain: "chain K \<Longrightarrow> longChain (range K)"
  apply(auto simp add: longChain_def)
  using nat_le_linear po_class.chain_mono by blast

lemma assumes "longChain Y" and "infinite Y"
  obtains y where "y\<in>Y" and "longChain (Set.filter (\<lambda>x. y\<sqsubseteq>x) Y)"
  by (metis (mono_tags, hide_lams) all_not_in_conv assms(1) longChain_def member_filter)


lemma longchain_one_less: assumes "longChain Y" and "infinite Y"
  shows "longChain (Y - {y})"
  by (metis Diff_subset assms(1) assms(2) infinite_imp_nonempty infinite_remove longchain_subset)

lemma longchain_fin_less: assumes "longChain Y" and "infinite Y" and "finite K"
  shows "longChain (Y - K)"
  apply(auto simp add: longChain_def)
  using assms(2) assms(3) infinite_super apply blast
  using assms(1) longChain_def by blast


lemma set_infinite_split: "infinite Y \<Longrightarrow> (infinite (Set.filter (\<lambda>a. P a) Y)) \<or> (infinite (Set.filter  (\<lambda>a. \<not> P a) Y))"
proof(rule ccontr, auto)
  assume "infinite Y" and "finite (Set.filter P Y)" and "finite (Set.filter (\<lambda>a. \<not> P a) Y)"
  have "(Set.filter (\<lambda>a. P a) Y) \<union> (Set.filter (\<lambda>a. \<not> P a) Y) = Y" by auto
  hence "finite Y"
    by (metis \<open>finite (Set.filter (\<lambda>a. \<not> P a) Y)\<close> \<open>finite (Set.filter P Y)\<close> finite_UnI)
  thus False
    using \<open>infinite Y\<close> by blast 
qed

(*
lemma assumes "longChain Y" and "infinite Y"
  obtains y where "y\<in>Y" and "infinite (Set.filter (\<lambda>x. y\<sqsubseteq>x) Y) \<or> infinite (Set.filter (\<lambda>x. \<not>(y\<sqsubseteq>x)) Y)"
  using assms(2) set_infinite_split by force

lemma longchain2chain_fin: assumes "longChain K" and "infinite K"
  obtains Y where "chain Y" and "range Y \<subseteq> K" and "infinite (range Y)"

lemma longchain2chain_fin: assumes "longChain K" and "finite K"
  obtains Y where "chain Y" and "range Y = K"
*)

lemma assumes  "s\<in>S" and "\<exists>x\<in>C. S <<| x"
  shows "s \<sqsubseteq> lub S"
  using assms(1) assms(2) is_ub_thelub_ex by blast

lemma assumes "S\<noteq>{}" and "S \<subseteq> C" and "\<exists>x. S <<| x"
  shows "lub S \<in> C"
  oops


lemma lc_const_fun: "longChain Y \<Longrightarrow> longChain ((\<lambda>y. y c ) `Y)"
  by (simp add: fun_belowD longchain_mono monofun_def)


lemma longadm_all: "(\<And>y. longAdm C (\<lambda>x. P x y)) \<Longrightarrow> longAdm C (\<lambda>x. \<forall>y. P x y)"
  by(auto simp add: longAdm_def)


end
