theory GLB

imports GFP Instantiation

begin
default_sort rev_div_cpo


(* greatest LOWER Bound *)
definition glb :: "'a::rev_div_cpo set \<Rightarrow> 'a"
  where "glb S = (inv Rev) (lub (Rev ` S))"

lemma glb_below: "longChain S \<Longrightarrow> S \<subseteq>C \<Longrightarrow> C\<in> DIV \<Longrightarrow> s\<in>S \<Longrightarrow> glb S \<sqsubseteq> s"
  apply(auto simp add: glb_def)
  by (metis (no_types, hide_lams) below_refl below_rev_def below_trans div_cpo_lub_ub imageI image_mono inv_rev longchain_rev rev_division)

lemma glb_greatest: assumes "longChain S" and "S \<subseteq>C" and "C\<in>DIV" and "(\<And>s. s\<in>S \<Longrightarrow> X \<sqsubseteq>s)"
  shows "X \<sqsubseteq> glb S"
proof - 
  have "(\<And>s. s\<in>(Rev`S) \<Longrightarrow> s \<sqsubseteq> Rev X)"
    using assms(4) below_rev.simps by blast
  hence "lub (Rev ` S) \<sqsubseteq> Rev X"
    by (meson assms(1) assms(2) assms(3) holmf_below_iff longchain_rev rev_div_lub_ex)
  thus ?thesis
    by (simp add: below_rev_def glb_def) 
qed


definition longAdm_glb :: "'a set \<Rightarrow> ('a::rev_div_cpo \<Rightarrow> bool) \<Rightarrow> bool"
  where "longAdm_glb C P \<longleftrightarrow> (\<forall>Y. longChain Y \<longrightarrow> Y \<subseteq> C \<longrightarrow> (\<forall>y\<in>Y. P y) \<longrightarrow> P (glb Y))"


lemma longadm_glb_all: "(\<And>y. longAdm_glb C (\<lambda>x. P x y)) \<Longrightarrow> longAdm_glb C (\<lambda>x. \<forall>y. P x y)"
  by(auto simp add: longAdm_glb_def)

lemma longadm2glb: "longAdm_glb C P \<longleftrightarrow> longAdm (Rev`C) (\<lambda>a. P (inv Rev a))"
  unfolding longAdm_glb_def longAdm_def glb_def
  apply auto
  apply (metis image_eqI inv_rev longchain_rev subset_imageE)
  by (metis (no_types, lifting) f_inv_into_f image_mono inv_into_into inv_rev longchain_rev)

lemma longadm2longadm_glb: "longAdm_glb C P \<Longrightarrow>  longAdm (Rev`C) (\<lambda>a. P (inv Rev a))"
  using longadm2glb by blast

lemma longadm_glb_const: assumes "C\<in>DIV"
  shows "longAdm_glb C (\<lambda>x. K \<sqsubseteq> x)"
  unfolding longAdm_glb_def
  using assms glb_greatest by blast


lemma glb_fun_below: assumes "longChain Y" and "Y \<subseteq> C" and "C\<in>DIV"
  shows "(\<lambda>c. glb ((\<lambda>y. y c ) `Y)) \<sqsubseteq> (glb Y)"
  apply(rule glb_greatest [of Y C], simp_all add: assms)
  apply(auto simp add: below_fun_def)
  by (smt assms(1) assms(2) assms(3) div_const_fun glb_below image_iff lc_const_fun)

lemma glb_fun_below_const: assumes "longChain Y" and "Y \<subseteq> C" and "C\<in>DIV"
  shows "glb ((\<lambda>y. y c ) `Y) \<sqsubseteq> (glb Y) c"
  by (metis assms(1) assms(2) assms(3) fun_belowD glb_fun_below)

lemma longadm_glb_const_fun: assumes "C\<in>DIV"
  shows "longAdm_glb C (\<lambda>x. K \<sqsubseteq> x c)"
proof(auto simp add: longAdm_glb_def)
  fix Y
  assume y_lc: "longChain Y" and "Y \<subseteq> C" and " \<forall>y\<in>Y. K \<sqsubseteq> y c"
  obtain C2 where "C2\<in>DIV" and "(\<lambda>y. y c ) `Y \<subseteq> C2"
    using \<open>Y \<subseteq> C\<close> assms div_const_fun by force
  hence "\<And>y. y\<in>Y \<Longrightarrow> glb ((\<lambda>y. y c ) `Y) \<sqsubseteq> y c"
    by (metis glb_below imageI lc_const_fun y_lc)
  hence "K \<sqsubseteq> glb ((\<lambda>y. y c ) `Y)"
    using glb_greatest 
    proof -
      have "\<And>b. b \<notin> (\<lambda>f. f c) ` Y \<or> b \<notin> (\<lambda>f. f c) ` Y \<or> K \<sqsubseteq> b"
        using \<open>\<forall>y\<in>Y. K \<sqsubseteq> y c\<close> by fastforce
      then show ?thesis
        by (metis \<open>\<And>thesis. (\<And>C2. \<lbrakk>C2 \<in> DIV; (\<lambda>y. y c) ` Y \<subseteq> C2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> glb_greatest lc_const_fun y_lc)
    qed
    thus "K \<sqsubseteq> glb Y c"
      using \<open>Y \<subseteq> C\<close> assms below_refl box_below glb_fun_below_const y_lc by fastforce
  qed




end