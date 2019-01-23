theory Induction

imports LFP Instantiation

begin

default_sort div_pcpo


(* similar to iterate, but no longer countable *)
definition longIterate :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
"longIterate C f = Inductive.lfp (* (Pow C)*) (\<lambda> (S::'a set).  insert (div_bot C) (f `S) \<union> {lub K | K. K \<subseteq>S \<and> longChain K })"

lemma longiterate_monofun[simp]: assumes "C\<in>DIV" shows "monofun (\<lambda> (S::'a set).  insert (div_bot C) (f `S) \<union> {lub K | K. K \<subseteq>S \<and> longChain K })"
  apply(rule monofunI)
  apply(simp add: less_set_def)
  by blast

lemma longiterate_mono[simp]: assumes "C\<in>DIV" shows "mono (\<lambda> (S::'a set).  insert (div_bot C) (f `S) \<union> {lub K | K. K \<subseteq>S \<and> longChain K })"
  apply(rule monoI)
  apply(simp add: less_set_def)
  by blast

lemma longiterate_good[simp]: 
  fixes C ::" 'a ::div_pcpo set"
  assumes "C\<in>DIV" and "goodFormed C f"
  shows "goodFormed (Pow C) (\<lambda>S. insert (div_bot C) (f `S) \<union> {lub K | K. K \<subseteq>S \<and> longChain K })"
  apply(auto simp add: goodFormed_def)
  apply (simp add: assms(1) div_bot)
  using assms(2) goodFormed_def apply auto
  by (meson assms(1) div_cpo_lub_in subset_trans)


lemma longiterate_step: assumes  "C\<in>DIV" 
  shows "(longIterate C f) = insert (div_bot C) (f `(longIterate C f)) \<union> {lub K | K. K \<subseteq>(longIterate C f) \<and> longChain K }"
  unfolding longIterate_def
  apply(subst lfp_unfold )
  using assms(1) longiterate_mono apply auto[1]
  by blast

lemma longiterate_bot[simp]: assumes "C\<in>DIV"
    shows "div_bot C \<in> (longIterate C f)"
  by(subst longiterate_step, auto simp add: assms)


lemma longiterate_subset: assumes "C\<in>DIV" and "goodFormed C f" shows "longIterate C f \<subseteq> C"
  unfolding longIterate_def
  apply(rule lfp_ordinal_induct)
  using assms(1) longiterate_mono apply blast
  apply (smt Pow_iff assms(1) assms(2) goodFormed_def longiterate_good)
  by blast

lemma longiterate_lub_in: assumes "C\<in>DIV" and "goodFormed C f"
  shows "\<And>K. longChain K \<Longrightarrow> K\<subseteq>(longIterate C f) \<Longrightarrow> lub K\<in>(longIterate C f)"
  by (metis (mono_tags, lifting) CollectI UnCI assms(1) assms(2) longiterate_step)

lemma longchain_map: 
  fixes C ::"'a set"
    assumes "longChain K" and "K \<subseteq> C" and "C\<in>DIV" and "(\<And>k. k\<in>K \<Longrightarrow> k \<sqsubseteq> f k)" and "monofun f" and "goodFormed C f"
  shows "(lub K \<sqsubseteq> f (lub K))"
proof - 
  have "longChain (f`K)"
    by (simp add: assms(1) assms(5) longchain_mono)
  have "\<And>k. k\<in>K \<Longrightarrow> k \<sqsubseteq> f(lub K)"
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) below_refl box_below div_cpo_g is_ub_thelub_ex monofun_def)
  thus ?thesis
    using assms(1) assms(2) assms(3) div_cpo_g holmf_below_iff by blast 
qed

lemma lub_in: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "\<And>K::'a set. K \<subseteq> {y::'a. y \<sqsubseteq> f y \<and> y \<in> C} \<Longrightarrow> longChain K \<Longrightarrow> lub K \<sqsubseteq> f (lub K)"
proof -
fix K :: "'a set"
  assume a1: "longChain K"
  assume a2: "K \<subseteq> {y. y \<sqsubseteq> f y \<and> y \<in> C}"
  obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
    "\<And>f A Aa Ab. (\<not> monofun f \<or> \<not> longChain A \<or> \<not> goodFormed Aa f \<or> \<not> A \<subseteq> Aa \<or> Aa \<notin> DIV \<or> lub A \<sqsubseteq> f (lub A) \<or> aa A f \<in> A) \<and> (\<not> monofun f \<or> \<not> longChain A \<or> \<not> goodFormed Ab f \<or> \<not> A \<subseteq> Ab \<or> Ab \<notin> DIV \<or> aa A f \<notsqsubseteq> f (aa A f) \<or> lub A \<sqsubseteq> f (lub A))"
    by (metis (full_types) longchain_map)
then show "lub K \<sqsubseteq> f (lub K)"
  using a2 a1 assms(1) assms(2) assms(3) by blast
qed

lemma long_iterate_below_fix: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "longIterate C f \<sqsubseteq> {y. y \<sqsubseteq> f y \<and> y \<in>C}"
  apply(simp add: longIterate_def less_set_def)
  apply(rule lfp_ordinal_induct)
  using assms(2) longiterate_mono apply auto[1]
  apply auto
  using assms(2) assms(3) div_bot goodFormed_def apply blast
  using assms(2) div_bot apply blast
  apply (metis (mono_tags, lifting) CollectD assms(1) monofunE subsetCE)
  apply (metis (mono_tags, lifting) Ball_Collect assms(3) goodFormed_def set_cpo_simps(1))
  using assms(1) assms(2) assms(3) lub_in apply fastforce
  by (simp add: assms(2) div_cpo_lub_in subset_iff)


lemma fixes C::"'a::div_cpo set"
  shows "C\<in>DIV \<Longrightarrow> longAdm C (\<lambda>x. x \<sqsubseteq> K)"
  apply(auto simp add: longAdm_def)
  using div_cpo_g holmf_below_iff by blast

lemma long_iterate_below_fix_least: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" and "a\<in>longIterate C f"
  shows "a \<sqsubseteq> lfp C f"
apply(rule lfp_induct_set [of "a" " (\<lambda> (S::'a set).  insert (div_bot C) (f `S) \<union> {lub K | K. K \<subseteq>S \<and> longChain K })"])
  using assms(4) longIterate_def apply blast
  using assms(2) longiterate_mono apply blast
  apply auto
  apply (simp add: assms(1) assms(2) assms(3) div_bot lfp_div)
  using assms(1) assms(2) assms(3) lfp_fix monofunE apply fastforce
proof -
  fix K::"'a set"
  assume k_subset: "K \<subseteq> complete_lattice_class.lfp (\<lambda>S::'a set. insert (div_bot C) (f ` S \<union> {lub K |K::'a set. K \<subseteq> S \<and> longChain K}))"
   and  k_elem: "K \<subseteq> {x::'a. x \<sqsubseteq> LFP.lfp C f}" and k_chain: "longChain K"
  have "K \<subseteq> longIterate C f" by(simp add: longIterate_def k_subset) 
  hence "K \<subseteq> C"
    using assms(2) assms(3) longiterate_subset by auto
  thus "lub K \<sqsubseteq> LFP.lfp C f"
    by (metis Ball_Collect assms(2) div_cpo_g holmf_below_iff k_chain k_elem)
qed


lemma long_iterate_below_fix_least_set: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "longIterate C f \<sqsubseteq> {y. y \<sqsubseteq> f y \<and> y \<in> C \<and> (\<forall>x\<in>{x. f x\<sqsubseteq> x \<and> x\<in>C}. y\<sqsubseteq>x)}"
  apply(subst less_set_def)
  apply auto
  apply (smt CollectD SetPcpo.less_set_def assms(1) assms(2) assms(3) long_iterate_below_fix subsetCE)
  using assms(2) assms(3) longiterate_subset apply blast
  using assms(1) assms(2) assms(3) lfp_all long_iterate_below_fix_least rev_below_trans by blast


lemma long_iterate_below_fix2: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "f x\<sqsubseteq> x \<Longrightarrow> x\<in>C \<Longrightarrow> a\<in>longIterate C f \<Longrightarrow> a\<sqsubseteq> x" 
  using long_iterate_below_fix_least_set apply (auto simp add: assms SetPcpo.less_set_def)
  using assms(1) assms(2) assms(3) by blast

lemma long_iterate_below_fix3: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" 
  shows "a\<in>longIterate C f \<Longrightarrow> a\<sqsubseteq>f a"
  using long_iterate_below_fix_least_set apply (auto simp add: assms SetPcpo.less_set_def)
  using assms(1) assms(2) assms(3) apply blast+
  done

lemma long_iterate_below_fix4: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" and "x\<in>longIterate C f"
  shows "x\<sqsubseteq>lfp C f"
  apply(rule lfp_greater, auto simp add: assms)
  using assms(1) assms(2) assms(3) assms(4) long_iterate_below_fix2 by fastforce

lemma longiterate_step2: assumes "C\<in>DIV" and "goodFormed C f" 
  and "x \<in> longIterate C f"
shows "f x \<in> longIterate C f"
  using assms longiterate_step by fastforce


lemma longiterate_lfp_in: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "lfp C f \<in> longIterate C f"
proof - 
  have h1: "\<And>K. longChain K \<Longrightarrow> K\<subseteq>(longIterate C f) \<Longrightarrow> \<exists>u\<in>(longIterate C f). \<forall>a\<in>K. a \<sqsubseteq> u"
    by (meson assms(2) assms(3) div_cpo_g dual_order.trans is_ub_thelub_ex longiterate_lub_in longiterate_subset)
  obtain a where a_def: "a\<in>(longIterate C f)" using assms(2) longiterate_bot by blast
  obtain z where "z\<in>(longIterate C f)" and "\<And>a. a\<in>(longIterate C f) \<Longrightarrow> (z\<sqsubseteq>a \<longrightarrow> a=z)" 
    using h1 by (metis a_def empty_iff own_zorn3)
  thus ?thesis
    by (metis assms(1) assms(2) assms(3) lfp_least_eq long_iterate_below_fix2 long_iterate_below_fix3 longiterate_step2 longiterate_subset subsetCE) 
qed




lemma longiterate_lfp: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "lfp C f = lub (longIterate C f)"
  apply(rule lfp_least_eq, simp_all add: assms)
    apply (metis assms(1) assms(2) assms(3) is_ubI lfp_all long_iterate_below_fix4 longiterate_bot longiterate_lfp_in lub_maximal)
  apply (metis assms(1) assms(2) assms(3) is_ubI lfp_fix long_iterate_below_fix4 longiterate_bot longiterate_lfp_in lub_maximal)
  by (metis assms(1) assms(2) assms(3) below_refl is_ubI lfp_div lfp_fix long_iterate_below_fix2 longiterate_bot longiterate_lfp_in lub_maximal)

lemma longiterate_step_back: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" and "x\<in>longIterate C f" and "x\<noteq>div_bot C"
  obtains a where "a\<sqsubseteq>x" and "a\<noteq>x" and "a\<in>longIterate C f" 
  using assms(2) assms(3) assms(4) assms(5) div_bot longiterate_bot longiterate_subset by blast


lemma longiterate_induction: assumes "goodFormed C f" and "C \<in> DIV"
  and "longAdm C P"
  and "P (div_bot C)"
  and "\<And>x. x\<in>C \<Longrightarrow> P x \<Longrightarrow> P (f x)"
  and "x\<in>longIterate C f"
shows "P x"
  apply(rule lfp_induct_set [of "x" " (\<lambda> (S::'a set).  insert (div_bot C) (f `S) \<union> {lub K | K. K \<subseteq>S \<and> longChain K })"])
  apply(simp_all only: longIterate_def [symmetric])
  using assms(6) longIterate_def apply blast
  using assms(2) longiterate_mono apply blast
  apply auto
  apply (simp add: assms(4))
  using assms(1) assms(2) assms(5) longiterate_subset apply auto[1]
  by (metis longAdm_def Ball_Collect assms(1) assms(2) assms(3) dual_order.trans longiterate_subset)
  



section \<open>high level induction lemma\<close>

lemma lfp_induction: assumes "goodFormed C f" and "C \<in> DIV" and "monofun f"
  and "longAdm C P"
  and "P (div_bot C)"
  and "\<And>x. x\<in>C \<Longrightarrow> P x \<Longrightarrow> P (f x)"
  shows "P (lfp C f)"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) longiterate_bot longiterate_induction longiterate_lfp_in by blast


lemma lfp_lfp_below2:
    assumes "monofun g1" 
    and "monofun g2"
    and "goodFormed C1 g1" 
    and "goodFormed C2 g2"
    and "C1 \<in> DIV" 
    and "C2 \<in> DIV"
    and "\<And>x. f (g1 x) \<sqsubseteq> g2 (f x)"
    and "\<And>x. x\<in>C1 \<Longrightarrow> f x \<in>C2"
    and "f (div_bot C1) = div_bot C2"
    and "longAdm C1 (\<lambda>x. f x \<sqsubseteq> (lfp C2 g2))"
  shows "f (lfp C1 g1) \<sqsubseteq> (lfp C2 g2)"
  apply(rule lfp_induction [of "C1" "g1"])
  apply( auto simp add: assms)
   apply (simp add: assms(2) assms(4) assms(6) div_bot lfp_greater)
  by (metis (mono_tags, lifting) assms(2) assms(4) assms(6) assms(7) below_trans lfp_fix monofun_def)



end
