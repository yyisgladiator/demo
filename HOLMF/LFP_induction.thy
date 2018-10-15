theory LFP_induction

imports LFP Instantiation

begin




(* similar to iterate, but no longer countable *)
definition longIterate :: "'a::div_pcpo set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
"longIterate C f = lfp (Pow C) (\<lambda> (S::'a set).  insert (div_bot C) (f `S))"

lemma longiterate_mono[simp]: assumes "C\<in>DIV" shows "monofun (\<lambda> (S::'a set).  insert (div_bot C) (f `S))"
  apply(rule monofunI)
  apply(simp add: less_set_def)
  by blast

lemma longiterate_good[simp]: 
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

lemma longiterate_bot[simp]: assumes "C\<in>DIV" and "goodFormed C f"
    shows "div_bot C \<in> (longIterate C f)"
  by(subst longiterate_step, auto simp add: assms)


lemma longiterate_subset: assumes "C\<in>DIV" and "goodFormed C f" shows "longIterate C f \<subseteq> C"
  by (metis (mono_tags, lifting) DIV_set_def PowD assms(1) assms(2) image_eqI lfp_div longIterate_def longiterate_good longiterate_mono)

thm own_zorn3

lemma assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "\<And>K. longChain K \<Longrightarrow> K\<subseteq>(longIterate C f) \<Longrightarrow> \<exists>u\<in>(longIterate C f). \<forall>a\<in>K. a \<sqsubseteq> u"
  oops

  
lemma long_iterate_below_fix: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "longIterate C f \<sqsubseteq> {y. y \<sqsubseteq> f y \<and> y \<in>C}"
  apply(simp add: longIterate_def)
  apply(rule lfp_least, auto simp add: assms DIV_set_def less_set_def)
  using assms(2) assms(3) div_bot goodFormed_def apply blast
  using assms(2) div_bot apply blast
  apply (simp add: assms(1) monofunE)
  using assms(3) goodFormed_def by blast

lemma long_iterate_below_fix_least: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "longIterate C f \<sqsubseteq> {y. y \<sqsubseteq> f y \<and> y \<in> C \<and> (\<forall>x\<in>{x. f x\<sqsubseteq> x \<and> x\<in>C}. y\<sqsubseteq>x)}"
  apply(simp add: longIterate_def)
  apply(rule lfp_least, auto simp add: assms DIV_set_def less_set_def)
  apply(auto simp add: assms div_bot goodFormed_def monofunE)
  using assms(2) assms(3) div_bot goodFormed_def apply blast
  using assms(3) goodFormed_def apply auto[1]
  by (meson assms(1) below_refl box_below monofun_def) 


lemma long_iterate_below_fix2: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "f x\<sqsubseteq> x \<Longrightarrow> x\<in>C \<Longrightarrow> a\<in>longIterate C f \<Longrightarrow> a\<sqsubseteq> x" 
  using long_iterate_below_fix_least apply (auto simp add: assms SetPcpo.less_set_def)
  using assms(1) assms(2) assms(3) by blast

lemma long_iterate_below_fix3: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" 
  shows "a\<in>longIterate C f \<Longrightarrow> a\<sqsubseteq>f a"
  using long_iterate_below_fix_least apply (auto simp add: assms SetPcpo.less_set_def)
  using assms(1) assms(2) assms(3) apply blast+
  done

lemma long_iterate_below_fix4: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" and "x\<in>longIterate C f"
  shows "x\<sqsubseteq>lfp C f"
  apply(rule lfp_greater, auto simp add: assms)
  using assms(1) assms(2) assms(3) assms(4) long_iterate_below_fix2 by fastforce

lemma long_iterate_below_fix5: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" 
  shows "lfp C f \<in> longIterate C f"
  apply(rule ccontr)
  oops

lemma "adm(\<lambda>x. x\<sqsubseteq>U)"
  by simp
lemma "chain K \<Longrightarrow> (\<And>i. K i \<sqsubseteq> U) \<Longrightarrow> ((\<Squnion>i. K i) \<sqsubseteq> U)"
  oops

lemma longiterate_step2: assumes "C\<in>DIV" and "goodFormed C f" 
  and "x \<in> longIterate C f"
shows "f x \<in> longIterate C f"
  using assms longiterate_step by fastforce

(* admissibility/completeness *)
lemma longiterate_subchain: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" 
and "longChain K" and "K\<subseteq>(longIterate C f)" 
shows "lub K \<in> longIterate C f"
proof - 
  have "\<And>k. k\<in>K \<Longrightarrow> k\<sqsubseteq>lfp C f"
    using assms(1) assms(2) assms(3) assms(5) long_iterate_below_fix4 by blast
  moreover have "K \<subseteq> C"
    using assms(2) assms(3) assms(5) longiterate_subset by auto
  ultimately have "lub K \<sqsubseteq> lfp C f"
    using assms(2) assms(4) div_cpo_g holmf_below_iff by blast

 thus ?thesis sorry
qed

lemma longiterate_test: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f" and  "a\<in>(longIterate C f)"
  shows "lfp C f \<in> longIterate C f"
proof - 
  have h1: "\<And>K. longChain K \<Longrightarrow> K\<subseteq>(longIterate C f) \<Longrightarrow> \<exists>u\<in>(longIterate C f). \<forall>a\<in>K. a \<sqsubseteq> u"
    by (metis SetPcpo.less_set_def assms(1) assms(2) assms(3) below_refl div_cpo_g holmf_below_lub longIterate_def longiterate_subchain longiterate_subset rev_below_trans)
  obtain z where "z\<in>(longIterate C f)" and "\<And>a. a\<in>(longIterate C f) \<Longrightarrow> (z\<sqsubseteq>a \<longrightarrow> a=z)" 
    using h1 by (metis assms(4) empty_iff own_zorn3)
  thus ?thesis
    by (smt assms(1) assms(2) assms(3) below_antisym contra_subsetD imageI insert_subset lfp_all long_iterate_below_fix3 long_iterate_below_fix4 longiterate_step longiterate_subset order_refl) 
qed



lemma longiterate_chain: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "longChain (longIterate C f)"
  apply(rule longchainI)
  sorry


lemma longiterate_lfp: assumes "monofun f" and "C\<in>DIV" and "goodFormed C f"
  shows "lfp C f = lub (longIterate C f)"
  apply(rule lfp_least_eq, simp_all add: assms)
  apply (meson assms(1) assms(2) assms(3) div_cpo_g holmf_below_iff long_iterate_below_fix2 longiterate_chain longiterate_subset)
  defer
   apply (simp add: assms(1) assms(2) assms(3) div_cpo_lub_in longiterate_chain longiterate_subset)
  sorry


lemma longiterate_induction: assumes "goodFormed C f" and "C \<in> DIV"
  and "longAdm P"
  and "monofun f"
  and "P (div_bot C)"
  and "\<And>x. x\<in>C \<Longrightarrow> P x \<Longrightarrow> P (f x)"
  and "x\<in>longIterate C f"
shows "P x"
  apply(cases "x = div_bot C")
   apply (simp add: assms(5))
proof (rule ccontr)
  assume "x\<noteq>div_bot C" and "\<not>P x"

  (* y is the smallest element where (P x) is not valid *)
  obtain y where y_in: "y\<in>longIterate C f" and y_p: "\<not>P y" and y_least: "\<And>z. z\<in>longIterate C f \<Longrightarrow>\<not>P z \<Longrightarrow>  y\<sqsubseteq>z" sorry

  let ?C = "{x. x\<in>longIterate C f \<and> x\<sqsubseteq>y \<and> x\<noteq>y}"

  have c_p: "\<And>c. c\<in>?C \<Longrightarrow> P c"
    using below_antisym y_least by fastforce
  have c_bot: "div_bot C \<in> ?C"
    by (smt CollectI assms(1) assms(2) assms(5) div_bot longiterate_bot longiterate_subset set_mp y_in y_p)
  hence c_chain: "longChain ?C"
    by (metis (no_types, lifting) CollectD assms(1) assms(2) assms(4) empty_iff longChain_def longiterate_chain)
  have c_lub: "P (lub ?C)"
    using assms(3) c_chain c_p longAdm_def by auto

  have "lub ?C \<noteq> y \<Longrightarrow> f (lub ?C) = y" sorry

  thus False
    using assms(1) assms(2) assms(4) assms(6) c_chain c_lub longiterate_subchain longiterate_subset y_p by fastforce
qed


lemma lfp_induction: assumes "goodFormed C f" and "C \<in> DIV"
  and "longAdm P"
  and "monofun f"
  and "\<And>x. x\<in>C \<Longrightarrow> bott\<sqsubseteq>x" and "bott\<in>C"
  and "P bott"
  and "\<And>x. x\<in>C \<Longrightarrow> P x \<Longrightarrow> P (f x)"
  shows "P (lfp C f)"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) below_antisym div_bot longiterate_bot longiterate_induction longiterate_test)



end
