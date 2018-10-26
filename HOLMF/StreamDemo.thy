theory StreamDemo

imports stream.Streams Instantiation Induction

begin

default_sort div_pcpo


instantiation stream :: (countable) division
begin
definition DIV_stream:: "'a stream set set" where
"DIV_stream = {UNIV}"   

instance
  apply(intro_classes)
  apply (simp add: DIV_stream_def)
  by (simp add: DIV_stream_def)
end



instantiation stream :: (countable) div_pcpo
begin

lemma longchain_eps[simp]:"longChain S \<Longrightarrow> longChain (insert \<epsilon> S)"
  by(auto simp add: longChain_def)

lemma stream_split: "{x \<in> S. #x \<le> Fin (Suc n)} = {x \<in> S. #x \<le> Fin n} \<union> {x \<in> S. #x = Fin (Suc n)}"
  apply auto
  apply (meson leI less2eq less2lnleD)
  by (metis Fin_leq_Suc_leq le_cases less2eq)

lemma stream_lc_one: "longChain S \<Longrightarrow> x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> #x = #y \<Longrightarrow> x=y"
    by (metis longChain_def snth_less snths_eq)

lemma longchain_one_lenght: "longChain S \<Longrightarrow>  finite {x \<in> S. #x = n}"
  sorry
lemma stream_lc_finite: assumes "longChain S"
  shows "finite {x. x\<in>S \<and> #x \<le> Fin n}"
  apply(induction n)
   apply auto
  apply(subst stream_split)
  apply auto
  by (simp add: longchain_one_lenght assms)

lemma stream_lc_infinite: assumes "longChain S" and "infinite S"
  shows "\<exists>x. x\<in>S \<and> Fin n \<le> #x"
proof (rule ccontr)
  assume "\<nexists>x. x \<in> S \<and> Fin n \<le> #x"
  hence as:"\<And> x. x\<in>S \<Longrightarrow> #x \<le> Fin n"
    by auto   
  have "\<And>x y. x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> #x = #y \<Longrightarrow> x=y"
    by (metis assms(1) longChain_def snth_less snths_eq)
  have "S = {x. x\<in>S \<and> #x \<le> Fin n}"
    using as by force
  hence "finite S"
    by (metis (full_types) assms(1) stream_lc_finite)
  thus False
    using assms(2) by auto 
qed

definition getNthElement:: "'a::countable stream set \<Rightarrow> nat \<Rightarrow> 'a stream" where
"getNthElement S n = stake n\<cdot>(SOME x. x\<in>S \<and> Fin n \<le> #x)"

lemma stake_below_2: assumes "n\<le>m" and "s\<sqsubseteq>xs \<or> xs\<sqsubseteq>s" and "Fin n \<le> #s" and "Fin m \<le> #xs"
  shows "stake n\<cdot>s \<sqsubseteq> stake m\<cdot>xs"
  by (smt assms(1) assms(2) assms(3) assms(4) below_trans less2nat slen_stake snth_less snths_eq stream.take_below)

lemma stream_lc2c:  assumes "longChain S" and "infinite S"
  shows "chain (getNthElement S)"
  apply(rule chainI)
  apply(simp add: getNthElement_def)
  apply(rule stake_below_2)
     apply simp
  apply (metis (mono_tags, lifting) assms(1) assms(2) longChain_def mem_Collect_eq someI_ex stream_lc_infinite)
  apply (metis (mono_tags, lifting) assms(1) assms(2) someI stream_lc_infinite)
  by (metis (no_types, lifting) assms(1) assms(2) someI stream_lc_infinite)

lemma stream_lc_n_length: assumes "longChain S" and "infinite S"
  shows "#(getNthElement S n) = Fin n"
  by (metis (no_types, lifting) StreamDemo.getNthElement_def assms(1) assms(2) slen_stake someI_ex stream_lc_infinite)

lemma stream_lc_inf: assumes "longChain S" and "infinite S"
  shows "#(\<Squnion>i. (getNthElement S) i) = \<infinity>"
  by (metis (no_types, lifting) StreamDemo.stream_lc2c StreamDemo.stream_lc_n_length Suc_n_not_le_n assms(1) assms(2) ch2ch_Rep_cfunR contlub_cfun_arg inf_chainl4 is_ub_thelub less2nat_lemma lnle_def lub_eqI lub_finch2)

lemma stream_lc_below: assumes "longChain S" and "infinite S"
  shows "\<exists>x. x\<in>S \<and> (getNthElement S n) \<sqsubseteq> x"
  apply(simp add: getNthElement_def)
  by (metis (mono_tags, lifting) assms(1) assms(2) finite_subset order_refl someI_ex stream.take_below stream_lc_infinite)

lemma assumes "longChain S" and "infinite S"
  shows "# (lub S) = \<infinity>"
  oops
lemma longchain2chain_h: assumes "longChain S" and "infinite S" 
  shows "(range (getNthElement S)) <| lub S"
  apply(rule is_ubI)
  apply auto
  sorry

lemma longchain2chain: assumes "longChain S" and "infinite S" 
  shows "S <<| (\<Squnion>i. (getNthElement S) i)"
  sorry

lemma assumes "longChain S" and "infinite S"
  obtains Y where "chain Y" and "lub S = (\<Squnion>i. Y i)"
  using chain_const by fastforce

instance
  apply(intro_classes)
  apply(auto simp add: DIV_stream_def)
  using longchain2chain by blast
end


definition example:: "(nat stream \<times> nat stream) \<Rightarrow> (nat stream \<times> nat stream)" where
"example  s = ( if (#(fst s)<\<infinity>) then (\<up>0 \<bullet> (fst s), \<epsilon>) else (\<up>0 \<bullet> (fst s) , \<up>0 \<bullet> (snd s)))"

lemma example_mono [simp]: "monofun example"
  apply(rule monofunI)
  apply(auto simp add: example_def monofun_cfun_arg)
  using eq_less_and_fst_inf inf_ub order_less_le by blast

lemma allgood[simp]: "goodFormed UNIV x"
  using goodFormed_def by blast

lemma stream_bot [simp]: "div_bot UNIV = \<epsilon>"
  apply(simp add: div_bot_def)
  by (simp add: bottom_def)

lemma prod_stream_bot[simp]: "(div_bot UNIV) = (\<epsilon>, \<epsilon>)"
  apply(simp add: div_bot_def)
  by (smt below_bottom_iff inst_prod_pcpo minimal the_equality)

lemma fixes C::"'a::div_cpo set"
  shows "C\<in>DIV \<Longrightarrow> monofun h \<Longrightarrow> K\<in>C \<Longrightarrow> longAdm C (\<lambda>a. h a \<sqsubseteq> K)"
  apply(auto simp add: longAdm_def)
  oops

lemma "sdom\<cdot>(snd (lfp UNIV example)) \<subseteq> {0}"
  apply(rule lfp_induction)
       apply auto
     apply(auto simp add: DIV_prod_def DIV_stream_def)
   defer
   apply(auto simp add: example_def)
  apply (smt Fin_02bot Fin_Suc bot_is_0 insert_not_empty leI mk_disjoint_insert notinfI3 only_empty_has_length_0 sconc_snd_empty singleton_insert_inj_eq slen_scons snd_conv srcdups_anotb_h srcdups_dom srcdups_dom_h srcdups_eq srcdups_sconc_duplicates strict_srcdups subset_singletonD)
  apply(auto simp add: longAdm_def)
  using prod_lub
  oops
  


lemma "(lfp UNIV example) \<in> {(s1, s2) | s1 s2. sdom\<cdot>s1 \<subseteq> {0} \<and> sdom\<cdot>s2 \<subseteq>{0}}"
  apply(rule lfp_induction)
       apply auto
     apply(auto simp add: DIV_prod_def DIV_stream_def)
    defer
   apply(auto simp add: example_def)
   apply(auto simp add: longAdm_def)
 
  using prod_div_bot DIV_stream_def 
  using prod_lub
  oops

lemma "lfp UNIV example = (\<up>0\<infinity>, \<up>0\<infinity>)"
  oops


end