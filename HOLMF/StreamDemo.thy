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

lemma finite_one: "x\<in>S \<Longrightarrow> (\<And>y. y\<in>S \<Longrightarrow> x = y) \<Longrightarrow> finite S"
  by (metis ex_new_if_finitel1 finite.emptyI finite.insertI singletonI)

lemma longchain_one_lenght: "longChain S \<Longrightarrow>  finite {x \<in> S. #x = n}"
  by (smt ex_new_if_finitel1 finite.intros(1) finite_one mem_Collect_eq stream_lc_one)

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


lemma longchain2chain_h: assumes "longChain S" and "infinite S" 
  shows "(range (getNthElement S)) <| lub S"
proof(rule is_ubI)
  fix x
  assume "x\<in>range (local.getNthElement S)"
  obtain s where "s\<in>S" and "x \<sqsubseteq> s"
    by (metis StreamDemo.stream_lc_below \<open>x \<in> range (local.getNthElement S)\<close> assms(1) assms(2) image_iff)
  thus "x \<sqsubseteq> lub S " oops
 
lemma stream_getnth_below: assumes "longChain S" and "infinite S" and "s\<in>S" and "#s = Fin n"
  shows "getNthElement S n \<sqsubseteq> s"
proof -
  have "#(local.getNthElement S n) = Fin n"
    using StreamDemo.stream_lc_n_length assms(1) assms(2) by blast
  then show ?thesis
    by (metis (no_types) StreamDemo.stream_lc_below antisym_conv approxl1 assms(1) assms(2) assms(3) assms(4) longChain_def mono_slen)
qed 

lemma stream_getnth_eq: assumes "longChain S" and "infinite S" and "s\<in>S" and "#s = Fin n"
  shows "getNthElement S n = s"
  by (simp add: assms(1) assms(2) assms(3) assms(4) eq_slen_eq_and_less stream_getnth_below stream_lc_n_length)

lemma longchain2chain_ub: assumes "longChain S" and "infinite S" 
  shows "S <| (\<Squnion>i. (getNthElement S) i)"
proof(rule is_ubI)
  fix x
  assume "x\<in>S"
  show "x \<sqsubseteq> (\<Squnion>i. local.getNthElement S i)"
  proof (cases "#x<\<infinity>")
    case True
    obtain n where "Fin n = #x"
      by (metis True lnat_well_h2)
    hence "getNthElement S n = x"
      by (simp add: \<open>x \<in> S\<close> assms(1) assms(2) stream_getnth_eq)
    then show ?thesis
      using assms(1) assms(2) is_ub_thelub stream_lc2c by blast
    next
      case False
      have "\<And>n. getNthElement S n \<sqsubseteq> x"
        by (metis False StreamDemo.stream_lc_below \<open>x \<in> S\<close> assms(1) assms(2) below_trans eq_less_and_fst_inf inf_ub leD longChain_def neq_iff)
      hence "\<And>n. getNthElement S n = stake n\<cdot>x"
        by (metis approxl1 assms(1) assms(2) stream_lc_n_length)
    then show ?thesis
      by (metis StreamDemo.stream_lc_inf assms(1) assms(2) eq_less_and_fst_inf lub_below stream.take_below stream_lc2c)
  qed
qed

lemma longchain2chain: assumes "longChain S" and "infinite S"
  shows "S <<| (\<Squnion>i. (getNthElement S) i)"
  by (meson StreamDemo.stream_lc2c assms(1) assms(2) below_refl box_below is_lubI is_ub_def longchain2chain_ub lub_below stream_lc_below)

lemma lc2c: assumes "longChain S" and "infinite S"
  shows "lub S = (\<Squnion>i. (getNthElement S) i)"
  using StreamDemo.longchain2chain assms(1) assms(2) lub_eqI by blast

lemma lc_lub_inf: assumes "longChain S" and "infinite S"
  shows "# (lub S) = \<infinity>"
  by (simp add: StreamDemo.lc2c StreamDemo.stream_lc_inf assms(1) assms(2))

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

lemma longAdmI: assumes "\<And>Y. longChain Y \<Longrightarrow> infinite Y \<Longrightarrow> Y \<subseteq> C \<Longrightarrow> (\<And>y. y\<in>Y \<Longrightarrow> P y) \<Longrightarrow> P (lub Y)"
  shows "longAdm C P"
  apply(auto simp add: longAdm_def)
  using assms lc_finite_lub by blast

lemma longAdmI_stream: fixes P::"'a::countable stream \<Rightarrow> bool"
  assumes "adm P"
    shows "longAdm UNIV P"
  apply(rule longAdmI)
  apply auto
  apply(subst lc2c, auto)
  oops

lemma fixes h::"'a::countable stream \<Rightarrow> 'b::countable stream"
  shows " cont h  \<Longrightarrow> longAdm UNIV (\<lambda>a. h a \<sqsubseteq> K)"
  apply(rule longAdmI)
  apply(subst lc2c)
  apply auto
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