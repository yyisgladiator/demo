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


instance
  apply(intro_classes)
  sorry
end


lemma stream_bot [simp]: "div_bot UNIV = \<epsilon>"
  apply(simp add: div_bot_def)
  by (simp add: bottom_def)

lemma prod_stream_bot[simp]: "(div_bot UNIV) = (\<epsilon>, \<epsilon>)"
  apply(simp add: div_bot_def)
  by (smt below_bottom_iff inst_prod_pcpo minimal the_equality)





definition example:: "(nat stream \<times> nat stream) \<Rightarrow> (nat stream \<times> nat stream)" where
"example  s = ( if (#(fst s)<\<infinity>) then (\<up>0 \<bullet> (fst s), \<epsilon>) else (\<up>0 \<bullet> (fst s) , \<up>0 \<bullet> (snd s)))"

lemma example_mono [simp]: "monofun example"
  apply(rule monofunI)
  apply(auto simp add: example_def monofun_cfun_arg)
  using eq_less_and_fst_inf inf_ub order_less_le by blast

lemma allgood[simp]: "goodFormed UNIV x"
  using goodFormed_def by blast

lemma fixes C::"'a::div_cpo set"
  shows "C\<in>DIV \<Longrightarrow> monofun h \<Longrightarrow> K\<in>C \<Longrightarrow> longAdm C (\<lambda>a. h a \<sqsubseteq> K)"
  apply(auto simp add: longAdm_def)
  oops



lemma ind_adm [simp]: "longAdm UNIV (\<lambda>a. snd a \<noteq> \<up>(Suc 0))"
  apply(auto simp add: longAdm_def)
  apply(rename_tac Y, case_tac "finite Y")
  using lc_finite_lub apply blast
  sorry

lemma "snd (lfp UNIV example) \<noteq> \<up>1"
  apply(rule lfp_induction)
  apply auto
     apply(auto simp add: DIV_prod_def DIV_stream_def)
   apply(simp add: example_def)
   apply(rename_tac a b, case_tac "#a=\<infinity>")
  apply auto
  apply (smt Pair_eqD2 inf_less_eq linorder_not_le prod.collapse stream.con_rews(2) sup'_def up_defined)
  done




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