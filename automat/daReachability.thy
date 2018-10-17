theory daReachability

imports  dAutomaton
  begin
  
section \<open>reachability\<close>

definition daReach_helper::"('s::type, 'm::message) dAutomaton \<Rightarrow> 'm sbElem set \<Rightarrow> 's set \<Rightarrow> 's set  \<Rightarrow> 's set" where
"daReach_helper da M S_init S = S \<union> { daNextState da s  input | input s. s\<in>(S\<union>S_init) \<and> input\<in>M \<and>
      (ubLen (ubRestrict (daRan da)\<cdot>(ubUp\<cdot>(daNextOutput da s input))) < \<infinity>)}"

definition daReach::"('s::type, 'm::message) dAutomaton \<Rightarrow> 'm sbElem set \<Rightarrow> 's set  \<Rightarrow> 's set" where
"daReach da M S_init = fix\<cdot>(\<Lambda> S. daReach_helper da M S_init S)"


lemma dareach_helper_mono: "monofun (\<lambda>S. daReach_helper da M S_init S)"
  apply(rule monofunI)
  apply(auto simp add: less_set_def)
   by (smt CollectD CollectI SetPcpo.less_set_def Un_iff daReach_helper_def subset_iff)

lemma dareach_helper_cont: "cont (\<lambda>S. daReach_helper da M S_init S)"
  apply(rule contI2)
   apply(simp add: dareach_helper_mono)
  apply (simp add:chain_def)
  apply(auto simp add: less_set_def)
  apply (simp add:lub_eq_Union)
  apply simp
  
  apply (simp add:contlub_cfun_arg)
(*  apply(auto simp add: daReach_helper_def) *)
(*  
  
"chain Y \<Longrightarrow> f\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. f\<cdot>(Y i))"

  apply (simp add:is_lub_rangeD1)
  using tsyn.distinct(1)
*)  
  sorry

lemma daReach_insert: "(daReach da M S_init) = (daReach da M S_init) \<union> { daNextState da s  input | input s. s\<in>((daReach da M S_init)\<union>S_init) \<and> input\<in>M \<and>
        (ubLen (ubRestrict (daRan da)\<cdot>(ubUp\<cdot>(daNextOutput da s input))) < \<infinity>)}"
  apply(subst daReach_def)
  by (metis (no_types) Abs_cfun_inverse2 daReach_def daReach_helper_def dareach_helper_cont fix_eq)


definition daOutReach:: "('s::type, 'm::message)dAutomaton => 'm sbElem set \<Rightarrow> 's set=> 'm SB set" where 
"daOutReach da M S_init = { daNextOutput da s m |s m. s\<in>(daReach da M S_init)  \<and> m\<in>M}"

end