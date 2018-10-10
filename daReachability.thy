theory daReachability

imports automat.ndAutomaton automat.dAutomaton bundle.tsynBundle
  begin
  
section \<open>reachability\<close>

definition daReach_helper::"('s::type, 'm::message) dAutomaton \<Rightarrow> 'm sbElem set \<Rightarrow> 's set \<Rightarrow> 's set  \<Rightarrow> 's set" where
"daReach_helper da M S_init S = S \<union> { daNextState da s  input | input s. s\<in>(S\<union>S_init) \<and> input\<in>M \<and>
       ubLen(daNextOutput da s input)<\<infinity> \<and> daRan da \<subseteq> ubDom\<cdot>(daNextOutput da s input)}"

definition daReach::"('s::type, 'm::message) dAutomaton \<Rightarrow> 'm sbElem set \<Rightarrow> 's set  \<Rightarrow> 's set" where
"daReach da M S_init = fix\<cdot>(\<Lambda> S. daReach_helper da M S_init S)"

lemma dareach_helper_cont: "cont (\<lambda>S. daReach_helper da M S_init S)"
  apply(rule contI2)
   apply(rule monofunI)
  apply(auto simp add: less_set_def)
   apply (smt CollectD CollectI SetPcpo.less_set_def Un_iff daReach_helper_def subset_iff)
(*  apply(auto simp add: daReach_helper_def) *)
  (*using counterElem_get_i.simps counterelemin_i_i_id
  by (metis tsyn.distinct(1)) *)
  sorry

lemma daReach_insert: "(daReach da M S_init) = (daReach da M S_init) \<union> { daNextState da s  input | input s. s\<in>((daReach da M S_init)\<union>S_init) \<and> input\<in>M \<and>
       ubLen(daNextOutput da s input)<\<infinity> \<and> daRan da \<subseteq> ubDom\<cdot>(daNextOutput da s input)}"
  apply(subst daReach_def)
  by (metis (no_types) Abs_cfun_inverse2 daReach_def daReach_helper_def dareach_helper_cont fix_eq)


definition daOutReach:: "('s::type, 'm::message)dAutomaton => 'm sbElem set \<Rightarrow> 's set=> 'm SB set" where 
"daOutReach da M S_init = { daNextOutput da s m |s m. s\<in>(daReach da M S_init)  \<and> m\<in>M}"

end