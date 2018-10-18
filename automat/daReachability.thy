theory daReachability

imports  dAutomaton
  begin
  
section \<open>Definitions\<close>

(* Given an automaton, a set of sbElem, the initial state, the set of states to be considered
  and it returns the set of all reachable states *)
definition daReach_helper::"('s::type, 'm::message) dAutomaton \<Rightarrow> 'm sbElem set \<Rightarrow> 's set \<Rightarrow> 's set  \<Rightarrow> 's set" where
"daReach_helper da M S_init S = S \<union> { daNextState da s  input | input s. s\<in>(S\<union>S_init) \<and> input\<in>M \<and>
      (ubLen (ubRestrict (daRan da)\<cdot>(ubUp\<cdot>(daNextOutput da s input))) < \<infinity>)}"

(* Given an automaton, a set of sbElem, the initial state,
  and it returns the set of all reachable states,
  calls daReach_helper*)
definition daReach_h::"('s::type, 'm::message) dAutomaton \<Rightarrow> 'm sbElem set \<Rightarrow> 's set  \<Rightarrow> 's set" where
"daReach_h da M S_init = fix\<cdot>(\<Lambda> S. daReach_helper da M S_init S)"

(* Returns all reachable states from the initial state *)
definition daReach::"('s::type, 'm::message) dAutomaton  \<Rightarrow> 's set" where
"daReach da = daReach_h da {sbe | sbe. (sbeDom sbe = daDom da)} {daInitialState da}"



(* Given an automaton, a set of sbElem, the initial state,
  and it returns the set of all outputs that can be produced by reachable states *)
definition daOutReach_h:: "('s::type, 'm::message)dAutomaton => 'm sbElem set \<Rightarrow> 's set=> 'm SB set" where 
"daOutReach_h da M S_init = { daNextOutput da s m |s m. s\<in>(daReach_h da M S_init)  \<and> m\<in>M}"


(* Returns all possible outputs from the initial state *)
definition daOutReach:: "('s::type, 'm::message)dAutomaton => 'm SB set" where
"daOutReach da  = daOutReach_h da {sbe | sbe. (sbeDom sbe = daDom da)} {daInitialState da}"




section \<open>Lemma\<close>

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
  by(auto simp add: daReach_helper_def)


lemma daReach_insert: "(daReach_h da M S_init) = (daReach_h da M S_init) \<union> { daNextState da s  input | input s. s\<in>((daReach_h da M S_init)\<union>S_init) \<and> input\<in>M \<and>
        (ubLen (ubRestrict (daRan da)\<cdot>(ubUp\<cdot>(daNextOutput da s input))) < \<infinity>)}"
  apply(subst daReach_h_def)
  by (metis (no_types) Abs_cfun_inverse2 daReach_h_def daReach_helper_def dareach_helper_cont fix_eq)




(* The output of the SPF contains only messages that are also in "daOutReach" *)

(* use this for induction *)
lemma assumes "c\<in>daDom da" and "ubDom\<cdot>ub = daDom da"
  shows "sdom\<cdot>(((da_h da state) \<rightleftharpoons> ub) . c) 
    \<subseteq> \<Union>{sdom\<cdot>(outBundle . c) | outBundle. outBundle \<in> (daOutReach_h da {sbe | sbe. (sbeDom sbe = daDom da)} {state})}"
  oops

(* final proof *)
lemma assumes "c\<in>daDom da" and "state \<in> daReach da" and "ubDom\<cdot>ub = daDom da"
  shows "sdom\<cdot>(((da_h da state) \<rightleftharpoons> ub) . c) \<subseteq> \<Union>{sdom\<cdot>(outBundle . c) | outBundle. outBundle \<in> daOutReach da}"
  oops


end