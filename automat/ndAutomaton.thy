(* Draft for Non-Deterministic Automaton *)

theory ndAutomaton

imports spec.SPS SpsStep HOLMF.LFP


begin

default_sort type


fun ndaWell::"((('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr) \<Rightarrow> bool " where
"ndaWell (transition, initialState, Discr chIn, Discr chOut) = finite chIn"

(* FYI: Non-deterministic version *)
cpodef ('state::type, 'm::message) ndAutomaton = 
  "{f::(('state \<times>'m sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr. ndaWell f}"
    sorry

setup_lifting type_definition_ndAutomaton

(* ToDo Move this somewhere else. eg prelude *)
setup_lifting type_definition_cfun


lemma nda_rep_cont[simp]: "cont Rep_ndAutomaton"
  by (simp add: cont_Rep_ndAutomaton)




    section \<open>Definitions\<close>

(*
lift_definition ndaTransition :: "('s, 'm::message) ndAutomaton \<rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('s \<times> 'm SB) set rev))" is
"\<lambda>nda. fst (Rep_ndAutomaton nda)"
  by (simp add: cfun_def)
*) 
lift_definition ndaTransition :: "('s, 'm::message) ndAutomaton \<rightarrow> (('s \<times>'m sbElem) \<Rightarrow> (('s \<times> 'm SB) set rev))" is
"\<lambda>nda. fst (Rep_ndAutomaton nda)"
  by (simp add: cfun_def)

lift_definition ndaInitialState :: "('s, 'm::message) ndAutomaton \<rightarrow> ('s \<times> 'm SB) set rev" is
"(\<lambda> nda. fst (snd (Rep_ndAutomaton nda)))"
  by (simp add: cfun_def)

lift_definition ndaDom :: "('s, 'm::message) ndAutomaton \<rightarrow> channel set" is
"(\<lambda> nda. undiscr(fst (snd (snd (Rep_ndAutomaton nda)))))"
  apply (simp add: cfun_def)
  by (smt Cont.contI2 below_ndAutomaton_def discrete_cpo is_ub_thelub monofunI po_eq_conv snd_monofun)

lift_definition ndaRan :: "('s, 'm::message) ndAutomaton \<rightarrow> channel set" is
"(\<lambda> nda. undiscr(snd (snd (snd (Rep_ndAutomaton nda)))))" 
  apply (simp add: cfun_def)
  by (smt Cont.contI2 below_ndAutomaton_def discrete_cpo is_ub_thelub monofunI po_eq_conv snd_monofun)


  (* Only monofun, not cont *)
definition ndaToDo:: "channel set \<Rightarrow> channel set \<Rightarrow> ('s \<times> 'm::message SB) set rev \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> 'm SPS" where
"ndaToDo In Out S \<equiv> \<lambda> h. uspecFlatten In Out 
                (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(h state)) S)"

(* ----------------------------------------------------------------------- *)
 section \<open>Lemma\<close>
(* ----------------------------------------------------------------------- *)
 subsection \<open>ndaDom\<close>

lemma rep_nda_ndawell[simp]: "ndaWell (Rep_ndAutomaton nda)"
  using Rep_ndAutomaton by auto

lemma nddom_finite[simp]:  "finite (ndaDom\<cdot>nda)"
  apply (simp add: ndaDom_def)  
  by (smt Rep_ndAutomaton fst_conv mem_Collect_eq ndaDom.abs_eq 
      ndaDom.rep_eq ndaWell.elims(2) snd_conv undiscr_Discr)

lemma ndatodo_monofun: "monofun (ndaToDo In Out S)" (is "monofun ?f")
proof (rule monofunI)                 
  fix x y :: "'a \<Rightarrow> 'b SPS"
  assume "x \<sqsubseteq> y"
  hence h: "(\<lambda>(state, sb). spsConcOut sb\<cdot>(x state)) \<sqsubseteq> (\<lambda>(state, sb). spsConcOut sb\<cdot>(y state))"
    by (simp add: below_fun_def cont_pref_eq1I) 
  thus "?f x \<sqsubseteq> ?f y" by (metis (no_types) h monofun_def ndaToDo_def uspecflatten_image_monofun)
 qed


lemma ndatodo_monofun2: "monofun (\<lambda> S. uspecFlatten In Out (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(some_h state)) S))"
proof -
  have b0:  "monofun (\<lambda> S. (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(some_h state)) S))"
    by (simp add: image_mono_rev monofunE)
  show ?thesis
    by (metis (no_types, lifting) b0 monofun_def uspecflatten_monofun)
qed

lemma ndatodo_monofun3: "S1 \<sqsubseteq> S2 \<Longrightarrow> h1 \<sqsubseteq> h2 \<Longrightarrow> (ndaToDo In Out S1 h1) \<sqsubseteq> (ndaToDo In Out S2 h2)"
proof -
  assume a1: "h1 \<sqsubseteq> h2"
  assume "S1 \<sqsubseteq> S2"
  then have "uspecFlatten In Out (setrevImage (\<lambda>(a, u). spsConcOut u\<cdot>(h1 a)) S1) \<sqsubseteq> uspecFlatten In Out (setrevImage (\<lambda>(a, u). spsConcOut u\<cdot>(h1 a)) S2)"
    by (metis (no_types) monofun_def ndatodo_monofun2)
  then show ?thesis
    using a1 by (metis (no_types) HOLCF_trans_rules(1) monofun_def ndaToDo_def ndatodo_monofun)
qed



definition ndaHelper2:: "channel set \<Rightarrow> channel set \<Rightarrow> 
  's \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> ('e \<Rightarrow> 'm SPS)" where
"ndaHelper2 In Out s transition \<equiv> \<lambda> h. (\<lambda>e. ndaToDo In Out (transition (s,e)) h)"


lemma ndaHelper2_monofun: "monofun (ndaHelper2 In Out s transition)"
  unfolding ndaHelper2_def
  by (metis (mono_tags, lifting) mono2mono_lambda monofun_def ndaToDo_def ndatodo_monofun)

lemma ndaHelper2_monofun2: "monofun (ndaHelper2 In Out s)"
  unfolding ndaHelper2_def
  apply(rule monofunI)
  apply(auto simp add: below_fun_def)
  by (metis (mono_tags, lifting) monofun_def ndaToDo_def ndatodo_monofun2)

definition nda_h_inner::"('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h_inner nda h \<equiv>  let dom = (ndaDom\<cdot>nda);
                          ran = (ndaRan\<cdot>nda) in 
     (\<lambda>s. spsStep dom ran\<cdot>(ndaHelper2 dom ran s (ndaTransition\<cdot>nda) h))"

lemma nda_h_inner_dom [simp]: "uspecDom\<cdot>(nda_h_inner nda h s) = ndaDom\<cdot>nda"
  unfolding nda_h_inner_def Let_def  by simp

lemma nda_h_inner_ran [simp]: "uspecRan\<cdot>(nda_h_inner nda h s) = ndaRan\<cdot>nda"
  unfolding nda_h_inner_def Let_def by simp

lemma nda_h_inner_monofun: "monofun (nda_h_inner nda)"
  unfolding nda_h_inner_def
  apply(simp only: Let_def)
  apply(rule monofunI)
  by (simp add: fun_belowI monofunE monofun_Rep_cfun2 ndaHelper2_monofun)

lemma ndadom_below_eq:"nda1 \<sqsubseteq> nda2 \<Longrightarrow> ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2"
  apply(simp add: ndaDom.rep_eq)
  by (metis (mono_tags, hide_lams) below_ndAutomaton_def discrete_cpo snd_monofun)


lemma ndaran_below_eq:"nda1 \<sqsubseteq> nda2 \<Longrightarrow> ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  apply(simp add: ndaRan.rep_eq)
  by (metis (mono_tags, hide_lams) below_ndAutomaton_def discrete_cpo snd_monofun)

lemma nda_helper2_h2:"x\<sqsubseteq>y \<Longrightarrow> ndaHelper2 CS1 CS2 xb x xa \<sqsubseteq> ndaHelper2 CS1 CS2 xb y xa"
  by (metis (mono_tags, lifting) below_fun_def monofun_def ndaHelper2_def ndaToDo_def ndatodo_monofun2)

lemma nda_h_inner_monofun2: "monofun (nda_h_inner)"
  unfolding nda_h_inner_def
  apply(simp only: Let_def)
  apply(rule monofunI)
  apply(simp add: ndadom_below_eq ndaran_below_eq)
  apply(auto simp add: below_fun_def)
  using nda_helper2_h2 by (simp add: nda_helper2_h2 monofun_cfun_arg)


(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h nda \<equiv> lfp (SetPcpo.setify (\<lambda>a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))) (nda_h_inner nda)"

lemma nda_inner_good: "goodFormed (SetPcpo.setify (\<lambda>a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))) (nda_h_inner nda)"
  unfolding goodFormed_def 
    unfolding SetPcpo.setify_def
    apply auto
    using USPEC_def by fastforce


(* ToDo: Move to SetPcpo *)
lemma setify_consts: "P\<in>S \<Longrightarrow> (\<lambda>a. P) \<in> SetPcpo.setify (\<lambda>a. S)"
  by (simp add: SetPcpo.setify_def)

lemma nda_h_valid_domain_h:
  "(\<lambda>a::'a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)) \<in> SetPcpo.setify (\<lambda>a::'a. {USPEC In Out |(In::channel set) Out::channel set. True})"
  apply auto
  apply(rule setify_consts)
  by blast

lemma nda_h_valid_domain: "(SetPcpo.setify (\<lambda>a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))) \<in> DIV"
  unfolding DIV_fun_def DIV_uspec_def
  using nda_h_valid_domain_h by fastforce

lemma nda_h_fixpoint:"nda_h nda = nda_h_inner nda (nda_h nda)"
  by (metis (no_types) nddom_finite lfp_fix nda_h_def nda_h_inner_monofun nda_h_valid_domain nda_inner_good)

lemma nda_h_mono:  "monofun nda_h"
  apply(rule monofunI)
  unfolding nda_h_def
  apply(simp add: ndadom_below_eq ndaran_below_eq)
  apply(rule lfp_monofun)
  apply (simp add: monofunE nda_h_inner_monofun2)
      apply (simp_all add: nda_h_inner_monofun nda_inner_good nda_h_valid_domain)
  by (metis (no_types) nda_inner_good ndadom_below_eq ndaran_below_eq)


definition nda_H :: "('s, 'm::message) ndAutomaton \<Rightarrow> 'm SPS" where
"nda_H nda \<equiv> ndaToDo (ndaDom\<cdot>nda)(ndaRan\<cdot>nda) (ndaInitialState\<cdot>nda) (nda_h nda)" 


lemma "cont (\<lambda>nda. fst (Rep_ndAutomaton nda))"
  by simp

lemma nda_H_monofun: "monofun nda_H"
  apply(rule monofunI)
  unfolding nda_H_def
  apply(simp add: ndadom_below_eq ndaran_below_eq)
  apply(rule ndatodo_monofun3)
  apply (simp add: monofun_cfun_arg)
  by (simp add: monofunE nda_h_mono)



lemma nda_belowI: assumes "ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2"
  and "ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  and "ndaInitialState\<cdot>nda1 \<sqsubseteq> ndaInitialState\<cdot>nda2"
  and "ndaTransition\<cdot>nda1 \<sqsubseteq> ndaTransition\<cdot>nda2"
shows "nda1 \<sqsubseteq> nda2"
  apply(auto simp add: below_ndAutomaton_def below_prod_def)
  apply (metis assms(4) ndaTransition.rep_eq)
    apply (metis assms(3) ndaInitialState.rep_eq)
  using assms(1) assms(2) apply(auto simp add: below_discr_def ndaDom.rep_eq ndaRan.rep_eq)
   apply (metis Discr_undiscr)+
  done


end