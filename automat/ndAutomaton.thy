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
   apply (meson finite.emptyI mem_Collect_eq ndaWell.simps)
  apply(rule admI, auto)
  sorry

setup_lifting type_definition_ndAutomaton

(* ToDo Move this somewhere else. eg prelude *)
setup_lifting type_definition_cfun


lemma nda_rep_cont[simp]: "cont Rep_ndAutomaton"
  by (simp add: cont_Rep_ndAutomaton)




(*******************************************************************)
    section \<open>Definitions\<close>
(*******************************************************************)

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

(*
definition creatConstSPS:: "channel set \<Rightarrow> 'm::message SB  \<Rightarrow> 'm SPS" where
"creatConstSPS \<equiv> \<lambda> In sb. createConstUspec (createConstSPF In\<cdot>sb)"
 
*)
definition ndaTodo_h:: "channel set \<Rightarrow> channel set\<Rightarrow>  ('s \<times> 'm::message SB) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow>'m SPS" where
"ndaTodo_h = (\<lambda> In Out (s, sb) h. if (ubLen (ubRestrict Out\<cdot>(ubUp\<cdot>sb)) < \<infinity>) then spsConcOut sb (h s) else
      uspecConstOut In (ubRestrict Out\<cdot>(ubUp\<cdot>sb)))"

  (* Only monofun, not cont *)
definition ndaConcOutFlatten:: "channel set \<Rightarrow> channel set \<Rightarrow> ('s \<times> 'm::message SB) set rev \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> 'm SPS" where
"ndaConcOutFlatten In Out S \<equiv> \<lambda> h. uspecFlatten In Out 
                (setrevImage (\<lambda> (s, sb). ndaTodo_h In Out (s, sb) h) S)"

definition ndaHelper2:: "channel set \<Rightarrow> channel set \<Rightarrow> 
  's \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> ('e \<Rightarrow> 'm SPS)" where
"ndaHelper2 In Out s transition \<equiv> \<lambda> h. (\<lambda>e. ndaConcOutFlatten In Out (transition (s,e)) h)"

definition nda_h_inner::"('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h_inner nda h \<equiv>  let dom = (ndaDom\<cdot>nda);
                          ran = (ndaRan\<cdot>nda) in 
     (\<lambda>s. spsStep_m dom ran (ndaHelper2 dom ran s (ndaTransition\<cdot>nda) h))"

(* Similar to Rum96 *)
definition  nda_h :: "('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h nda \<equiv> lfp (SetPcpo.setify (\<lambda>a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))) (nda_h_inner nda)"

definition nda_H :: "('s, 'm::message) ndAutomaton \<Rightarrow> 'm SPS" where
"nda_H nda \<equiv> ndaConcOutFlatten (ndaDom\<cdot>nda)(ndaRan\<cdot>nda) (ndaInitialState\<cdot>nda) (nda_h nda)"


definition uspecIsStrict :: "('a::ubcl_comp, 'b::ubcl_comp) ufun uspec \<Rightarrow> bool" where
"uspecIsStrict = uspecForall ufIsStrict"


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

lemma ndatodo_h_monofun: "monofun (ndaTodo_h In Out (s, sb))"
proof (rule monofunI)
  fix x::"('a \<Rightarrow> 'b SPS)"
  fix y::"('a \<Rightarrow> 'b SPS)"
  assume a1: "x \<sqsubseteq> y"
  have h: "x s \<sqsubseteq> y s"
    by (meson a1 below_fun_def)
  thus " ndaTodo_h In Out (s, sb) x \<sqsubseteq> ndaTodo_h In Out (s, sb) y"
    apply (simp add: ndaTodo_h_def)
    apply rule
    by (simp add: spsConcOut_def spsconcout_mono monofunE)
qed

lemma ndatodo_h_dom: assumes "\<And> s. uspecDom\<cdot>(H s) = In \<and> uspecRan\<cdot>(H s) = Out"
  shows "uspecDom\<cdot>(ndaTodo_h In Out (s, sb) H) = In"
  apply (simp add: ndaTodo_h_def)
  apply (case_tac "(ubLen (ubRestrict Out\<cdot>(ubUp\<cdot>sb)) < \<infinity>)")
  by (simp_all add: assms)

lemma ndatodo_h_ran: assumes "\<And> s. uspecDom\<cdot>(H s) = In \<and> uspecRan\<cdot>(H s) = Out"
  shows "uspecRan\<cdot>(ndaTodo_h In Out (s, sb) H) = Out"
  apply (simp add: ndaTodo_h_def)
  apply (case_tac "(ubLen (ubRestrict Out\<cdot>(ubUp\<cdot>sb)) < \<infinity>)")
  by (simp_all add: assms ubclDom_ubundle_def)


lemma ndatodo_monofun: "monofun (ndaConcOutFlatten In Out S)" (is "monofun ?f")
proof (rule monofunI)                 
  fix x y :: "'a \<Rightarrow> 'b SPS"
  assume a1: "x \<sqsubseteq> y"
  have h: "(\<lambda>(state, sb). spsConcOut sb (x state)) \<sqsubseteq> (\<lambda>(state, sb). spsConcOut sb (y state))"
  proof (simp add: below_fun_def, rule, rule)
    fix a::'a and b::"'b stream\<^sup>\<Omega>"
    have "x a \<sqsubseteq> y a"
      by (meson a1 fun_below_iff)
    then show "spsConcOut b (x a) \<sqsubseteq> spsConcOut b (y a)"
      apply (simp add: spsConcOut_def)
      by (simp add: monofunE spsconcout_mono)
  qed
  have h3: "(\<lambda>(s::'a, sb::'b stream\<^sup>\<Omega>). ndaTodo_h In Out (s, sb) x) \<sqsubseteq> 
              (\<lambda>(s::'a, sb::'b stream\<^sup>\<Omega>). ndaTodo_h In Out (s, sb) y)"
    by (metis (mono_tags, lifting) a1 below_fun_def case_prod_conv monofunE ndatodo_h_monofun old.prod.exhaust)
  show "?f x \<sqsubseteq> ?f y" 
    apply (simp add: ndaConcOutFlatten_def)
    apply (rule uspecflatten_mono2)
    using h3 setrevimage_mono_obtain2 by blast
 qed


lemma ndatodo_monofun2: "monofun (\<lambda> S. uspecFlatten In Out (setrevImage (\<lambda>(state, sb). spsConcOut sb (some_h state)) S))"
proof -
  have b0:  "monofun (\<lambda> S. (setrevImage (\<lambda>(state, sb). spsConcOut sb (some_h state)) S))"
    by (simp add: image_mono_rev monofunE)
  show ?thesis
    by (metis (no_types, lifting) b0 monofun_def uspecflatten_monofun)
qed

lemma ndatodo_monofun3: "S1 \<sqsubseteq> S2 \<Longrightarrow> h1 \<sqsubseteq> h2 \<Longrightarrow> (ndaConcOutFlatten In Out S1 h1) \<sqsubseteq> (ndaConcOutFlatten In Out S2 h2)"
proof -
  assume a1: "h1 \<sqsubseteq> h2"
  assume a2: "S1 \<sqsubseteq> S2"
  have h1: "(\<lambda>(s::'a, sb::'b stream\<^sup>\<Omega>). ndaTodo_h In Out (s, sb) h1) \<sqsubseteq> 
              (\<lambda>(s::'a, sb::'b stream\<^sup>\<Omega>). ndaTodo_h In Out (s, sb) h2)"
    by (metis (mono_tags, lifting) a1 below_fun_def case_prod_conv monofunE ndatodo_h_monofun old.prod.exhaust)
  have h2: "\<And> ele. ele \<in> inv Rev S2 \<Longrightarrow> ele \<in> inv Rev S1"
    by (meson a2 revBelowNeqSubset subsetCE)
  show ?thesis
    apply (simp add: ndaConcOutFlatten_def)
    apply (rule uspecflatten_mono2)
    by (smt below_fun_def h1 h2 image_eqI inv_rev_rev setrevImage_def setrevimage_mono_obtain3)
qed

(* ToDo: Copy to USPEC *)
lemma uspecflatten_one_h:"({u::('a::ufuncl). (\<exists>Z::'a set. u \<in> Z \<and> (Z \<in> Rep_rev_uspec ` {a::'a uspec. a = uspec \<and> uspecDom\<cdot>a = uspecDom\<cdot>uspec \<and> uspecRan\<cdot>a = uspecRan\<cdot>uspec}))}) 
  = Rep_rev_uspec uspec"
  by blast
lemma uspecflatten_one [simp]: "uspecDom\<cdot>uspec = In \<Longrightarrow> uspecRan\<cdot>uspec = Out \<Longrightarrow> uspecFlatten In Out (Rev {uspec}) = uspec"
  apply(simp add: uspecFlatten_def uspec_set_filter_def setrevFilter_def)
  apply(simp add: Set.filter_def )
  apply(simp add: setflat_insert)
  apply auto
  apply(subst uspecflatten_one_h)
  by (simp add: uspecdom_insert uspecran_insert)
 

lemma ndatodo_dom[simp]: "uspecDom\<cdot>(h s) = In \<Longrightarrow> uspecDom\<cdot>(ndaTodo_h In Out (s,out) h) = In"
  by(simp add: ndaTodo_h_def)

lemma ndatodo_ran[simp]:"uspecRan\<cdot>(h s) = Out \<Longrightarrow> uspecRan\<cdot>(ndaTodo_h In Out (s,out) h) = Out"
  apply(simp add: ndaTodo_h_def)
  by (simp add: ubclDom_ubundle_def)

lemma ndaconout_one[simp]: assumes "uspecDom\<cdot>(h s) = In" and "uspecRan\<cdot>(h s) = Out"
  shows "ndaConcOutFlatten In Out (Rev {(s,out)}) h = ndaTodo_h In Out (s, out) h"
  apply(simp add: ndaConcOutFlatten_def setrevImage_def)
  apply(rule uspecflatten_one)
  by(simp_all add: assms)

lemma ndaconcout_one2[simp]: assumes "uspecDom\<cdot>(h (fst T)) = In" and "uspecRan\<cdot>(h (fst T)) = Out"
  shows "ndaConcOutFlatten In Out (Rev { T }) h = ndaTodo_h In Out T h"
  by (metis assms(1) assms(2) ndaconout_one prod.collapse)

lemma ndaHelper2_monofun: "monofun (ndaHelper2 In Out s transition)"
  unfolding ndaHelper2_def
  by (metis (mono_tags, lifting) mono2mono_lambda monofun_def ndatodo_monofun)

lemma ndaHelper2_monofun2: "monofun (ndaHelper2 In Out s)"
  unfolding ndaHelper2_def
  apply(rule monofunI)
  apply(auto simp add: below_fun_def)
  by (simp add: ndatodo_monofun3)


lemma nda_h_inner_dom [simp]: "uspecDom\<cdot>(nda_h_inner nda h s) = ndaDom\<cdot>nda"
  unfolding nda_h_inner_def Let_def  by simp

lemma nda_h_inner_ran [simp]: "uspecRan\<cdot>(nda_h_inner nda h s) = ndaRan\<cdot>nda"
  unfolding nda_h_inner_def Let_def by simp

lemma nda_h_inner_monofun: "monofun (nda_h_inner nda)"
  unfolding nda_h_inner_def
  apply(simp only: Let_def)
  apply(rule monofunI)
  by (simp add: fun_belowI ndaHelper2_def ndatodo_monofun3 spsStep_mono_2)

lemma ndadom_below_eq:"nda1 \<sqsubseteq> nda2 \<Longrightarrow> ndaDom\<cdot>nda1 = ndaDom\<cdot>nda2"
  apply(simp add: ndaDom.rep_eq)
  by (metis (mono_tags, hide_lams) below_ndAutomaton_def discrete_cpo snd_monofun)


lemma ndaran_below_eq:"nda1 \<sqsubseteq> nda2 \<Longrightarrow> ndaRan\<cdot>nda1 = ndaRan\<cdot>nda2"
  apply(simp add: ndaRan.rep_eq)
  by (metis (mono_tags, hide_lams) below_ndAutomaton_def discrete_cpo snd_monofun)

lemma nda_helper2_h2:"x\<sqsubseteq>y \<Longrightarrow> ndaHelper2 CS1 CS2 xb x xa \<sqsubseteq> ndaHelper2 CS1 CS2 xb y xa"
  apply (simp add: ndaHelper2_def)
  apply (simp add: ndaConcOutFlatten_def)
  by (smt below_fun_def below_refl case_prod_unfold inv_rev_rev pair_imageI prod.collapse revBelowNeqSubset 
      setrevImage_def setrevimage_mono_obtain3 subset_iff uspecflatten_mono2)


lemma nda_h_inner_monofun2: "monofun (nda_h_inner)"
  unfolding nda_h_inner_def
  apply(simp only: Let_def)
  apply(rule monofunI)
  apply(simp add: ndadom_below_eq ndaran_below_eq)
  apply(auto simp add: below_fun_def)
  by (simp add: monofun_cfun_arg nda_helper2_h2 spsStep_mono_2)


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
  by (metis (no_types) lfp_fix nda_h_def nda_h_inner_monofun nda_h_valid_domain nda_inner_good)

lemma nda_h_least: assumes "other_h \<in> SetPcpo.setify (\<lambda>a::'a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))"
  and "nda_h_inner nda other_h \<sqsubseteq> other_h"
  shows "nda_h nda \<sqsubseteq> other_h"
  unfolding nda_h_def
  apply(rule lfp_least)
  using assms nda_h_inner_monofun nda_h_valid_domain nda_inner_good by auto

lemma nda_h_least_eq: assumes "other_h \<in> SetPcpo.setify (\<lambda>a::'a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))"
  and "nda_h_inner nda other_h \<sqsubseteq> other_h"
  and "\<And>x. x\<in>SetPcpo.setify (\<lambda>a::'a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)) \<Longrightarrow> nda_h_inner nda x \<sqsubseteq> x \<Longrightarrow> other_h \<sqsubseteq> x"
  shows "nda_h nda = other_h"
  unfolding nda_h_def
  apply(rule lfp_least_eq)
  using nda_h_inner_monofun apply blast
  using assms nda_h_inner_monofun nda_h_valid_domain nda_inner_good by auto

lemma nda_h_mono:  "monofun nda_h"
  apply(rule monofunI)
  unfolding nda_h_def
  apply(simp add: ndadom_below_eq ndaran_below_eq)
  apply(rule lfp_monofun)
  apply (simp add: monofunE nda_h_inner_monofun2)
      apply (simp_all add: nda_h_inner_monofun nda_inner_good nda_h_valid_domain)
  by (metis (no_types) nda_inner_good ndadom_below_eq ndaran_below_eq)

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

lemma ubcllen_0_not_elemwell: "ubclLen sb = (0::lnat) \<Longrightarrow>  \<not> sbHdElemWell sb"
  by (metis sbHdElemWell_def sbLen_empty_bundle ubclDom_ubundle_def)

lemma sbhdwell_ubconceq: assumes "ubDom\<cdot>(sbe2SB sbe) = ubDom\<cdot>us"
  shows "sbHdElemWell (ubConcEq (sbe2SB sbe)\<cdot>us)"
  apply (simp only: sbHdElemWell_def)
  apply rule
  by (metis (no_types, lifting) assms sbHdElem_bottom_exI sbHdElem_channel sbe2sb_dom sbe2sb_hdelem_conc sbe2sb_nbot ubconceq_dom)

lemma nda_h_final_h_1: assumes "sbeDom sbe = ndaDom\<cdot>nda"
  shows "uspecFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s, sb). ndaTodo_h (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (s, sb) (nda_h nda)) ((ndaTransition\<cdot>nda) (state, sbe))) \<sqsubseteq>
(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state))"
  apply (rule uspec_belowI) 
    apply (metis (no_types, lifting) nda_h_fixpoint nda_h_inner_dom spfConcIn_dom spfConcIn_ran ufclDom_ufun_def ufclRan_ufun_def uspecflatten_dom uspecimage_dom1)
   apply (metis (no_types, lifting) nda_h_fixpoint nda_h_inner_ran spfConcIn_dom spfConcIn_ran ufclDom_ufun_def ufclRan_ufun_def uspecflatten_ran uspecimage_ran1)
proof (rule setrev_belowI)
let ?H  = "(ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda))"
  let ?In = "(ndaDom\<cdot>nda)"
  let ?Out = "(ndaRan\<cdot>nda)"
  let ?transition = "(ndaTransition\<cdot>nda)"

  show "inv Rev (uspecRevSet\<cdot>(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)))
    \<subseteq> inv Rev (uspecRevSet\<cdot>(uspecFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). ndaTodo_h (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (s, sb) (nda_h nda)) ((ndaTransition\<cdot>nda) (state, sbe)))))"
  proof rule
    fix x::"('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun"      
    assume a1: "uspec_in x (uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state))"
    have f1:"uspecRevSet\<cdot>(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)) = 
              (setrevImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (uspecRevSet\<cdot>(nda_h nda state)))"
      apply (rule uspecimage_useful_uspecrevset)
      by (simp add: ufclDom_ufun_def ufclRan_ufun_def)
    obtain y where y_def_1: "uspec_in y (nda_h nda state)" 
      and y_def_2: "x = (Rep_cfun (spfConcIn (sbe2SB sbe))) y"
      by (metis (mono_tags, lifting) a1 f1 setrevimage_mono_obtain3)
    have f2: "uspec_in y ((nda_h_inner nda (nda_h nda)) state)"
      by (metis nda_h_fixpoint y_def_1)
    then have f3: "uspec_in y (spsStep_m ?In ?Out ?H)"
      by (metis nda_h_inner_def)
    obtain f where f_def_1: "f \<in> (inv Rev (spsStep_h\<cdot>?H))" and f_def_2: "spsStep_P ?In ?Out f"
      and "y =  spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f)"
      using f3 nddom_finite spsstep_ele_rev by blast
    then have x_f_eq: "x = (Rep_cfun (spfConcIn (sbe2SB sbe))) (spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f))"
      by (simp add: y_def_2)  

    have "\<And> sbe. uspec_in (f sbe) (?H sbe)"
      by (metis (no_types, lifting) Abs_cfun_inverse2 f_def_1 inv_rev_rev mem_Collect_eq setify_insert spsStep_h_cont spsStep_h_def)

    then have "\<And> sbe. uspec_in (f sbe) ((\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda)) sbe)"
      by (simp add: ndaHelper2_def)
    then have "\<And> sbe. uspec_in (f sbe) (uspecFlatten ?In ?Out (setrevImage (\<lambda>(s, sb). ndaTodo_h ?In ?Out (s, sb) (nda_h nda)) (?transition (state,sbe))))"
      by (simp add: ndaConcOutFlatten_def)
    have "\<And> us. x \<rightleftharpoons> us = (Rep_cfun (spfConcIn (sbe2SB sbe))) (spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f)) \<rightleftharpoons> us"
      using x_f_eq by blast
    then have "\<And> us. (Rep_cfun (spfConcIn (sbe2SB sbe))) (spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f)) \<rightleftharpoons> us = 
          (spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f)) \<rightleftharpoons> (ubConcEq (sbe2SB sbe)\<cdot>us)"
      by (metis (no_types, lifting) option.exhaust_sel spfConcIn_dom spfConcIn_step ubclDom_ubundle_def ubconceq_dom ufdom_2ufundom)
    then have "\<And> us. ubDom\<cdot>us = ?In \<Longrightarrow> (spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f)) \<rightleftharpoons> (ubConcEq (sbe2SB sbe)\<cdot>us) = 
          ((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f) (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>(ubConcEq (sbe2SB sbe)\<cdot>us))))\<rightleftharpoons>(ubConcEq (sbe2SB sbe)\<cdot>us)"
      apply (subst spfstep_step)
      using ubconceq_dom apply blast
      using assms sbhdwell_ubconceq apply fastforce
      using nddom_finite apply blast
       apply (metis (no_types, lifting) assms f_def_2 sbe2sb_hdelem4 sbeDom_def spfRtIn_dom spfRtIn_ran spsStep_P_def)
      by blast
    then have "\<And> us. ubDom\<cdot>us = ?In \<Longrightarrow> (spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) f)) \<rightleftharpoons> (ubConcEq (sbe2SB sbe)\<cdot>us) = 
          (f sbe)\<rightleftharpoons> us"
      by (metis (no_types, lifting) assms sbe2sb_hdelem4 sbe2sb_rt spfRtIn_step)

    have "ufDom\<cdot>x = ?In" 
      by (simp add: x_f_eq)
    have "ufRan\<cdot>x = ?Out" 
      by (simp add: x_f_eq)

    have "\<And> us. ubDom\<cdot>us = ?In \<Longrightarrow> x \<rightleftharpoons> us = (f sbe) \<rightleftharpoons> us"
      using \<open>\<And>us::'a stream\<^sup>\<Omega>. ubDom\<cdot>us = ndaDom\<cdot>(nda::('b, 'a) ndAutomaton) \<Longrightarrow> spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>sbEl::'a sbElem. spfRtIn\<cdot> ((f::'a sbElem \<Rightarrow> 'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>) sbEl)) \<rightleftharpoons> ubConcEq (sbe2SB (sbe::'a sbElem))\<cdot>us = f sbe \<rightleftharpoons> us\<close> x_f_eq by auto
   
    have "\<And> us. ubDom\<cdot>us \<noteq> ?In \<Longrightarrow> x \<rightleftharpoons> us = (ufLeast ?In ?Out) \<rightleftharpoons> us"
      by (metis \<open>ufDom\<cdot> (x::'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>) = ndaDom\<cdot>(nda::('b, 'a) ndAutomaton)\<close> test2 test2_2 ufRestrict_apply)


    show "uspec_in x (uspecFlatten ?In ?Out (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). ndaTodo_h ?In ?Out (s, sb) (nda_h nda)) ((ndaTransition\<cdot>nda) (state, sbe))))"
    proof -
      have "\<forall>u ua. (ufDom\<cdot>u \<noteq> ufDom\<cdot>ua \<or> (\<exists>ub. ubDom\<cdot>(ub::'a stream\<^sup>\<Omega>) = ufDom\<cdot>u \<and> u \<rightleftharpoons> ub \<noteq> ua \<rightleftharpoons> ub)) \<or> u = ua"
        by (meson spf_eq)
      then obtain uu :: "('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun \<Rightarrow> ('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun \<Rightarrow> 'a stream\<^sup>\<Omega>" where
              f1: "\<forall>u ua. (ufDom\<cdot>u \<noteq> ufDom\<cdot>ua \<or> ubDom\<cdot>(uu ua u) = ufDom\<cdot>u \<and> u \<rightleftharpoons> uu ua u \<noteq> ua \<rightleftharpoons> uu ua u) \<or> u = ua"
          by (metis (full_types))
      have "\<forall>x0 x1 x2 x3. (dom (Rep_sbElem (x0::'a sbElem)) \<noteq> x3 \<longrightarrow> (x1 x0::('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun) = ufLeast x3 x2) = (dom (Rep_sbElem x0) = x3 \<or> x1 x0 = ufLeast x3 x2)"
        by auto
      then have "\<forall>C Ca f. spsStep_P C Ca f = (\<forall>s. ufDom\<cdot>(f s) = C \<and> ufRan\<cdot>(f s) = Ca) "
        by (simp add: spsStep_P_def)
      then have f2: "\<forall>s. ufDom\<cdot>(f s) = ndaDom\<cdot>nda \<and> ufRan\<cdot>(f s) = ndaRan\<cdot>nda"
        using f_def_2 by blast
      have f3: "ufDom\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s))) = ndaDom\<cdot>nda"
        using nddom_finite spfstep_dom by blast
      have f4: "ufDom\<cdot>(f sbe) \<noteq> ndaDom\<cdot>nda \<longrightarrow> ufDom\<cdot>(f sbe) = ndaDom\<cdot>nda"
        using f2 by (metis (no_types) ufleast_ufdom)
      have "\<forall>u ua ub. ubDom\<cdot>(u::'a stream\<^sup>\<Omega>) \<noteq> ufDom\<cdot>ua \<or> spfConcIn ub\<cdot>ua \<rightleftharpoons> u = ua \<rightleftharpoons> ubConcEq ub\<cdot>u"
        using spfConcIn_step by blast
      then have f5: "ubDom\<cdot> (uu (spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s)))) (f sbe)) = ufDom\<cdot>(f sbe) \<and> f sbe \<rightleftharpoons> uu (spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s)))) (f sbe) \<noteq> spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s))) \<rightleftharpoons> uu (spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s)))) (f sbe) \<longrightarrow> f sbe \<rightleftharpoons> uu (spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s)))) (f sbe) = spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s))) \<rightleftharpoons> uu (spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s)))) (f sbe)"
        using \<open>\<And>us::'a stream\<^sup>\<Omega>. ubDom\<cdot>us = ndaDom\<cdot>(nda::('b, 'a) ndAutomaton) \<Longrightarrow> (x::'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>) \<rightleftharpoons> us = (f::'a sbElem \<Rightarrow> 'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>) (sbe::'a sbElem) \<rightleftharpoons> us\<close> f4 x_f_eq by auto
      have "ufDom\<cdot>(f sbe) = ufDom\<cdot> (spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s))))"
        using f4 f3 spfConcIn_dom by blast
      then have "f sbe = spfConcIn (sbe2SB sbe)\<cdot> (spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot> (\<lambda>s. spfRtIn\<cdot>(f s)))"
        using f5 f1 by meson
      then show ?thesis
       by (metis \<open>\<And>sbe::'a sbElem. uspec_in ((f::'a sbElem \<Rightarrow> 'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>) sbe) (uspecFlatten (ndaDom\<cdot>(nda::('b, 'a) ndAutomaton)) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). ndaTodo_h (ndaDom\<cdot>nda) ?Out (s, sb) (nda_h nda)) ((ndaTransition\<cdot>nda) (state::'b, sbe))))\<close> x_f_eq)
    qed
  qed
qed


lemma nda_h_final_h_2:assumes "sbeDom sbe = ndaDom\<cdot>nda" and
  nda_h_state_not_empty: "nda_h nda state \<noteq> uspecMax (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)" 
  shows "(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)) \<sqsubseteq>
    ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state, sbe)) (nda_h nda)" 
  apply (rule uspec_belowI)
  apply (metis (no_types, lifting) assms(1) ndaConcOutFlatten_def nda_h_final_h_1 uspecdom_eq uspecflatten_dom)
  apply (metis (no_types, lifting) assms(1) ndaConcOutFlatten_def nda_h_final_h_1 uspecflatten_ran uspecran_eq)
proof (rule setrev_belowI)
  let ?H  = "(ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda))"
  let ?In = "(ndaDom\<cdot>nda)"
  let ?Out = "(ndaRan\<cdot>nda)"
  let ?transition = "(ndaTransition\<cdot>nda)"
  show "inv Rev (uspecRevSet\<cdot>(ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state, sbe)) (nda_h nda)))
    \<subseteq> inv Rev (uspecRevSet\<cdot>(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)))" 
  proof rule
    fix x::"('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun"
    let ?L = " \<lambda> sbe. (ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state, sbe)) (nda_h nda))"
    assume a100: "uspec_in x (?L sbe)"
    obtain Z where "Z \<in> inv Rev (setrevImage (\<lambda> (s, sb). ndaTodo_h ?In ?Out (s, sb) (nda_h nda)) (?transition (state, sbe)))"
        and x_in_Z: "uspec_in x Z"
      by (smt a100 case_prodE2 inv_rev_rev ndaConcOutFlatten_def pair_imageI setrevImage_def setrevimage_mono_obtain3 uspec_bex_triv_one_point2 uspecflatten_elen)

    (* nda_h nda state simplify *)
    have nda_h_2_spsStep_m: "(nda_h nda state) = 
      spsStep_m ?In ?Out (\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))"
      apply (subst nda_h_fixpoint)
      apply (simp add: nda_h_inner_def Let_def)
      by (simp add: ndaHelper2_def)

    (* spsStep properties  *)
    then have ndaConcOutFlatten_not_empty:
      "spsStep_h\<cdot>((\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))) \<noteq>
      Rev {}"
      using nda_h_state_not_empty spsstep_m_not_empty by auto
    have ndaConcOutFlatten_dom: "\<And> sbe. uspecDom\<cdot>(((\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))) sbe) = 
        ?In"
      by (simp add: ndaConcOutFlatten_def)

    have image_in_apply: "\<And> f. uspec_in f  (nda_h nda state) \<Longrightarrow> uspec_in ((Rep_cfun (spfConcIn (sbe2SB sbe))) f) 
            (uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state))"
      apply (rule uspecimage_ele_in)
      by (simp_all add: ufclRan_ufun_def ufclDom_ufun_def)
    have g_spsStep_p: "\<And>g sbe. g \<in> (inv Rev (spsStep_h\<cdot>(\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))))
      \<Longrightarrow> ufclDom\<cdot>(g sbe) = ?In \<and> ufclRan\<cdot>(g sbe) = ?Out"
      by (metis ndaConcOutFlatten_def spsstep_h_ele uspec_allDom uspec_allRan uspecflatten_dom uspecflatten_ran)

    obtain g where g_def_1: "g \<in> (inv Rev (spsStep_h\<cdot>(\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))))" and
      g_def_2: "uspec_in (g sbe) Z" and g_def_3: "x = g sbe"
      using x_in_Z a100 ndaConcOutFlatten_not_empty spsstep_h_ele4 by blast
    have g_dom_ran: "\<And> sbe. ufclDom\<cdot>(g sbe) = ?In \<and> ufclRan\<cdot>(g sbe) = ?Out"
      by (simp add: g_def_1 g_spsStep_p)
    then have g_spsStep_P: "spsStep_P ?In ?Out g"
      by (simp add: spsStep_P_def ufclDom_ufun_def ufclRan_ufun_def)
    have "uspec_in (((\<lambda> h. spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) g))
      ((spsStep_m ?In ?Out (\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))))"
      apply (rule spsstep_m_ele)
      apply (simp_all add: g_def_1)
      by (simp add: g_spsStep_P)
    then have "uspec_in ((Rep_cfun (spfConcIn (sbe2SB sbe))) ((\<lambda> h. spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) g))
      (uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (spsStep_m ?In ?Out (\<lambda>e. ndaConcOutFlatten ?In ?Out (?transition (state,e)) (nda_h nda))))"
      using image_in_apply nda_h_2_spsStep_m by auto
    moreover have "(Rep_cfun (spfConcIn (sbe2SB sbe))) ((\<lambda> h. spfStep ?In ?Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) g) = 
              x "
      apply (rule ufun_eqI)
       apply (metis g_def_3 g_dom_ran nddom_finite spfConcIn_dom spfstep_dom ufclDom_ufun_def)
      apply (simp add: ubclDom_ubundle_def)
      apply (subst spfstep_step)
          apply auto[1]
      using assms(1) sbhdwell_ubconceq apply fastforce
        apply simp
       apply (metis g_dom_ran spfRtIn_dom spfRtIn_ran ufclDom_ufun_def ufclRan_ufun_def)
      by (metis assms(1) g_def_3 sbe2sb_hdelem3 sbe2sb_hdelem_conc sbe2sb_rt spfRtIn_step ubconceq_insert)
    ultimately show " uspec_in x (uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state))"
      by (simp add: nda_h_2_spsStep_m)
  qed
qed


lemma nda_h_final: assumes "sbeDom sbe = ndaDom\<cdot>nda" and
  nda_h_state_not_empty: "nda_h nda state \<noteq> uspecMax (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)"
  shows "spsConcIn (sbe2SB sbe) (nda_h nda state) = 
   ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state,sbe)) (nda_h nda)"
   apply (rule uspec_eqI)  defer
    apply (subst spsconcin_dom)
    apply (metis ndaConcOutFlatten_def nda_h_fixpoint nda_h_inner_dom uspecflatten_dom)
  apply (simp add: assms(1) nda_h_final_h_2 nda_h_state_not_empty spsConcIn_def)
  apply (simp add: spsConcIn_def)
  by (metis (no_types) assms(1) ndaConcOutFlatten_def nda_h_final_h_1 nda_h_final_h_2 nda_h_state_not_empty po_eq_conv)



lemma nda_h_I:
  assumes "sbeDom sbe = ndaDom\<cdot>nda" 
    and "uspecIsConsistent (nda_h nda state)" (* For the proof see "ndaTotal.thy" *)
    and "transitions = (ndaTransition\<cdot>nda) (state,sbe)"
  shows "spsConcIn (sbe2SB sbe) (nda_h nda state) = 
    ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) transitions (nda_h nda)"
  unfolding assms(3)
  apply(rule nda_h_final, simp add: assms)
  by (metis assms(2) uspecmax_consistent uspecmax_dom uspecmax_ran)



lemma nda_h_bottom_h: "uspecIsStrict (spsStep_m (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)
  (ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda)))"
  apply (simp add: uspecIsStrict_def)
  apply (rule uspec_ballI)
  apply (rule ufisstrictI)
proof -
  fix x::"('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun"
  fix sb::"'a stream\<^sup>\<Omega>"
  assume a1: "uspec_in x (spsStep_m (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda)))"
  assume a2: "ubclDom\<cdot>sb = ufDom\<cdot>x"
  assume a3: "ubclLen sb = (0::lnat)"
  obtain y where y_def_1: " y \<in> (inv Rev (spsStep_h\<cdot>(ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda))))"
              and y_def_2: "spsStep_P (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) y"
   and y_def_3: "x = spfStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(y sbEl))"
    using a1 nddom_finite spsstep_ele_rev by blast
  have f1: "\<not> sbHdElemWell sb"
    by (simp add: a3 ubcllen_0_not_elemwell)
  show "x \<rightleftharpoons> sb = ubclLeast (ufRan\<cdot>x)"
    apply (subst y_def_3)
    by (simp add: a2 f1 spfStep_2_spfStep_inj spfStep_inj_def ufleast_apply y_def_3)
qed

lemma nda_h_bottom: "uspecIsStrict (nda_h nda state)"
  by (metis nda_h_bottom_h nda_h_fixpoint nda_h_inner_def)



lemma nda_h_final_back_h_1: "finite In \<Longrightarrow> 
  uspecDom\<cdot>other = In  \<Longrightarrow>
  uspecRan\<cdot>other = Out \<Longrightarrow>
  uspecIsStrict other \<Longrightarrow>
  \<forall> sbe. h sbe \<in> USPEC In Out \<Longrightarrow>
  \<forall> sbe. h sbe \<noteq> uspecMax In Out \<Longrightarrow>
  \<forall> sbe. sbeDom sbe = In \<longrightarrow> (spsConcIn (sbe2SB sbe) other = h sbe)
            \<Longrightarrow> 
      (spsStep_m In Out h \<sqsubseteq> other)"
proof -
  assume a0: "finite In"
  assume a1: "uspecDom\<cdot>other = In"
  assume a2: "uspecRan\<cdot>other = Out"
  assume a4: "uspecIsStrict other"
  assume a5: "\<forall> sbe. h sbe \<in> USPEC In Out"
  assume a6: "\<forall> sbe. h sbe \<noteq> uspecMax In Out"
  assume a3: "\<forall> sbe. sbeDom sbe = In \<longrightarrow>
 (spsConcIn (sbe2SB sbe) other = h sbe)"

  have a3_simp: "\<And> sbe. sbeDom sbe = In \<Longrightarrow>
 (spsConcIn (sbe2SB sbe) other = h sbe)"
    using a3 by blast
  (* dom and ran of other *)
  have other_dom: "\<And> sbe. uspecDom\<cdot>(spsConcIn (sbe2SB sbe) other) = uspecDom\<cdot>other"
    by (simp add: spsconcin_dom)
  have h1: "\<And> sbe. sbeDom sbe = In \<Longrightarrow> uspecDom\<cdot>other = uspecDom\<cdot>(h sbe) \<and> uspecDom\<cdot>other = In"
    apply rule
     apply (metis a3 other_dom)
    by (metis a1)

  have R_sub_L: "inv Rev (uspecRevSet\<cdot>other) \<subseteq> inv Rev (uspecRevSet\<cdot>(spsStep_m In Out h))"
  proof rule
    fix x:: "'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>"
    assume a11: "uspec_in x other"
    have spsStep_h_h_not_empty:"spsStep_h\<cdot>h \<noteq> Rev {}"
      by (metis (no_types, lifting) SetRev.setify_notempty a5 a6 not_uspec_consisten_empty_eq rev_inv_rev spsStep_h_insert uspec_dom uspec_eqI2 uspec_ran uspecmax_consistent uspecmax_dom uspecmax_ran uspecrevset_insert)
    have f8: "\<And>f sbe. f \<in> inv Rev (spsStep_h\<cdot>h) \<Longrightarrow> uspec_in (f sbe) (h sbe)"
      by (simp add: spsstep_h_ele)
    then have elem_h_spsStep_P: "\<And>f. f \<in> inv Rev (spsStep_h\<cdot>h) \<Longrightarrow> spsStep_P In Out f"
      by (metis (no_types, hide_lams) a5 spsStep_P_def ufclDom_ufun_def ufclRan_ufun_def uspec_allDom uspec_allRan uspec_dom uspec_ran)
   
    
    have f9: "\<And> sbe. uspec_in (spfConcIn (sbe2SB sbe)\<cdot>x) (spsConcIn (sbe2SB sbe) other)"
      by (simp add: a11 spsconcin_ele)
    then have f10: "\<And> sbe. sbeDom sbe = In \<Longrightarrow> uspec_in (spfConcIn (sbe2SB sbe)\<cdot>x) (h sbe)"
      by (metis a3)
    then have f101: "\<And> sbe. sbeDom sbe = In \<Longrightarrow> 
      \<exists> g \<in> inv Rev (spsStep_h\<cdot>h). g sbe = (spfConcIn (sbe2SB sbe)\<cdot>x)"
      by (simp add: spsStep_h_h_not_empty spsstep_h_ele4)


    have f11: "\<And> f sbe. sbeDom sbe = In \<Longrightarrow> f \<in> inv Rev (spsStep_h\<cdot>h) 
      \<Longrightarrow> uspec_in (f sbe) (h sbe)"
      by (simp add: spsstep_h_ele)
    then have f12: "\<And> f sbe. sbeDom sbe = In \<Longrightarrow> f \<in> inv Rev (spsStep_h\<cdot>h) 
      \<Longrightarrow> uspec_in (f sbe) (spsConcIn (sbe2SB sbe) other)"
      by (simp add: a3)
    have f13: "\<And>f sbe. sbeDom sbe = In \<Longrightarrow> uspec_in f (spsConcIn (sbe2SB sbe) other)
      \<Longrightarrow> \<exists> g \<in> inv Rev (spsStep_h\<cdot>h). g sbe = f"
      by (simp add: a3 spsStep_h_h_not_empty spsstep_h_ele4)
    obtain the_g where the_g_def: "the_g \<equiv> (\<lambda> sbe. if (sbeDom sbe = In) 
      then (spfConcIn (sbe2SB sbe)\<cdot>x) else (SOME f. uspec_in f (h sbe)))"
      by simp
    have the_g_in_h: "the_g \<in> inv Rev (spsStep_h\<cdot>h)"
      by (metis f10 someI_ex spsStep_h_h_not_empty spsstep_h_ele2 spsstep_h_inI the_g_def)
    have the_g_spsStep_P: "spsStep_P In Out the_g"
      by (simp add: elem_h_spsStep_P the_g_in_h)

    have the_g_spsStep: "uspec_in ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) the_g) (spsStep_m In Out h)"
      apply (rule spsstep_m_ele)
        apply (simp add: a0)
       apply (simp add: the_g_in_h)
      by (simp add: the_g_spsStep_P)

    let ?spfStep_g = "((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) the_g)"
    have spfStep_g_ufisstrict: "ufIsStrict ?spfStep_g"
      unfolding ufIsStrict_def
      apply (simp add: a0)
      by (simp add: a0 spfStep_2_spfStep_inj spfStep_inj_def ubcllen_0_not_elemwell ufleast_apply)

    have "\<And>x. uspec_in x other \<Longrightarrow> ufIsStrict x"
      by (metis a4 setrevForall_def uspecForall_def uspecIsStrict_def)

    then have x_ufisstrict: "ufIsStrict x"
      by (simp add: a11)

    have bla: "\<And> xa. \<not> sbHdElemWell xa  \<Longrightarrow> ubclLen xa = 0"
      apply (simp add: ubclLen_ubundle_def)
      apply (simp add: sbHdElemWell_def)
      by (metis strict_slen ublen_not_0 usclLen_stream_def)
    have x_dom_ran: "ufDom\<cdot>x = In \<and> ufRan\<cdot>x = Out"
      by (metis a1 a11 a2 ufclDom_ufun_def ufclRan_ufun_def uspec_allDom uspec_allRan)
    have spfStep_g_strict_apply: "\<And> xa. \<not> sbHdElemWell xa \<Longrightarrow> ubclDom\<cdot>xa = In \<Longrightarrow> ?spfStep_g \<rightleftharpoons> xa = ubclLeast Out"
      by (simp add: a0 spfStep_2_spfStep_inj spfStep_inj_def ufleast_apply)

    have x_strict_apply: "\<And> xa. \<not> sbHdElemWell xa \<Longrightarrow> ubclDom\<cdot>xa = In \<Longrightarrow> x \<rightleftharpoons> xa = ubclLeast Out"
      using bla ufIsStrict_def x_dom_ran x_ufisstrict by blast
    have helper: "\<And>xa::'a stream\<^sup>\<Omega>. ubclDom\<cdot>xa = In \<Longrightarrow> sbHdElemWell xa 
      \<Longrightarrow> the_g (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa))) \<rightleftharpoons> sbRt\<cdot>xa = x \<rightleftharpoons> xa"
    proof -
      fix xa::"'a stream\<^sup>\<Omega>"
      assume a22: "ubclDom\<cdot>xa = In" 
      assume a23: "sbHdElemWell xa"
      let ?da_hd = "(Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))"
      have h1: "dom (sbHdElem\<cdot>xa) = In"
        apply (simp add: sbhdelem_insert)
        by (metis a22 ubclDom_ubundle_def)
      then have h2: "dom (inv convDiscrUp (sbHdElem\<cdot>xa)) = In"
        by (metis UNIV_I a23 convDiscrUp_dom convDiscrUp_inj inv_into_f_f sbHdElemWell_inv_ex)
      have h3: "sbElemWell (inv convDiscrUp (sbHdElem\<cdot>xa))"
        by (meson a23 sbHdElemWell_def sbHdElem_sbElemWell)
      then have h4: "sbeDom (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa))) = In"
        apply (simp add: sbeDom_def)
        apply (simp add: Abs_sbElem_inverse)
        by (simp add: \<open>dom (inv convDiscrUp (sbHdElem\<cdot>(xa::'a stream\<^sup>\<Omega>))) = (In::channel set)\<close>)
      have da_hd_sub: "sbe2SB ?da_hd = ubHd\<cdot>xa"
      proof -
        have h5: "\<And>c. c \<in> In \<Longrightarrow> (\<lambda>c. (c \<in> ubDom\<cdot>xa)\<leadsto>lshd\<cdot>(xa  .  c))\<rightharpoonup>c =
          lshd\<cdot>(xa  .  c)"
          by (metis (mono_tags, lifting) a22 option.sel ubclDom_ubundle_def)
        have h6: "ubDom\<cdot>xa = In"
          by (metis a22 ubclDom_ubundle_def)
        have h7: "\<And> c. c \<in> In \<Longrightarrow> xa  .  c \<noteq> \<epsilon>"
          by (metis (full_types) a23 h6 sbHdElemWell_def)
        have h8: "\<And>c::channel. c \<in> In \<Longrightarrow> 
          updis (inv Discr (inv Iup (lshd\<cdot>(xa  .  c)))) && \<epsilon> = stake (Suc (0::nat))\<cdot>(xa  .  c)"
        proof -
          fix c:: channel
          assume a30: "c \<in> In"
          obtain daEle rtSt where da_conc: "xa . c = \<up>daEle \<bullet> rtSt"
            by (metis a30 h7 surj_scons)
          show "updis (inv Discr (inv Iup (lshd\<cdot>(xa  .  c)))) && \<epsilon> = stake (Suc (0::nat))\<cdot>(xa  .  c)"
            apply (simp add: da_conc)
            by (metis (no_types, hide_lams) Abs_cfun_inverse2 cont_discrete_cpo discr.exhaust iup_inv_iup sup'_def surj_def surj_f_inv_f up_def)
        qed
        show ?thesis
          apply (rule ub_eq)
           apply (metis a22 h4 sbe2sb_dom ubclDom_ubundle_def ubhd_ubdom)
          apply (simp add: h4)   
          apply (simp add: sbe2SB_def)
          apply (subst ubgetch_ubrep_eq)
           apply (smt domIff id_apply sbe2SB.rep_eq ubWell_def ubrep_well)
          apply (simp add: h4)
          apply (simp add: h3 Abs_sbElem_inverse)
          apply (simp add: ubHd_def ubTake_def)
          apply (subst ubMapStream_ubGetCh)
            apply (simp add: usclTake_well)
           apply (metis a22 ubclDom_ubundle_def)
          apply (subst convDiscrUp_inv_subst)
            apply (metis a22 a23 h1 sbHdElemWell_def sbHdElem_channel ubclDom_ubundle_def)
          using h1 apply auto[1]
          apply (simp add: sbhdelem_insert)
          apply (simp add: h6)
          apply (simp add: sup'_def usclTake_stream_def)
          by (simp add: h8)
      qed
      have h7: "xa = ubConc (ubHd\<cdot>xa)\<cdot>(sbRt\<cdot>xa)" (is "xa = ?R")
      proof(rule ub_eq)
        show f0: "ubDom\<cdot>xa = ubDom\<cdot>(?R)" by simp
        fix x :: "'a\<^sup>\<Omega>"
        fix c
        assume a0: "c\<in>ubDom\<cdot>xa" 
        show "xa  .  c = (ubConc (ubHd\<cdot>xa)\<cdot>(sbRt\<cdot>xa) ) .  c"
          apply(subst ubConc_usclConc_eq)
              using ubhd_ubdom a0 apply auto[1]
               using sbrt_sbdom a0 apply auto[1]
        proof -
            have f1: "c\<in>ubDom\<cdot>(ubConc (ubHd\<cdot>xa)\<cdot>(sbRt\<cdot>xa))" 
              using a0 f0 by blast
            have f2: "c\<in>ubDom\<cdot>(ubHd\<cdot>xa)" 
              by (simp add: a0)
            have f3: "c\<in>ubDom\<cdot>(ubRt\<cdot>xa)"
              by (simp add: a0)
            show "xa  .  c = usclConc (ubHd\<cdot>xa  .  c)\<cdot>(sbRt\<cdot>xa  .  c)" 
              apply (simp add: ubHd_def sbRt_def)
              apply (simp add: ubTake_def sbDrop_def)
            proof -
              have f1: "\<And>c s n. \<not> usclOkay c (s::'a stream) \<or> usclOkay c (sdrop n\<cdot>s)"
                by (metis usclDrop_stream_def usclDrop_well)
              have f2: "\<And>c s n. \<not> usclOkay c (s::'a stream) \<or> usclOkay c (stake n\<cdot>s)"
                by (metis usclTake_stream_def usclTake_well)
              obtain cc :: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> channel" and ss :: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> 'a stream" where
                f3: "\<And>c u f ca ua. (c \<notin> ubDom\<cdot>u \<or> usclOkay (cc f) (ss f) \<or> ubMapStream f u . c = f (u . c)) \<and> (\<not> usclOkay (cc f) (f (ss f)) \<or> ca \<notin> ubDom\<cdot>ua \<or> ubMapStream f ua . ca = f (ua . ca))"
                by (metis ubMapStream_ubGetCh)
              then have f4: "\<And>c u f. c \<notin> ubDom\<cdot>u \<or> \<not> usclOkay (cc f) (f (ss f)) \<or> Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>u)\<leadsto>f (u . c)) . c = f (u . c)"
                by (simp add: ubMapStream_def)
              have f5: "\<And>f. usclOkay (cc f) (ss f) \<or> Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>xa)\<leadsto>f (xa . c)) . c = f (xa . c)"
                using f3 by (simp add: a0 ubMapStream_def)
              then have f6: "\<And>n. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>xa)\<leadsto>sdrop n\<cdot>(xa . c)) . c = sdrop n\<cdot>(xa . c)"
                using f4 f1 a0 by blast
              have "\<And>n. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>xa)\<leadsto>stake n\<cdot>(xa . c)) . c = stake n\<cdot>(xa . c)"
                using f5 f4 f2 a0 by blast
              then show "xa . c = usclConc (ubMapStream (Rep_cfun (usclTake (Suc 0))) xa . c)\<cdot> (sbMapStream (Rep_cfun (sdrop (Suc 0))) xa . c)"
                using f6 by (simp add: sbMapStream_def ubMapStream_def usclConc_stream_def usclTake_stream_def)
            qed
          qed
        qed
      show "the_g (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa))) \<rightleftharpoons> sbRt\<cdot>xa = x \<rightleftharpoons> xa"
        apply (simp add: the_g_def h4)
        apply (simp add: da_hd_sub)
        apply (subst spfConcIn_step)
         apply (metis a22 sbrt_sbdom ubclDom_ubundle_def x_dom_ran)
        apply (simp)
        using h7 by auto
    qed
    have "?spfStep_g = x"
      apply (rule ufun_eqI)
       apply (simp_all add: a0)
       apply (metis a1 a11 ufclDom_ufun_def uspec_allDom)
      apply (case_tac "sbHdElemWell xa") defer
       apply (simp add: spfStep_g_strict_apply x_strict_apply)
      apply (subst spfstep_step)
          apply (simp add: ubclDom_ubundle_def)
         apply (simp_all add: a0)
       apply (metis spsStep_P_def the_g_spsStep_P)
      by (simp add: helper)

    then show "uspec_in x (spsStep_m In Out h)"
      using the_g_spsStep by auto
  qed

  show "(spsStep_m In Out h \<sqsubseteq> other)"
    by (metis R_sub_L a0 a1 a2 revBelowNeqSubset spstep_m_dom spstep_m_ran uspec_belowI)
qed


lemma nda_h_final_back_h_2: "(spsStep_m In Out h = other)
 \<Longrightarrow> \<forall> sbe. sbeDom sbe = In \<longrightarrow>
 (uspecIsStrict other \<and> h sbe \<in> USPEC In Out \<and> spsConcIn (sbe2SB sbe) other = h sbe)"
  sorry


lemma nda_h_final_back_eq_h: "(\<forall> sbe. sbeDom sbe = In \<longrightarrow>
 (uspecIsStrict other \<and> h sbe \<in> USPEC In Out \<and> spsConcIn (sbe2SB sbe) other = h sbe))
            \<longleftrightarrow> 
      (spsStep_m In Out h = other)"
  sorry


(* This is the version used for "ndaTotal" *)
(* Annika needs a different lemma with equality, that "nda_h nda = other" *)
lemma nda_h_final_back: assumes "\<And>state sbe. sbeDom sbe = ndaDom\<cdot>nda \<Longrightarrow> 
spsConcIn (sbe2SB sbe) (other state) = 
  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state,sbe)) (other)"
  and "\<And> state. uspecIsStrict (other state)"
  and "\<And> state. uspecDom\<cdot>(other state) = ndaDom\<cdot>nda" 
  and "\<And> state. uspecRan\<cdot>(other state) = ndaRan\<cdot>nda"
shows "nda_h nda \<sqsubseteq> other" 
  apply(rule nda_h_least) 
  apply(simp only: USPEC_def SetPcpo.setify_def)
  using assms(2) assms(3) apply auto[1]
    apply (simp_all add: assms(4))
  apply (simp add: nda_h_inner_def Let_def)
  apply (simp add: below_fun_def)
  apply rule
  apply (simp add: ndaHelper2_def)
proof -
  fix x::'a
  have "spsStep_m (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (\<lambda>e::'b sbElem. ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (x, e)) other) 
        \<sqsubseteq> other x"
    apply (rule nda_h_final_back_h_1)
    apply (simp_all add: assms)
    apply rule 
     apply (metis (mono_tags, hide_lams) ndaHelper2_def nda_h_final_back_h_2 uspec_ran)
    apply rule
    unfolding ndaConcOutFlatten_def
    sorry
  then show "spsStep_m (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (\<lambda>e::'b sbElem. ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (x, e)) other) 
          \<sqsubseteq> other x"
    by simp
qed








lemma nda_h_final_back_eq: assumes "\<And>state sbe. sbeDom sbe = ndaDom\<cdot>nda \<Longrightarrow> 
spsConcIn (sbe2SB sbe) (other state) = 
  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state,sbe)) (other)"
  and "\<And> state. uspecIsStrict (other state)"
  and "\<And> state. uspecDom\<cdot>(other state) = ndaDom\<cdot>nda" 
  and "\<And> state. uspecRan\<cdot>(other state) = ndaRan\<cdot>nda"

  and "\<And>x state sbe. uspecIsStrict (x state) \<Longrightarrow> uspecDom\<cdot>(x state) = ndaDom\<cdot>nda \<Longrightarrow> uspecRan\<cdot>(x state) = ndaRan\<cdot>nda
    \<Longrightarrow> sbeDom sbe = ndaDom\<cdot>nda \<Longrightarrow> spsConcIn (sbe2SB sbe) (x state) =  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state,sbe)) (x)
    \<Longrightarrow> other \<sqsubseteq> x"
shows "nda_h nda = other" 
proof -
  have "nda_h nda\<sqsubseteq>other"
    by (simp add: assms(1) assms(2) assms(3) assms(4) nda_h_final_back) 
  moreover have "other \<sqsubseteq> nda_h nda"
    by (smt assms(5) fun_belowI ndaHelper2_def nda_h_final_back_eq_h nda_h_fixpoint nda_h_inner_def nda_h_inner_dom nda_h_inner_ran not_below2not_eq)
  ultimately show ?thesis
    by (simp add: po_eq_conv) 
qed


end