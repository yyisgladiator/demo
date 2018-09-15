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


  (* Only monofun, not cont *)
definition ndaConcOutFlatten:: "channel set \<Rightarrow> channel set \<Rightarrow> ('s \<times> 'm::message SB) set rev \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> 'm SPS" where
"ndaConcOutFlatten In Out S \<equiv> \<lambda> h. uspecFlatten In Out 
                (setrevImage (\<lambda>(s, sb). spsConcOut sb\<cdot>(h s)) S)"

definition ndaHelper2:: "channel set \<Rightarrow> channel set \<Rightarrow> 
  's \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> ('e \<Rightarrow> 'm SPS)" where
"ndaHelper2 In Out s transition \<equiv> \<lambda> h. (\<lambda>e. ndaConcOutFlatten In Out (transition (s,e)) h)"

definition nda_h_inner::"('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h_inner nda h \<equiv>  let dom = (ndaDom\<cdot>nda);
                          ran = (ndaRan\<cdot>nda) in 
     (\<lambda>s. spsStep dom ran\<cdot>(ndaHelper2 dom ran s (ndaTransition\<cdot>nda) h))"

(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h nda \<equiv> lfp (SetPcpo.setify (\<lambda>a. USPEC (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))) (nda_h_inner nda)"

definition nda_H :: "('s, 'm::message) ndAutomaton \<Rightarrow> 'm SPS" where
"nda_H nda \<equiv> ndaConcOutFlatten (ndaDom\<cdot>nda)(ndaRan\<cdot>nda) (ndaInitialState\<cdot>nda) (nda_h nda)"


definition uspecIsStrict :: "('a::ubcl_comp, 'a) ufun uspec \<Rightarrow> bool" where
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

lemma ndatodo_monofun: "monofun (ndaConcOutFlatten In Out S)" (is "monofun ?f")
proof (rule monofunI)                 
  fix x y :: "'a \<Rightarrow> 'b SPS"
  assume "x \<sqsubseteq> y"
  hence h: "(\<lambda>(state, sb). spsConcOut sb\<cdot>(x state)) \<sqsubseteq> (\<lambda>(state, sb). spsConcOut sb\<cdot>(y state))"
    by (simp add: below_fun_def cont_pref_eq1I) 
  thus "?f x \<sqsubseteq> ?f y" by (metis (no_types) h monofun_def ndaConcOutFlatten_def uspecflatten_image_monofun)
 qed


lemma ndatodo_monofun2: "monofun (\<lambda> S. uspecFlatten In Out (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(some_h state)) S))"
proof -
  have b0:  "monofun (\<lambda> S. (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(some_h state)) S))"
    by (simp add: image_mono_rev monofunE)
  show ?thesis
    by (metis (no_types, lifting) b0 monofun_def uspecflatten_monofun)
qed

lemma ndatodo_monofun3: "S1 \<sqsubseteq> S2 \<Longrightarrow> h1 \<sqsubseteq> h2 \<Longrightarrow> (ndaConcOutFlatten In Out S1 h1) \<sqsubseteq> (ndaConcOutFlatten In Out S2 h2)"
proof -
  assume a1: "h1 \<sqsubseteq> h2"
  assume "S1 \<sqsubseteq> S2"
  then have "uspecFlatten In Out (setrevImage (\<lambda>(a, u). spsConcOut u\<cdot>(h1 a)) S1) \<sqsubseteq> uspecFlatten In Out (setrevImage (\<lambda>(a, u). spsConcOut u\<cdot>(h1 a)) S2)"
    by (metis (no_types) monofun_def ndatodo_monofun2)
  then show ?thesis
    using a1 by (metis (no_types) HOLCF_trans_rules(1) monofun_def ndaConcOutFlatten_def ndatodo_monofun)
qed





lemma ndaHelper2_monofun: "monofun (ndaHelper2 In Out s transition)"
  unfolding ndaHelper2_def
  by (metis (mono_tags, lifting) mono2mono_lambda monofun_def ndaConcOutFlatten_def ndatodo_monofun)

lemma ndaHelper2_monofun2: "monofun (ndaHelper2 In Out s)"
  unfolding ndaHelper2_def
  apply(rule monofunI)
  apply(auto simp add: below_fun_def)
  by (metis (mono_tags, lifting) monofun_def ndaConcOutFlatten_def ndatodo_monofun2)


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
  by (metis (mono_tags, lifting) below_fun_def monofun_def ndaHelper2_def ndaConcOutFlatten_def ndatodo_monofun2)

lemma nda_h_inner_monofun2: "monofun (nda_h_inner)"
  unfolding nda_h_inner_def
  apply(simp only: Let_def)
  apply(rule monofunI)
  apply(simp add: ndadom_below_eq ndaran_below_eq)
  apply(auto simp add: below_fun_def)
  using nda_helper2_h2 by (simp add: nda_helper2_h2 monofun_cfun_arg)

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

(*
lemma nda_h_final_h:assumes "sbeDom sbe = ndaDom\<cdot>nda"
  shows "uspecRevSet\<cdot>(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)) =
    uspecRevSet\<cdot>(uspecFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s, sb). spsConcOut sb\<cdot>(nda_h nda s)) ((ndaTransition\<cdot>nda) (state, sbe))))"
proof (rule setrev_eqI2)
  let ?H  = "(ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda))"
  let ?In = "(ndaDom\<cdot>nda)"
  let ?Out = "(ndaRan\<cdot>nda)"
  let ?transition = "(ndaTransition\<cdot>nda)"

  show "inv Rev (uspecRevSet\<cdot>(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)))
    \<subseteq> inv Rev (uspecRevSet\<cdot>(uspecFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) ((ndaTransition\<cdot>nda) (state, sbe)))))"
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
    then have f3: "uspec_in y (spsStep ?In ?Out\<cdot>?H)"
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
    then have "\<And> sbe. uspec_in (f sbe) (uspecFlatten ?In ?Out 
                (setrevImage (\<lambda>(s, sb). spsConcOut sb\<cdot>((nda_h nda) s)) (?transition (state,sbe))))"
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


    show "uspec_in x (uspecFlatten ?In ?Out (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) ((ndaTransition\<cdot>nda) (state, sbe))))"
    proof -
      have "\<forall>u ua. (ufDom\<cdot>u \<noteq> ufDom\<cdot>ua \<or> (\<exists>ub. ubDom\<cdot>(ub::'a stream\<^sup>\<Omega>) = ufDom\<cdot>u \<and> u \<rightleftharpoons> ub \<noteq> ua \<rightleftharpoons> ub)) \<or> u = ua"
        by (meson spf_eq)
      then obtain uu :: "('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun \<Rightarrow> ('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun \<Rightarrow> 'a stream\<^sup>\<Omega>" where
              f1: "\<forall>u ua. (ufDom\<cdot>u \<noteq> ufDom\<cdot>ua \<or> ubDom\<cdot>(uu ua u) = ufDom\<cdot>u \<and> u \<rightleftharpoons> uu ua u \<noteq> ua \<rightleftharpoons> uu ua u) \<or> u = ua"
          by (metis (full_types))
      have "\<forall>x0 x1 x2 x3. (dom (Rep_sbElem (x0::'a sbElem)) \<noteq> x3 \<longrightarrow> (x1 x0::('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun) = ufLeast x3 x2) = (dom (Rep_sbElem x0) = x3 \<or> x1 x0 = ufLeast x3 x2)"
        by auto
      then have "\<forall>C Ca f. spsStep_P C Ca f = (\<forall>s. (dom (Rep_sbElem (s::'a sbElem)) \<noteq> C \<or> ufDom\<cdot>(f s) = C \<and> ufRan\<cdot>(f s) = Ca) \<and> (dom (Rep_sbElem s) = C \<or> f s = ufLeast C Ca))"
        by (simp add: spsStep_P_def)
      then have f2: "\<forall>s. (dom (Rep_sbElem s) \<noteq> ndaDom\<cdot>nda \<or> ufDom\<cdot>(f s) = ndaDom\<cdot>nda \<and> ufRan\<cdot>(f s) = ndaRan\<cdot>nda) \<and> (dom (Rep_sbElem s) = ndaDom\<cdot>nda \<or> f s = ufLeast (ndaDom\<cdot>nda) (ndaRan\<cdot>nda))"
      using f_def_2 by presburger
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
       by (metis \<open>\<And>sbe::'a sbElem. uspec_in ((f::'a sbElem \<Rightarrow> 'a stream\<^sup>\<Omega>\<Rrightarrow> 'a stream\<^sup>\<Omega>) sbe) (uspecFlatten (ndaDom\<cdot>(nda::('b, 'a) ndAutomaton)) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) ((ndaTransition\<cdot>nda) (state::'b, sbe))))\<close> x_f_eq)
    qed
  qed
  show "inv Rev (uspecRevSet\<cdot>(uspecFlatten ?In ?Out (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) ((ndaTransition\<cdot>nda) (state, sbe)))))
    \<subseteq> inv Rev (uspecRevSet\<cdot>(uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state)))" 
  proof rule
    fix x::"('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun"
    let ?L = " \<lambda> sbe. (uspecFlatten ?In ?Out (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) (?transition (state, sbe))))"
    assume a100: "uspec_in x (?L sbe)"
    obtain Z where z_def_1: "Z \<in> inv Rev (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) (?transition (state, sbe)))" and 
                   z_def_2: "uspec_in x Z"
      using a100 uspecflatten_elen by blast
    obtain W where w_def_1: "W \<in> inv Rev (?transition (state, sbe))" and w_def_2: " Z = (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) W"
      by (metis (no_types, lifting) setrevimage_mono_obtain3 z_def_1)
    obtain s1 sbe1 where s1_sbe1_def: "W = (s1, sbe1)"
      using surjective_pairing by blast
    have "uspec_in x (spsConcOut sbe1\<cdot>(nda_h nda s1))"
      using s1_sbe1_def w_def_2 z_def_2 by auto
    have "(spsConcOut sbe1\<cdot>(nda_h nda s1)) \<in> inv Rev (setrevImage (\<lambda>(s::'b, sb::'a stream\<^sup>\<Omega>). spsConcOut sb\<cdot>(nda_h nda s)) (?transition (state, sbe)))"
      using s1_sbe1_def w_def_2 z_def_1 by auto

    have f100: "uspec_in x (uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (spsStep ?In ?Out\<cdot>(ndaHelper2 ?In ?Out state ?transition (nda_h nda))))"
      apply (simp add: ndaHelper2_def ndaConcOutFlatten_def)
      sorry


    show "uspec_in x (uspecImage (Rep_cfun (spfConcIn (sbe2SB sbe))) (nda_h nda state))"
      by (metis f100 nda_h_fixpoint nda_h_inner_def)
  qed
qed


lemma nda_h_final: assumes "sbeDom sbe = ndaDom\<cdot>nda"
  shows "spsConcIn (sbe2SB sbe) (nda_h nda state) = 
  uspecFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s, sb). spsConcOut sb\<cdot>(nda_h nda s)) ((ndaTransition\<cdot>nda) (state,sbe)))"
  apply (rule uspec_eqI)  defer
    apply (subst spsconcin_dom)
     apply (simp add: one_lnat_def sbe_ch_len)
    apply (metis (no_types, lifting) nda_h_fixpoint nda_h_inner_dom uspecflatten_dom)
   apply (subst spsconcin_ran)
    apply (simp add: one_lnat_def sbe_ch_len)
   apply (metis (no_types, lifting) nda_h_fixpoint nda_h_inner_ran uspecflatten_ran)
  apply (simp add: spsConcIn_def)
  by (simp add: assms nda_h_final_h)


lemma nda_h_bottom_h: "uspecIsStrict (spsStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot>
  (ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda)))"
  apply (simp add: uspecIsStrict_def)
  apply (rule uspec_ballI)
  apply (rule ufisstrictI)
proof -
  fix x::"('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun"
  fix sb::"'a stream\<^sup>\<Omega>"
  assume a1: "uspec_in x (spsStep (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)\<cdot>(ndaHelper2 (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) state (ndaTransition\<cdot>nda) (nda_h nda)))"
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

lemma nda_h_final_back: assumes "\<And>state sbe. sbeDom sbe = ndaDom\<cdot>nda \<Longrightarrow> spsConcIn (sbe2SB sbe) (other state) = 
  uspecFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (setrevImage (\<lambda>(s, sb). spsConcOut sb\<cdot>(other s)) ((ndaTransition\<cdot>nda) (s,sbe)))"
  and "\<And> state. uspecDom\<cdot>(other state) = ndaDom\<cdot>nda" and "\<And> state. uspecRan\<cdot>(other state) = ndaRan\<cdot>nda"
shows "other = nda_h nda" 
  sorry

*)


end