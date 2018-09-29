theory ndaTotal

imports ndAutomaton dAutomaton

begin


fun makeItOne::"'a::type set rev \<Rightarrow> 'a" where
"makeItOne (Rev A) = (SOME a. a\<in>A)"

fun makeItOneSet::"'a::type set rev \<Rightarrow> 'a set rev" where
"makeItOneSet (Rev A) = Rev {(SOME a. a\<in>A)}"

lift_definition ndaOne:: "('s::type,'m::message) ndAutomaton \<Rightarrow> ('s,'m) ndAutomaton" is
"\<lambda>nda. (\<lambda>s. makeItOneSet ((ndaTransition\<cdot>nda) s), makeItOneSet (ndaInitialState\<cdot>nda), Discr (ndaDom\<cdot>nda), Discr (ndaRan\<cdot>nda))"
  by simp

lift_definition nda2da :: "('s::type,'m::message) ndAutomaton \<Rightarrow> ('s,'m) dAutomaton" is
"\<lambda>nda. (\<lambda>s. makeItOne ((ndaTransition\<cdot>nda) s), fst (makeItOne (ndaInitialState\<cdot>nda)), snd (makeItOne (ndaInitialState\<cdot>nda)), (ndaDom\<cdot>nda), (ndaRan\<cdot>nda))"
  by simp




subsection\<open>makeItOne\<close>
lemma makeitone_in: "A\<noteq>{} \<Longrightarrow> makeItOne (Rev A) \<in> A"
  by (simp add: some_in_eq)




subsection\<open>makeItOneSet\<close>
lemma makeitoneset_one: "\<exists>!a. (makeItOneSet A = Rev {a})"
  by (metis makeItOneSet.elims rev.set the_elem_eq)
lemma makeitoneset_in: "A\<noteq>(Rev {}) \<Longrightarrow> A\<sqsubseteq>makeItOneSet A"
  by (metis (no_types, lifting) inv_rev_rev makeItOneSet.simps revBelowNeqSubset setrev_eqI singletonD some_in_eq subsetI)
lemma makeitoneset_subset: "makeItOneSet A = Rev {makeItOne (A)}"
  by (metis below_refl makeItOne.elims makeItOneSet.simps)


subsection \<open>ndaOne\<close>

lemma ndaone_dom [simp]: "ndaDom\<cdot>(ndaOne nda) = ndaDom\<cdot>nda"
  by(simp add: ndaDom.rep_eq ndaOne.rep_eq)

lemma ndaone_ran [simp]: "ndaRan\<cdot>(ndaOne nda) = ndaRan\<cdot>nda"
  by(simp add: ndaRan.rep_eq ndaOne.rep_eq)

lemma ndaone_transition [simp]: "ndaTransition\<cdot>(ndaOne nda) = (\<lambda>s. makeItOneSet ((ndaTransition\<cdot>nda) s))"
  by(simp add: ndaTransition.rep_eq ndaOne.rep_eq)

lemma ndaone_initial [simp]: "ndaInitialState\<cdot>(ndaOne nda) = makeItOneSet (ndaInitialState\<cdot>nda)"
  by(simp add: ndaInitialState.rep_eq ndaOne.rep_eq)

lemma ndaone_below: assumes trans_total: "\<And>s. (ndaTransition\<cdot>nda) s \<noteq> Rev {}"
        and initial_total: "(ndaInitialState\<cdot>nda) \<noteq> Rev {}"
  shows "nda \<sqsubseteq> ndaOne nda"
  apply(rule nda_belowI, simp_all)
  apply (simp add: initial_total makeitoneset_in)
  by (simp add: fun_belowI makeitoneset_in trans_total)

lemma nda_one_h_below: 
    assumes trans_total: "\<And>s. (ndaTransition\<cdot>nda) s \<noteq> Rev {}"
        and initial_total: "(ndaInitialState\<cdot>nda) \<noteq> Rev {}"
      shows "nda_h nda \<sqsubseteq> nda_h (ndaOne nda)"
  using nda_h_mono by (simp add: nda_h_mono initial_total monofunE ndaone_below trans_total)




subsection \<open>nda2da\<close>
lemma nda2da_dom[simp]: "daDom (nda2da nda) = ndaDom\<cdot>nda"
  by(simp add: daDom_def nda2da.rep_eq)

lemma nda2da_ran[simp]: "daRan (nda2da nda) = ndaRan\<cdot>nda"
  by(simp add: daRan_def nda2da.rep_eq)

lemma nda2da_transition [simp]: "daTransition (nda2da nda) = (\<lambda>s. makeItOne ((ndaTransition\<cdot>nda) s))"
  by(simp add: daTransition_def nda2da.rep_eq)

lemma nda2da_init_state [simp]: "daInitialState (nda2da nda) = fst (makeItOne (ndaInitialState\<cdot>nda))"
  by(simp add: daInitialState_def nda2da.rep_eq)

lemma nda2da_init_out [simp]: "daInitialOutput (nda2da nda) = snd (makeItOne (ndaInitialState\<cdot>nda))"
  by(simp add: daInitialOutput_def nda2da.rep_eq)

lemma uspec_in: "uspecDom\<cdot>uspec = In \<Longrightarrow> uspecRan\<cdot>uspec=Out \<Longrightarrow> uspec \<in> USPEC In Out"
  apply(simp only: USPEC_def)
  by blast

lemma nda2da_da_step:   assumes "sbeDom sbe = ndaDom\<cdot>nda" 
  shows "spfConcIn (sbe2SB sbe)\<cdot>(da_h (nda2da nda) s) = spfConcOut (daNextOutput (nda2da nda) s sbe)\<cdot>((da_h (nda2da nda) (daNextState (nda2da nda) s sbe)))"
  by (simp add: assms da_h_stepI)


(* ToDo: copy to SB *)
lemma sbconc_inf: fixes sb::"'m::message SB"
    assumes "ubDom\<cdot>sb=ubDom\<cdot>ub_inf" and "ubLen ub_inf = \<infinity>"
  shows "ubConc ub_inf\<cdot>sb = ub_inf"
proof(rule ub_eq)
  show "ubDom\<cdot>(ubConc ub_inf\<cdot>sb) = ubDom\<cdot>ub_inf" by (simp add: assms(1))
next
  fix c
  assume "c \<in> ubDom\<cdot>(ubConc ub_inf\<cdot>sb)"
  hence c_dom: "c\<in>(ubDom\<cdot>ub_inf)"
    by (simp add: assms(1))
  hence "usclLen\<cdot>(ub_inf . c) = \<infinity>"
    using assms(2) ublen_channel by fastforce
  thus "(ubConc ub_inf\<cdot>sb)  .  c = ub_inf  .  c"
    by (simp add: c_dom assms(1) usclConc_stream_def usclLen_stream_def)
qed

lemma spfconcout_inf: "ubLen ub = \<infinity> \<Longrightarrow> ubDom\<cdot>ub=ufRan\<cdot>uf \<Longrightarrow> ubclDom\<cdot>x = ufDom\<cdot>uf \<Longrightarrow> spfConcOut ub\<cdot>uf \<rightleftharpoons> x = ub"
  apply (simp add: ubclDom_ubundle_def spfConcOut_step)
  by (metis sbconc_inf ubclDom_ubundle_def ubclRestrict_ubundle_def ubclrestrict_dom_id ufran_2_ubcldom2)

lemma spfconcout_inf_const: assumes "ubDom\<cdot>ub = ufRan\<cdot>uf" and "ubLen ub = \<infinity>"
  shows "spfConcOut ub\<cdot>uf = ufConst (ufDom\<cdot>uf)\<cdot>ub"
  apply(rule ufun_eqI)
   apply simp
  apply simp
  using assms(1) assms(2) spfconcout_inf by blast


lemma ubconceq_restrict: "ubDom\<cdot>ub2 \<subseteq> cs \<Longrightarrow> ubConcEq (ubRestrict cs\<cdot>ub)\<cdot>ub2 = ubConcEq ub\<cdot>ub2"
  apply(rule ub_eq)
  apply simp
   apply blast
  apply simp
  by (smt IntE IntI Un_iff sbrestrict2sbgetch subset_Un_eq ubconc_getch ubrestrict_ubdom2 ubup_ubgetch ubup_ubgetch2)

lemma spfconcout_restrict: "ufRan\<cdot>uf \<subseteq> ubDom\<cdot>ub \<Longrightarrow> spfConcOut ub\<cdot>uf = spfConcOut (ubRestrict (ufRan\<cdot>uf)\<cdot>ub)\<cdot>uf"
  apply(rule ufun_eqI)
   apply simp
  apply simp
  apply(simp add: ubclDom_ubundle_def)
  by (metis order_refl ubclDom_ubundle_def ubconceq_insert ubconceq_restrict ufran_2_ubcldom2)

lemma spfconcout_inf_const2: assumes "ufRan\<cdot>uf \<subseteq> ubDom\<cdot>ub" and "ubLen (ubRestrict (ufRan\<cdot>uf)\<cdot>ub) = \<infinity>"
  shows "spfConcOut ub\<cdot>uf = (ufConst (ufDom\<cdot>uf)\<cdot>(ubRestrict (ufRan\<cdot>uf)\<cdot>ub))"
  apply(rule ufun_eqI)
   apply simp
  apply simp
  using assms(1) assms(2) spfconcout_inf spfconcout_restrict by fastforce

lemma ublen_not_0: assumes "ubLen ub \<noteq> 0" and "c\<in>ubDom\<cdot>ub"
  shows "usclLen\<cdot>(ub . c) \<noteq> 0"
  using assms(1) assms(2) ublen_channel by fastforce


lemma ublen_up_restrict[simp]: fixes ub ::"'a::message SB"
  assumes "ubLen (ubRestrict cs\<cdot>(ubUp\<cdot>ub)) \<noteq> 0"
  shows "cs \<subseteq> ubDom\<cdot>ub"
proof - 
  have "\<And>c. c\<in>cs \<Longrightarrow>  usclLen\<cdot>((ubRestrict cs \<cdot>(ubUp\<cdot>ub)) . c) \<noteq> 0" 
    by(subst ublen_not_0, auto simp add: assms)
  hence "\<And>c. c\<in>cs \<Longrightarrow>  usclLen\<cdot>((ubUp\<cdot>ub) . c) \<noteq> 0" by simp
  thus ?thesis
    using ubup_ubgetch2 usclLen_bot by fastforce
qed

lemma ublen_up_restrict2[simp]: fixes ub ::"'a::message SB"
  shows "ubLen (ubRestrict cs\<cdot>(ubUp\<cdot>ub)) \<noteq> 0 \<Longrightarrow> (ubRestrict cs\<cdot>(ubUp\<cdot>ub)) = ubRestrict cs\<cdot>ub"
  apply(rule ub_eq)
  apply (simp add: inf_absorb2)
  apply simp
  by (simp add: rev_subsetD)

lemma nda2da_nda_step: 
  assumes "sbeDom sbe = ndaDom\<cdot>nda"  
  shows "spsConcIn (sbe2SB sbe) (uspecConst (da_h (nda2da nda) s)) = 
  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (makeItOneSet ((ndaTransition\<cdot>nda) (s, sbe))) (\<lambda>s::'a. uspecConst (da_h (nda2da nda) s))"
  apply (simp add: nda2da_da_step assms daNextOutput_def daNextState_def)
  apply(subst makeitoneset_subset)
  apply(subst ndaconcout_one2)
  apply (simp add: ufclDom_ufun_def)
   apply (simp add: ufclRan_ufun_def)

  apply(cases "((ubLen ( ubclRestrict (ndaRan\<cdot>nda)\<cdot>(ubUp\<cdot>(daNextOutput (nda2da nda) s sbe)) )) < \<infinity>)")
   apply (simp add: ndaTodo_h_def case_prod_beta' daNextOutput_def ubclRestrict_ubundle_def)+
  apply(subst ublen_up_restrict2)
  using Zero_lnless_infty apply auto[1]
  apply(subst spfconcout_inf_const2)
  apply simp_all
    apply (metis Zero_lnless_infty ublen_up_restrict)
  apply (metis Zero_lnless_infty inf_less_eq leI ublen_up_restrict2)
  apply(simp add: uspecConstOut_def)
  done

(*
lemma nda2da_least_h: "nda_h_inner nda (\<lambda>s::'a. uspecConst (da_h (nda2da nda) s)) \<sqsubseteq> (\<lambda>s::'a. uspecConst (da_h (nda2da nda) s))"
  apply(auto simp add: below_fun_def)
  apply(rule uspec_belowI)
    apply (simp add: ufclDom_ufun_def)
   apply (simp add: ufclRan_ufun_def)
  apply simp

  apply(simp add: nda_h_inner_def Let_def)
  apply(simp add: ndaHelper2_def)
  sorry
*)

lemma nda2da_ndaone_below: "nda_h (ndaOne nda) \<sqsubseteq> (\<lambda>s. uspecConst (da_h (nda2da nda) s)) "
  apply(rule nda_h_final_back)
  using nda2da_nda_step apply fastforce
  apply (simp add: ufclDom_ufun_def)
  by (simp add: ufclRan_ufun_def)
(*
  apply(rule nda_h_least)
   apply(simp add: SetPcpo.setify_def)
  apply(subst uspec_in)
     apply (simp add: ufclDom_ufun_def)
    apply (simp add: ufclRan_ufun_def)
  apply simp
  by (simp add: nda2da_least_h)
*)


lemma ndaone_consistent:
      shows "uspecIsConsistent (nda_h (ndaOne nda) s)"
  by (metis fun_below_iff nda2da_ndaone_below uspec_isconsistent_below uspecconst_consistent)



lemma nda_consistent:  assumes trans_total: "\<And>s. (ndaTransition\<cdot>nda) s \<noteq> Rev {}"
        and initial_total: "(ndaInitialState\<cdot>nda) \<noteq> Rev {}"
      shows "uspecIsConsistent (nda_h nda s)"
  by (metis (no_types, hide_lams) below_fun_def initial_total monofunE nda_h_mono ndaone_below ndaone_consistent trans_total uspec_isconsistent_below)




end