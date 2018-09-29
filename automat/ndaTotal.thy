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

lemma nda2da_step:   assumes "sbeDom sbe = ndaDom\<cdot>nda" 
  shows "spfConcIn (sbe2SB sbe)\<cdot>(da_h (nda2da nda) s) = spfConcOut (daNextOutput (nda2da nda) s sbe)\<cdot>((da_h (nda2da nda) (daNextState (nda2da nda) s sbe)))"
  by (simp add: assms da_h_stepI)

lemma 
  assumes "sbeDom sbe = ndaDom\<cdot>nda" 
  shows "spsConcIn (sbe2SB sbe) (uspecConst (da_h (nda2da nda) s)) = 
  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) (makeItOneSet ((ndaTransition\<cdot>nda) (s, sbe))) (\<lambda>s::'a. uspecConst (da_h (nda2da nda) s))"
  apply simp
  apply(simp add: ndaConcOutFlatten_def ndaTodo_h_def)
  oops

lemma nda2da_least_h: "nda_h_inner nda (\<lambda>s::'a. uspecConst (da_h (nda2da nda) s)) \<sqsubseteq> (\<lambda>s::'a. uspecConst (da_h (nda2da nda) s))"
  apply(auto simp add: below_fun_def)
  apply(rule uspec_belowI)
    apply (simp add: ufclDom_ufun_def)
   apply (simp add: ufclRan_ufun_def)
  apply simp

  apply(simp add: nda_h_inner_def Let_def)
  apply(simp add: ndaHelper2_def)
  sorry

lemma nda2da_in: "nda_h nda \<sqsubseteq> (\<lambda>s. uspecConst (da_h (nda2da nda) s)) "
  apply(rule nda_h_least)
   apply(simp add: SetPcpo.setify_def)
  apply(subst uspec_in)
     apply (simp add: ufclDom_ufun_def)
    apply (simp add: ufclRan_ufun_def)
  apply simp
  by (simp add: nda2da_least_h)




lemma ndaone_consistent:
      shows "uspecIsConsistent (nda_h (ndaOne nda) s)"
  by (metis fun_below_iff nda2da_in uspec_isconsistent_below uspecconst_consistent)



lemma nda_consistent:  assumes trans_total: "\<And>s. (ndaTransition\<cdot>nda) s \<noteq> Rev {}"
        and initial_total: "(ndaInitialState\<cdot>nda) \<noteq> Rev {}"
      shows "uspecIsConsistent (nda_h nda s)"
  by (metis (no_types, hide_lams) below_fun_def initial_total monofunE nda_h_mono ndaone_below ndaone_consistent trans_total uspec_isconsistent_below)




end