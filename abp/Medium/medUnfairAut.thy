theory medUnfairAut

imports PreludeMed automat.ndAutomaton automat.ndaTotal

begin


datatype medState = Single

(* Superset of the Fair-Transition *)
fun medUnfairTransitionH :: "medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medUnfairTransitionH  _      -    = { (Single,    -   )            }" |
"medUnfairTransitionH  _   (Msg m) = { (Single  ,    -   ),  (Single  ,    Msg m  ) }"

fun medUnfairTransition :: "(medState \<times> 'a mediumMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a mediumMessage tsyn SB) set rev)" where
"medUnfairTransition (s,f) = (if sbeDom f = mediumDom then 
    Rev ((\<lambda>(s,out). (s, mediumOut_o out)) ` (medUnfairTransitionH s (mediumElem_get_i f))) 
  else Rev { undefined })"

lift_definition medUnfairAut :: "(medState, 'a mediumMessage tsyn) ndAutomaton" is 
  "(medUnfairTransition, Rev {(Single, mediumOut_o - )}, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def)

definition medUnfair :: "'a mediumMessage tsyn SPS" where
"medUnfair = nda_h medUnfairAut Single"





lemma medunfairaut_dom[simp]: "ndaDom\<cdot>medUnfairAut = mediumDom"
  by (simp add: medUnfairAut.rep_eq ndaDom.rep_eq)

lemma medunfairaut_ran[simp]: "ndaRan\<cdot>medUnfairAut = mediumRan"
  by (simp add: medUnfairAut.rep_eq ndaRan.rep_eq)


lemma medunfair_transition_tick [simp]: "medUnfairTransition (state, (mediumElemIn_i -)) = Rev {(Single, mediumOut_o -)}"
  by simp

lemma medunfair_transition_msg [simp]: "medUnfairTransition (state, (mediumElemIn_i (Msg m))) = Rev {(Single, mediumOut_o -), (Single, mediumOut_o (Msg m))}"
  by simp


lemma medunfair_trans_total_h: "medUnfairTransition (Single, s) \<noteq> Rev {}"
  apply(cases "sbeDom s = mediumDom", simp_all)
  by (metis insert_not_empty medUnfairTransitionH.elims)

lemma medunfair_trans_total[simp]: "(ndaTransition\<cdot>medUnfairAut) s \<noteq> Rev {}"
  apply(simp add: ndaTransition_def medUnfairAut.rep_eq)
  by (metis medState.exhaust medUnfairTransition.cases medunfair_trans_total_h)

lemma medunfair_initial_total [simp]: "ndaInitialState\<cdot>medUnfairAut \<noteq> Rev {}"
  by(simp add: ndaInitialState_def medUnfairAut.rep_eq)

lemma medunfair_consistent[simp]: "uspecIsConsistent (nda_h medUnfairAut s)"
  apply(rule nda_consistent)
  by simp_all

lemma medunfair_step_tick [simp]: "spsConcIn (mediumIn_i -) medUnfair = spsConcOut(mediumOut_o -) medUnfair"
  apply(simp add: mediumIn_i_def medUnfair_def)
  apply(rule nda_h_one_I, simp_all)
   apply (simp add: medUnfairAut.rep_eq ndaTransition.rep_eq)
  by (auto simp add: one_lnat_def)

lemma medunfair_step_msg [simp]: "spsConcIn (mediumIn_i (Msg m)) medUnfair 
  = ndaConcOutFlatten mediumDom mediumRan (Rev {(Single, mediumOut_o -), (Single, mediumOut_o (Msg m))}) (\<lambda>s. medUnfair)"
  apply(simp add: medUnfair_def mediumIn_i_def)
  apply(subst nda_h_I, auto)
  apply(simp add: ndaTransition_def medUnfairAut.rep_eq)
  by (metis medState.exhaust)





(* Allgemein det-step*)
lemma uspecimage_rep_eq: assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))" 
  shows "Rep_uspec (uspecImage f S) =((setrevImage f (uspecRevSet\<cdot>S)),
    Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))),
    Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"
  by (simp add: assms setrevImage_def ufuncldom_least_dom ufuncldom_least_ran uspecImage_def uspec_allDom uspec_allRan)

lemma uspecimage_set: assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))" 
  shows "uspecSet (uspecImage f sps) = f ` (uspecSet sps)"
  apply(simp add: uspecSet_def uspecRevSet_def)
  apply(subst uspecimage_rep_eq)
  using assms apply blast
  by (simp add: rep_rev_revset setrevImage_def)

lemma spsconcin_set:  "uspecSet (spsConcIn In sps) = (Rep_cfun (spfConcIn In)) ` (uspecSet sps)"
  apply(simp add: spsConcIn_def)
  apply(rule uspecimage_set)
  by (simp add: spfconcin_uspec_iamge_well ufclRan_ufun_def)

lemma spsconcout_set:  "uspecSet (spsConcOut Out sps) = (Rep_cfun (spfConcOut Out)) ` (uspecSet sps)"
  apply(simp add: spsConcOut_def)
  apply(rule uspecimage_set)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spsonestep_spf: assumes "spsConcIn In sps1 = spsConcOut Out sps2" 
  shows "(Rep_cfun (spfConcIn In)) `(uspecSet sps1) = (Rep_cfun (spfConcOut Out)) ` uspecSet sps2"
  by (metis assms spsconcin_set spsconcout_set)

lemma spsonestep_spf_exists: assumes "spsConcIn In sps1 = spsConcOut Out sps2" and "spf1 \<in> uspecSet sps1"
  shows  "\<exists>spf2. spf2 \<in> uspecSet sps2 \<and> spfConcIn In\<cdot>spf1 = spfConcOut Out\<cdot>spf2"
  by (metis (no_types, hide_lams) assms(1) assms(2) image_iff spsconcin_set spsconcout_set)
  



(* Global, non-det-step *)

lemma uspecflatten_rep_eq: "Rep_rev_uspec (uspecFlatten Dom Ran uspec) 
  = ((setflat\<cdot>(Rep_rev_uspec ` (inv Rev (uspec_set_filter Dom Ran\<cdot>uspec)))))"
  apply(simp add: uspecFlatten_def)
  using rep_abs_rev_simp uspecflatten_well by blast

lemma uspecflatten_set: "uspecSet (uspecFlatten Dom Ran (Rev uspecs)) = 
    (Set.filter (\<lambda> uf. ufDom\<cdot>uf = Dom \<and> ufRan\<cdot>uf = Ran) (\<Union> (uspecSet ` uspecs)))"
  apply(simp add: uspecSet_def uspecRevSet_def)
  apply(simp add: uspecflatten_rep_eq)
  apply(simp add: setflat_union uspec_set_filter_def setrevFilter_def)
  apply auto
  apply blast
  apply (metis ufclDom_ufun_def uspec_allDom uspecrevset_insert)
  apply (metis rep_rev_revset ufclDom_ufun_def uspec_allDom)
  apply (metis rep_rev_revset ufclRan_ufun_def uspec_allRan)
  apply (metis ufclRan_ufun_def uspec_allRan uspecrevset_insert)
  by (metis (mono_tags, lifting) member_filter rep_rev_revset ufclDom_ufun_def ufclRan_ufun_def uspec_allDom uspec_allRan)

lemma ndaconcoutflat_set: 
  "uspecSet (ndaConcOutFlatten Dom Ran (Rev Transition) h) = 
    (Set.filter (\<lambda> uf. ufDom\<cdot>uf = Dom \<and> ufRan\<cdot>uf = Ran) (\<Union> (((\<lambda> (s, sb). uspecSet (ndaTodo_h Dom Ran sb (h s))) ` Transition))))"
  apply(simp add: ndaConcOutFlatten_def setrevImage_def)
  apply(simp add: uspecflatten_set)
  by (simp add: case_prod_beta')

lemma ndaconcout_subset: assumes "(nextState, Out) \<in> Transition" and "uspecDom\<cdot>(h nextState) = Dom" and "uspecRan\<cdot>(h nextState) = Ran"
  shows " uspecSet(ndaTodo_h Dom Ran Out (h nextState)) \<subseteq> uspecSet (ndaConcOutFlatten Dom Ran (Rev Transition) h) "
  apply(subst ndaconcoutflat_set)
  apply rule
  by (smt UN_iff assms(1) assms(2) assms(3) case_prod_beta' fst_conv member_filter ndaconcoutflat_set ndaconout_one snd_conv)


lemma ndaconcout_get: assumes "spf \<in> uspecSet (ndaConcOutFlatten Dom Ran Transition h)"
  shows "\<exists> nextState Out. (nextState, Out) \<in> (inv Rev) Transition 
          \<and>spf \<in> uspecSet(ndaTodo_h Dom Ran Out (h nextState))"
  by (metis (mono_tags, lifting) UN_iff assms case_prod_beta' member_filter ndaconcoutflat_set prod.collapse rev_inv_rev)

lemma ndastep_spf: assumes "spsConcIn In sps = ndaConcOutFlatten Dom Ran (Rev Transition) h" and "spf\<in>uspecSet sps"
  and "\<And>nextState Out. (nextState, Out) \<in> Transition \<Longrightarrow> ubLen (ubRestrict Ran\<cdot>(ubUp\<cdot>Out)) < \<infinity>"
  shows "\<exists> nextState Out spf2. (nextState, Out) \<in> Transition 
          \<and> spf2 \<in>(uspecSet (h nextState))
          \<and> spfConcIn In\<cdot>spf = spfConcOut Out\<cdot>spf2"
proof - 
  have "spfConcIn In\<cdot>spf \<in> uspecSet (ndaConcOutFlatten Dom Ran (Rev Transition) h)"
    by (metis assms(1) assms(2) rev_image_eqI spsconcin_set)
  from this obtain nextState Out where  in_trans: "(nextState, Out) \<in> Transition" 
      and step_h:"spfConcIn In\<cdot>spf \<in> uspecSet(ndaTodo_h Dom Ran Out (h nextState))"
    using ndaconcout_get by force
  hence "ubLen (ubRestrict Ran\<cdot>(ubUp\<cdot>Out)) < \<infinity>"
    using assms(3) by blast
  hence "spfConcIn In\<cdot>spf \<in> uspecSet(spsConcOut Out (h nextState))" using step_h ndaTodo_h_def by metis
  thus ?thesis
    using in_trans spsconcout_set by fastforce
qed

lemma ndaconcout_get_step: assumes "spf \<in> uspecSet (ndaConcOutFlatten Dom Ran Transition h)"
  shows "\<exists> nextState Out. (nextState, Out) \<in> (inv Rev) Transition 
          \<and>spf \<in> uspecSet(ndaTodo_h Dom Ran Out (h nextState))"
  by (metis (mono_tags, lifting) UN_iff assms case_prod_beta' member_filter ndaconcoutflat_set prod.collapse rev_inv_rev)


lemma lnat_1_inf [simp]: "1 < \<infinity>"
  unfolding one_lnat_def
  by simp



(* Medium-spezifisch *)

lemma medtodo [simp]: "ndaTodo_h mediumDom mediumRan (mediumOut_o m) sps = spsConcOut (mediumOut_o m) sps"
  by(auto simp add: ndaTodo_h_def)

lemma medunfair_spf_step_tick [simp]: assumes "spf \<in> uspecSet (medUnfair)"
  obtains spf2 where "spf2\<in>uspecSet medUnfair" and "spfConcIn (mediumIn_i -)\<cdot>spf = spfConcOut (mediumOut_o -)\<cdot>spf2"
  using assms medunfair_step_tick spsonestep_spf_exists by blast

lemma med_msg_step_h: assumes "spf\<in>uspecSet medUnfair"
  shows "\<exists> nextState Out spf2. (nextState, Out) \<in> ({(Single, mediumOut_o -), (Single, mediumOut_o (Msg m))}) 
          \<and> spf2 \<in>(uspecSet medUnfair)
          \<and> spfConcIn (mediumIn_i (Msg m))\<cdot>spf = spfConcOut Out\<cdot>spf2"
  by(rule ndastep_spf [of "(mediumIn_i (Msg m))" medUnfair], auto simp add: assms)

lemma medunfair_spf_step_msg [simp]: assumes "spf \<in> uspecSet (medUnfair)"
  shows "\<exists> out spf2. spf2\<in>uspecSet medUnfair \<and> spfConcIn (mediumIn_i (Msg m))\<cdot>spf = spfConcOut (mediumOut_o out)\<cdot>spf2 \<and> out\<in>{-, Msg m}"
  using assms med_msg_step_h by fastforce



(* Autogenerate: *)
lemma med_spf_strict[simp]: "spf\<in>uspecSet (medUnfair) \<Longrightarrow> (spf \<rightleftharpoons> ubLeast mediumDom) = ubLeast mediumRan"
  sorry

lemma med_spf_strict2[simp]: "spf\<in>uspecSet (medUnfair) \<Longrightarrow> (spf \<rightleftharpoons> (mediumIn_stream_i\<cdot>\<epsilon>)) = ubLeast mediumRan"
  by (simp add: medin_stream_least)

(* Final Proof *)
lemma medunfair_dom [simp]: assumes "spf \<in> uspecSet medUnfair"
  shows "tsynDom\<cdot>(medium_get_stream_o\<cdot>(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>s)) \<subseteq> tsynDom\<cdot>s"
  using assms apply(induction s arbitrary: spf rule:ind)
    apply(rule adm_all, rule admI)
    apply (rule, simp)
    defer
    apply (simp)
  
  oops

end