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


lemma sps2spf_step_single: assumes "spsConcIn input sps = spsConcOut output sps2"
          and "spf \<in> uspecSet sps"
        obtains spf2 where "spfConcIn input\<cdot>spf = spfConcOut output\<cdot>spf2" and "spf2 \<in> uspecSet sps2"
  oops

lemma medunfair_spf_step_tick [simp]: assumes "spf \<in> uspecSet (medUnfair)"
  shows "spfConcIn (mediumIn_i -)\<cdot>spf = spfConcOut (mediumOut_o -)\<cdot>spf"
  oops

(* Final Proof *)
lemma medunfair_dom [simp]: assumes "spf \<in> uspecSet medUnfair"
  shows "tsynDom\<cdot>(medium_get_stream_o\<cdot>(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>s)) \<subseteq> tsynDom\<cdot>s"
  using assms apply(induction s arbitrary: spf rule:ind)
  apply(rule admI)
    apply auto
  oops

end