theory medUnfairAut

imports PreludeMed automat.ndAutomaton automat.ndaTotal

begin


datatype medState = Single

(* Superset of the Fair-Transition *)
fun medUnfairTransitionH :: "medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medUnfairTransitionH  _      -    = { (Single,    -   )            }" |
"medUnfairTransitionH  _   (Msg m) = { (Single  ,    -   ),  (Single  ,    Msg m  ) }"

fun medUnfairTransition :: "(medState \<times> 'a mediumMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a mediumMessage tsyn SB) set )" where
"medUnfairTransition (s,f) = (if sbeDom f = mediumDom then 
    ((\<lambda>(s,out). (s, mediumOut_o out)) ` (medUnfairTransitionH s (mediumElem_get_i f))) 
  else { undefined })"

lift_definition medUnfairAut :: "(medState, 'a mediumMessage tsyn) ndAutomaton" is 
  "(medUnfairTransition, {(Single, mediumOut_o - )}, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def)

definition medUnfair :: "'a mediumMessage tsyn SPS" where
"medUnfair = nda_h medUnfairAut Single"





lemma medunfairaut_dom[simp]: "ndaDom\<cdot>medUnfairAut = mediumDom"
  by (simp add: medUnfairAut.rep_eq ndaDom.rep_eq)

lemma medunfairaut_ran[simp]: "ndaRan\<cdot>medUnfairAut = mediumRan"
  by (simp add: medUnfairAut.rep_eq ndaRan.rep_eq)


lemma medunfair_transition_tick [simp]: "medUnfairTransition (state, (mediumElemIn_i -)) = {(Single, mediumOut_o -)}"
  by simp

lemma medunfair_transition_msg [simp]: "medUnfairTransition (state, (mediumElemIn_i (Msg m))) = {(Single, mediumOut_o -), (Single, mediumOut_o (Msg m))}"
  by simp


lemma medunfair_trans_total_h: "medUnfairTransition (Single, s) \<noteq> {}"
  apply(cases "sbeDom s = mediumDom", simp_all)
  by (metis insert_not_empty medUnfairTransitionH.elims)

lemma medunfair_trans_total[simp]: "(ndaTransition\<cdot>medUnfairAut) s \<noteq> {}"
  apply(simp add: ndaTransition_def medUnfairAut.rep_eq)
  by (metis medState.exhaust medUnfairTransition.cases medunfair_trans_total_h)

lemma medunfair_initial_total [simp]: "ndaInitialState\<cdot>medUnfairAut \<noteq> {}"
  by(simp add: ndaInitialState_def medUnfairAut.rep_eq)

lemma medunfair_consistent[simp]: "uspecIsConsistent (nda_h medUnfairAut s)"
  apply(rule nda_consistent)
  by simp_all

lemma medunfair_step_tick [simp]: "spsConcIn (mediumIn_i -)\<cdot>medUnfair = spsConcOut(mediumOut_o -)\<cdot>medUnfair"
  apply(simp add: mediumIn_i_def medUnfair_def)
  apply(rule nda_h_one_I, simp_all)
   apply (simp add: medUnfairAut.rep_eq ndaTransition.rep_eq)
  by (auto simp add: one_lnat_def)

lemma medunfair_step_msg [simp]: "spsConcIn (mediumIn_i (Msg m))\<cdot>medUnfair 
  = ndaConcOutFlatten mediumDom mediumRan ({(Single, mediumOut_o -), (Single, mediumOut_o (Msg m))}) (\<lambda>s. medUnfair)"
  apply(simp add: medUnfair_def mediumIn_i_def)
  apply(subst nda_h_I, auto)
  apply(simp add: ndaTransition_def medUnfairAut.rep_eq)
  by (metis medState.exhaust)




(* Allgemein det-step*)
lemma uspecimage_rep_eq: assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))" 
  shows "Rep_uspec (uspecImage f S) =((f ` (uspecSet\<cdot>S)),
    Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))),
    Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"
  by (simp add: assms ufuncldom_least_dom ufuncldom_least_ran uspecImage_def uspec_allDom uspec_allRan)

lemma spsonestep_spf: assumes "spsConcIn In\<cdot>sps1 = spsConcOut Out\<cdot>sps2" 
  shows "(Rep_cfun (spfConcIn In)) `(uspecSet\<cdot>sps1) = (Rep_cfun (spfConcOut Out)) ` uspecSet\<cdot>sps2"
  by (metis assms spsconcin_set spsconcout_set)

lemma spsonestep_spf_exists: assumes "spsConcIn In\<cdot>sps1 = spsConcOut Out\<cdot>sps2" and "spf1 \<in> uspecSet\<cdot>sps1"
  shows  "\<exists>spf2. spf2 \<in> uspecSet\<cdot>sps2 \<and> spfConcIn In\<cdot>spf1 = spfConcOut Out\<cdot>spf2"
  by (metis (no_types, hide_lams) assms(1) assms(2) image_iff spsconcin_set spsconcout_set)
  



(* Medium-spezifisch *)

lemma medtodo [simp]: "ndaTodo_h mediumDom mediumRan (mediumOut_o m) sps = spsConcOut (mediumOut_o m)\<cdot>sps"
  by(auto simp add: ndaTodo_h_def)

lemma medunfair_spf_step_tick [simp]: assumes "spf \<in> uspecSet\<cdot>(medUnfair)"
  obtains spf2 where "spf2\<in>uspecSet\<cdot>medUnfair" and "spfConcIn (mediumIn_i -)\<cdot>spf = spfConcOut (mediumOut_o -)\<cdot>spf2"
  using assms medunfair_step_tick spsonestep_spf_exists by blast

lemma med_msg_step_h: assumes "spf\<in>uspecSet\<cdot>medUnfair"
  shows "\<exists> nextState Out spf2. (nextState, Out) \<in> ({(Single, mediumOut_o -), (Single, mediumOut_o (Msg m))}) 
          \<and> spf2 \<in>(uspecSet\<cdot>medUnfair)
          \<and> spfConcIn (mediumIn_i (Msg m))\<cdot>spf = spfConcOut Out\<cdot>spf2"
  by(rule ndastep_spf [of "(mediumIn_i (Msg m))" medUnfair], auto simp add: assms)

lemma medunfair_spf_step_msg [simp]: assumes "spf \<in> uspecSet\<cdot>(medUnfair)"
  shows "\<exists> out spf2. spf2\<in>uspecSet\<cdot>medUnfair \<and> spfConcIn (mediumIn_i (Msg m))\<cdot>spf = spfConcOut (mediumOut_o out)\<cdot>spf2 \<and> out\<in>{-, Msg m}"
  using assms med_msg_step_h by fastforce



(* Autogenerate: *)
lemma medunfair_strict_spf[simp]: "spf\<in>uspecSet\<cdot>(medUnfair) \<Longrightarrow> ufIsStrict spf"
  by (simp add: medUnfair_def nda_h_bottom)

lemma mediumdom_nbot[simp]: "mediumDom\<noteq>{}"
  by(simp add: mediumDom_def)

lemma medium_dom_spf[simp]: "spf\<in>uspecSet\<cdot>(medUnfair) \<Longrightarrow> ufDom\<cdot>spf = mediumDom"
  sorry

lemma medium_ran_spf[simp]: "spf\<in>uspecSet\<cdot>(medUnfair) \<Longrightarrow> ufRan\<cdot>spf = mediumRan"
  sorry

lemma med_spf_strict[simp]: "spf\<in>uspecSet\<cdot>(medUnfair) \<Longrightarrow> (spf \<rightleftharpoons> ubLeast mediumDom) = ubLeast mediumRan"
  by(subst spf_isstrict, simp_all)

lemma med_spf_strict2[simp]: "spf\<in>uspecSet\<cdot>(medUnfair) \<Longrightarrow> (spf \<rightleftharpoons> (mediumIn_stream_i\<cdot>\<epsilon>)) = ubLeast mediumRan"
  by (simp add: medin_stream_least)

lemma adm_subset[simp]:"adm(\<lambda>s. g\<cdot>s \<subseteq> f\<cdot>s)"
  by simp

thm adm_subsetEq
(* Final Proof *)

lemma medapply_cont[simp]: "spf\<in>uspecSet\<cdot>(medUnfair) \<Longrightarrow> cont (\<lambda>s. (spf \<rightleftharpoons> mediumIn_stream_i\<cdot>s))"
  using cont_compose f20 op_the_cont by blast

lemma medapply_subst: assumes "spf\<in>uspecSet\<cdot>(medUnfair)" 
  shows "(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>s) = (\<Lambda> s. (spf \<rightleftharpoons> mediumIn_stream_i\<cdot>s))\<cdot>s"
  by (simp add: assms)

lemma medunfair_step_stream_tick: assumes "spf\<in>uspecSet\<cdot>medUnfair"
  obtains spf2 where "medium_get_stream_o\<cdot>(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>(\<up>- \<bullet> s)) = \<up>- \<bullet> medium_get_stream_o\<cdot>(spf2 \<rightleftharpoons> mediumIn_stream_i\<cdot>s)"
  and  "spf2\<in>uspecSet\<cdot>medUnfair"
  sorry

lemma medunfair_step_stream_msg: assumes "spf\<in>uspecSet\<cdot>medUnfair"
  shows "\<exists>spf2 out. medium_get_stream_o\<cdot>(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>(\<up>(Msg m) \<bullet> s)) = \<up>out \<bullet> medium_get_stream_o\<cdot>(spf2 \<rightleftharpoons> mediumIn_stream_i\<cdot>s)
    \<and> spf2\<in>uspecSet\<cdot>medUnfair \<and> out\<in>{-, Msg m}"
  sorry

lemma medunfair_step_stream_msg_dom: assumes "spf\<in>uspecSet\<cdot>medUnfair"
  shows "\<exists>spf2. tsynDom\<cdot>(medium_get_stream_o\<cdot>(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>(\<up>(Msg m) \<bullet> s))) \<sqsubseteq> 
    insert m (tsynDom\<cdot>(medium_get_stream_o\<cdot>(spf2 \<rightleftharpoons> mediumIn_stream_i\<cdot>s)))
    \<and> spf2\<in>uspecSet\<cdot>medUnfair"
  sorry

lemma medunfair_dom [simp]: assumes "spf \<in> uspecSet\<cdot>medUnfair"
  shows "tsynDom\<cdot>(medium_get_stream_o\<cdot>(spf \<rightleftharpoons> mediumIn_stream_i\<cdot>s)) \<sqsubseteq> tsynDom\<cdot>s"
  using assms apply(induction s arbitrary: spf rule:ind)
  apply(rule admI, auto)
   apply (smt ch2ch_Rep_cfunR contlub_cfun_arg lub_mono medapply_subst)
  apply(rename_tac m s spf)                  
  apply(case_tac m, auto simp add: tsyndom_sconc_null tsyndom_sconc_msg)
  defer
  apply (metis medunfair_step_stream_tick tsyndom_sconc_null)
  using medunfair_step_stream_msg_dom tsyndom_sconc_msg
  by (smt SetPcpo.less_set_def insert_iff subset_iff)


end