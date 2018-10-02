theory medGeneralAut

imports PreludeMed automat.ndaTotal

begin


(* The first parameter describes what happens in the drop-case *)
(* Normally f is constant and returns "-" ... But it can also alter the message *)
fun medGeneralTransitionH :: "nat set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medGeneralTransitionH _      _         state     -    = { (state,    -   )            }" |   (* Time *)
"medGeneralTransitionH _ dropBehaviour (Suc n) (Msg m) = { (  n  ,   out  ) | out . out\<in>(dropBehaviour m)   }" |  (* Drop *)
"medGeneralTransitionH resetSet  _        0    (Msg m) = { (  n  , (Msg m)) | n. n \<in> resetSet}"     (* Pass *)

definition tsynDelay :: "nat \<Rightarrow> 'm::message tsyn SB \<rightarrow> 'm tsyn SB" where
"tsynDelay n = ubConcEq (sbNTimes n (tsynbNull  (\<C> ''in'')))" 

(* ToDo: use delaySet to nondeterministically delay everything *)
fun medGeneralTransition :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a medMessage tsyn SB) set rev)" where
"medGeneralTransition delaySet resetSet dropBehaviour (s,f) = (if sbeDom f = medInDom then 
    Rev {(sNext, tsynDelay n\<cdot>(medOut out)) | n sNext out. n\<in>delaySet  \<and> (sNext, out)\<in>(medGeneralTransitionH resetSet dropBehaviour s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))} 
  else Rev {undefined})"

lift_definition medGeneralAut :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState, 'a medMessage tsyn) ndAutomaton" is 
  "\<lambda>delaySet resetSet dropBehaviour. (medGeneralTransition delaySet resetSet dropBehaviour, Rev {(n, medOut - )| n. n \<in> resetSet}, Discr medInDom, Discr medOutDom)"
  by (simp add: medInDom_def)

definition medGeneral :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medGeneral delaySet resetSet dropBehaviour n = nda_h (medGeneralAut delaySet resetSet dropBehaviour) n"



definition medFair :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medFair = medGeneral {0} UNIV (\<lambda>s. {-})"  (* No delay, normal counter, normal drop *)

definition medFairDelay :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medFairDelay = medGeneral UNIV UNIV (\<lambda>s. {-})"  (* arbitrary but finite delay, normal counter, normal drop *)

definition medFairDelayTupel :: "medState \<Rightarrow> ('a\<times>'b) medMessage tsyn SPS" where
"medFairDelayTupel = medGeneral UNIV UNIV (\<lambda>(a,b). {Msg (undefined, b), -, Msg (a, undefined)})"  
  (* arbitrary but finite delay, normal counter, drop can alter elements and only delete part of the information *)

definition medGurantee :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medGurantee = medGeneral {0} {n. n\<le>5} (\<lambda>s. {-})" 
  (* No delay, Passes at least every 5th message, normal drop *)




lemma medgen_dom[simp]: "ndaDom\<cdot>(medGeneralAut d r b ) = medInDom"
  by (simp add: medGeneralAut.rep_eq ndaDom.rep_eq)

lemma medgen_ran[simp]: "ndaRan\<cdot>(medGeneralAut d r b ) = medOutDom"
  by (simp add: medGeneralAut.rep_eq ndaRan.rep_eq)

lemma medgen_trans[simp]: "ndaTransition\<cdot>(medGeneralAut Delay Reset Drop) = medGeneralTransition Delay Reset Drop"
  by (simp add: medGeneralAut.rep_eq ndaTransition.rep_eq)

lemma medgen_transh_total:  "Reset\<noteq>{} \<Longrightarrow> (\<And>m. Drop m \<noteq> {}) \<Longrightarrow>  medGeneralTransitionH Reset Drop s m \<noteq> {}"
  apply(cases m)
   apply(cases s)
  by simp_all

lemma medgen_trans_total_h: "Delay\<noteq>{} \<Longrightarrow> Reset\<noteq>{} \<Longrightarrow> (\<And>m. Drop m \<noteq> {}) \<Longrightarrow> medGeneralTransition Delay Reset Drop (s,sbe) \<noteq> Rev {}"
  apply(simp)
  apply(cases "sbeDom sbe \<noteq> medInDom")
   apply simp
  apply auto
  by (metis all_not_in_conv medgen_transh_total old.prod.exhaust)

lemma medgen_trans_total[simp]: "Delay\<noteq>{} \<Longrightarrow> Reset\<noteq>{} \<Longrightarrow> (\<And>m. Drop m \<noteq> {}) \<Longrightarrow> medGeneralTransition Delay Reset Drop s \<noteq> Rev {}"
  by (metis medgen_trans_total_h surj_pair)


lemma medgen_trans_tick [simp]: 
    "medGeneralTransition Delay Reset Drop (state, (medInElem -)) = Rev {(state, tsynDelay n\<cdot>(medOut -)) | n::nat. n \<in> Delay}"
  by(simp add: sbeNull.rep_eq medInDom_def medInElem.simps)

lemma medfair_transition_msg_suc [simp]: 
  shows "medGeneralTransition Delay Reset Drop (Suc n, (medInElem (Msg m))) = Rev {(n, tsynDelay na\<cdot>(medOut out)) |(na::nat) out::'a tsyn. na \<in> Delay \<and> out \<in> Drop m}"
  by(simp add: medInMsgElem.rep_eq medInDom_def medInElem.simps)

lemma medfair_transition_msg_0 [simp]: 
    "medGeneralTransition Delay Reset Drop (0, (medInElem (Msg m))) = Rev {(sNext, tsynDelay n\<cdot>(medOut (\<M> m))) |(n::nat) sNext::nat. n \<in> Delay \<and> sNext \<in> Reset}"
  by(simp add: medInMsgElem.rep_eq medInDom_def image_iff medInElem.simps)


lemma medinelem_get_id[simp]: "(medMessageTransform Rep_sbElem (medInElem m)\<rightharpoonup>\<C> ''in'') = m"
apply(cases m)
  by(simp add: medInElem.simps medInMsgElem.rep_eq sbeNull.rep_eq medInDom_def)+

lemma medgen_init_total[simp]: assumes "Reset\<noteq>{}" 
  shows "ndaInitialState\<cdot>(medGeneralAut Delay Reset Drop) \<noteq> Rev {}"
  by(simp add: ndaInitialState.rep_eq medGeneralAut.rep_eq assms)

lemma med_gen_step_tick: assumes "Delay\<noteq>{}" and  "Reset\<noteq>{}" and "(\<And>m. Drop m \<noteq> {})"
shows "spsConcIn (medIn -) (medGeneral Delay Reset Drop s) = 
  ndaConcOutFlatten medInDom medOutDom (Rev {(s, tsynDelay n\<cdot>(medOut -)) | n::nat. n \<in> Delay}) (medGeneral Delay Reset Drop)"
  apply(simp add: medIn_def medGeneral_def)
  apply(subst nda_h_I)
     apply simp_all
   apply(rule nda_consistent)
    apply(simp_all add: assms )
  by (metis medGeneral_def)


lemma med_gen_step_msg_suc: assumes "Delay\<noteq>{}" and  "Reset\<noteq>{}" and "(\<And>m. Drop m \<noteq> {})"
shows "spsConcIn (medIn (Msg m)) (medGeneral Delay Reset Drop (Suc s)) = 
  ndaConcOutFlatten medInDom medOutDom (Rev {(s, tsynDelay n\<cdot>(medOut out)) |(n::nat) out::'a tsyn. n \<in> Delay \<and> out \<in> Drop m}) (medGeneral Delay Reset Drop)"
  apply(simp add: medIn_def medGeneral_def)
  apply(subst nda_h_I)
     apply simp_all
   apply(rule nda_consistent)
    apply(simp_all add: assms )
  by (metis medGeneral_def)


lemma med_gen_step_msg_0: assumes "Delay\<noteq>{}" and  "Reset\<noteq>{}" and "(\<And>m. Drop m \<noteq> {})"
shows "spsConcIn (medIn (Msg m)) (medGeneral Delay Reset Drop 0) = 
  ndaConcOutFlatten medInDom medOutDom (Rev {(sNext, tsynDelay n\<cdot>(medOut (\<M> m))) |(n::nat) sNext::nat. n \<in> Delay \<and> sNext \<in> Reset}) (medGeneral Delay Reset Drop)"
  apply(simp add: medIn_def medGeneral_def)
  apply(subst nda_h_I)
     apply simp_all
   apply(rule nda_consistent)
    apply(simp_all add: assms )
  by (metis medGeneral_def)


end