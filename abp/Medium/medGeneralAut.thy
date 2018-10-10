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

fun medGeneralTransition :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState \<times> 'a mediumMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a mediumMessage tsyn SB) set rev)" where
"medGeneralTransition delaySet resetSet dropBehaviour (s,f) = 
  (let inMsg = mediumElem_get_ar f;
       outSet = {(sNext,(mediumOut_as out)) | sNext out.(sNext, out)\<in>(medGeneralTransitionH resetSet dropBehaviour s inMsg)}
  in
  (if sbeDom f = mediumDom then
    (if(inMsg = -) then Rev outSet else Rev {(sNext, tsynDelay n\<cdot>outElem)| n sNext outElem . n\<in>delaySet \<and> (sNext, outElem)\<in>outSet})
  else Rev {undefined}))"


lift_definition medGeneralAut :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState, 'a mediumMessage tsyn) ndAutomaton" is 
  "\<lambda>delaySet resetSet dropBehaviour. (medGeneralTransition delaySet resetSet dropBehaviour, Rev {(n, mediumOut_as - )| n. n \<in> resetSet}, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def)

definition medGeneral :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> medState \<Rightarrow> 'a mediumMessage tsyn SPS" where
"medGeneral delaySet resetSet dropBehaviour n = nda_h (medGeneralAut delaySet resetSet dropBehaviour) n"



definition medFair :: "medState \<Rightarrow> 'a mediumMessage tsyn SPS" where
"medFair = medGeneral {0} UNIV (\<lambda>s. {-})"  (* No delay, normal counter, normal drop *)

definition medFairDelay :: "medState \<Rightarrow> 'a mediumMessage tsyn SPS" where
"medFairDelay = medGeneral UNIV UNIV (\<lambda>s. {-})"  (* arbitrary but finite delay, normal counter, normal drop *)

definition medFairDelayTupel :: "medState \<Rightarrow> ('a\<times>'b) mediumMessage tsyn SPS" where
"medFairDelayTupel = medGeneral UNIV UNIV (\<lambda>(a,b). {Msg (undefined, b), -, Msg (a, undefined)})"  
  (* arbitrary but finite delay, normal counter, drop can alter elements and only delete part of the information *)

definition medGurantee :: "medState \<Rightarrow> 'a mediumMessage tsyn SPS" where
"medGurantee = medGeneral {0} {n. n\<le>5} (\<lambda>s. {-})" 
  (* No delay, Passes at least every 5th message, normal drop *)




lemma medgen_dom[simp]: "ndaDom\<cdot>(medGeneralAut d r b ) = mediumDom"
  by (simp add: medGeneralAut.rep_eq ndaDom.rep_eq)

lemma medgen_ran[simp]: "ndaRan\<cdot>(medGeneralAut d r b ) = mediumRan"
  by (simp add: medGeneralAut.rep_eq ndaRan.rep_eq)

lemma medgen_trans[simp]: "ndaTransition\<cdot>(medGeneralAut Delay Reset Drop) = medGeneralTransition Delay Reset Drop"
  by (simp add: medGeneralAut.rep_eq ndaTransition.rep_eq)

lemma medgen_transh_total:  "Reset\<noteq>{} \<Longrightarrow> (\<And>m. Drop m \<noteq> {}) \<Longrightarrow>  medGeneralTransitionH Reset Drop s m \<noteq> {}"
  apply(cases m)
   apply(cases s)
  by simp_all

lemma medgen_trans_total_h: "Delay\<noteq>{} \<Longrightarrow> Reset\<noteq>{} \<Longrightarrow> (\<And>m. Drop m \<noteq> {}) \<Longrightarrow> medGeneralTransition Delay Reset Drop (s,sbe) \<noteq> Rev {}"
  apply(simp)
  apply(cases "sbeDom sbe \<noteq> mediumDom")
   apply simp
  apply (auto simp add: Let_def)
  apply(cases "mediumElem_get_ar sbe = -")
  apply auto
  by (metis all_not_in_conv medgen_transh_total old.prod.exhaust)

lemma medgen_trans_total[simp]: "Delay\<noteq>{} \<Longrightarrow> Reset\<noteq>{} \<Longrightarrow> (\<And>m. Drop m \<noteq> {}) \<Longrightarrow> medGeneralTransition Delay Reset Drop s \<noteq> Rev {}"
  by (metis medgen_trans_total_h surj_pair)


lemma medgen_trans_tick [simp]: 
    "Delay\<noteq>{} \<Longrightarrow> medGeneralTransition Delay Reset Drop (state, (mediumElemIn_ar -)) = Rev {(state, mediumOut_as -)}"
  by auto

lemma medfair_transition_msg_suc [simp]: 
  shows "medGeneralTransition Delay Reset Drop (Suc n, (mediumElemIn_ar (Msg m))) = Rev {(n, tsynDelay na\<cdot>(mediumOut_as out)) |(na::nat) out::'a tsyn. na \<in> Delay \<and> out \<in> Drop m}"
  by auto
 

lemma medfair_transition_msg_0 [simp]: 
    "medGeneralTransition Delay Reset Drop (0, (mediumElemIn_ar (Msg m))) = Rev {(sNext, tsynDelay n\<cdot>(mediumOut_as (\<M> m))) |(n::nat) sNext::nat. n \<in> Delay \<and> sNext \<in> Reset}"
  by simp


lemma medgen_init_total[simp]: assumes "Reset\<noteq>{}" 
  shows "ndaInitialState\<cdot>(medGeneralAut Delay Reset Drop) \<noteq> Rev {}"
  by(simp add: ndaInitialState.rep_eq medGeneralAut.rep_eq assms)

lemma med_gen_step_tick: assumes "Delay\<noteq>{}" and  "Reset\<noteq>{}" and "(\<And>m. Drop m \<noteq> {})"
shows "spsConcIn (mediumIn_ar -) (medGeneral Delay Reset Drop s) = 
  ndaConcOutFlatten mediumDom mediumRan (Rev {(s, (mediumOut_as -))}) (medGeneral Delay Reset Drop)"
  apply(simp add: mediumIn_ar_def medGeneral_def)
  apply(subst nda_h_I)
     apply simp_all
   apply(rule nda_consistent)
    apply(simp_all add: assms )
  by (metis medGeneral_def)


lemma med_gen_step_msg_suc: assumes "Delay\<noteq>{}" and  "Reset\<noteq>{}" and "(\<And>m. Drop m \<noteq> {})"
shows "spsConcIn (mediumIn_ar (Msg m)) (medGeneral Delay Reset Drop (Suc s)) = 
  ndaConcOutFlatten mediumDom mediumRan (Rev {(s, tsynDelay n\<cdot>(mediumOut_as out)) |(n::nat) out::'a tsyn. n \<in> Delay \<and> out \<in> Drop m}) (medGeneral Delay Reset Drop)"
  apply(simp add: mediumIn_ar_def medGeneral_def)
  apply(subst nda_h_I)
     apply simp_all
   apply(rule nda_consistent)
    apply(auto simp add: assms)
  unfolding medGeneral_def
  by (metis (no_types, hide_lams))


lemma med_gen_step_msg_0: assumes "Delay\<noteq>{}" and  "Reset\<noteq>{}" and "(\<And>m. Drop m \<noteq> {})"
shows "spsConcIn (mediumIn_ar (Msg m)) (medGeneral Delay Reset Drop 0) = 
  ndaConcOutFlatten mediumDom mediumRan (Rev {(sNext, tsynDelay n\<cdot>(mediumOut_as (\<M> m))) |(n::nat) sNext::nat. n \<in> Delay \<and> sNext \<in> Reset}) (medGeneral Delay Reset Drop)"
  apply(simp add: mediumIn_ar_def medGeneral_def)
  apply(subst nda_h_I)
     apply simp_all
   apply(rule nda_consistent)
    apply(simp_all add: assms )
  by (metis medGeneral_def)


end