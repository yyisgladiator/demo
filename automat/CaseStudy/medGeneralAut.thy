theory medGeneralAut

imports PreludeMed

begin


(* The first parameter describes what happens in the drop-case *)
(* Normally f is constant and returns "-" ... But it can also alter the message *)
fun medGeneralTransitionH :: "nat set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medGeneralTransitionH _      _         state     -    = { (state,    -   )            }" |   (* Time *)
"medGeneralTransitionH _ dropBehaviour (Suc n) (Msg m) = { (  n  ,   out  ) | out . out\<in>(dropBehaviour m)   }" |  (* Drop *)
"medGeneralTransitionH resetSet  _        0    (Msg m) = { (  n  , (Msg m)) | n. n \<in> resetSet}"     (* Pass *)

fun tsynDelay :: "nat \<Rightarrow> 'm tsyn SB \<Rightarrow> 'm tsyn SB" where
"tsynDelay n tsb = undefined" (* ToDo: Should be -- ubConcEq (sbNTimes n (tsynNull (ubDom tsb))) tsb *)

(* ToDo: use delaySet to nondeterministically delay everything *)
fun medGeneralTransition :: "nat set \<Rightarrow> medState set \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a medMessage tsyn SB) set rev)" where
"medGeneralTransition delaySet resetSet dropBehaviour (s,f) = (if sbeDom f = medInDom then 
    Rev {(s, tsynDelay n (medOut out)) | n s out. n\<in>delaySet  \<and> (s, out)\<in>(medGeneralTransitionH resetSet dropBehaviour s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))} 
  else undefined)"

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




lemma medfairaut_dom[simp]: "ndaDom\<cdot>(medGeneralAut d r b ) = medInDom"
  by (simp add: medGeneralAut.rep_eq ndaDom.rep_eq)

lemma medfairaut_ran[simp]: "ndaRan\<cdot>(medGeneralAut d r b ) = medOutDom"
  by (simp add: medGeneralAut.rep_eq ndaRan.rep_eq)


(*
lemma medfair_transition_tick [simp]: "medGeneralTransition (state, (medInElem -)) = Rev {(state, medOut -)}"
  by(simp add: sbeNull.rep_eq medInDom_def medInElem.simps)

lemma medfair_transition_msg_suc [simp]: "medGeneralTransition (Suc n, (medInElem (Msg m))) = Rev {(n, medOut -)}"
  by(simp add: medInMsgElem.rep_eq medInDom_def medInElem.simps)

lemma medfair_transition_msg_0 [simp]: "medGeneralTransition (0, (medInElem (Msg m))) = Rev {(n, medOut (Msg m)) | n. True}"
  by(auto simp add: medInMsgElem.rep_eq medInDom_def image_iff medInElem.simps)
*)


end