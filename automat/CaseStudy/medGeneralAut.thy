theory medGeneralAut

imports PreludeMed

begin


(* The first parameter describes what happens in the drop-case *)
(* Normally f is constant and returns "-" ... But it can also alter the message *)
fun medGeneralTransitionH :: "('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medGeneralTransitionH F  state     -    = { (state,    -   )            }" |   (* Time *)
"medGeneralTransitionH F (Suc n) (Msg m) = { (  n  ,   out  ) | out . out\<in>(F m)   }" |  (* Drop *)
"medGeneralTransitionH F    0    (Msg m) = { (  n  , (Msg m)) | n . True }"     (* Pass *)

fun tsynDelay :: "nat \<Rightarrow> 'm tsyn SB \<Rightarrow> 'm tsyn SB" where
"tsynDelay n tsb = undefined" (* ToDo: Should be -- ubConcEq (sbNTimes n (tsynNull (ubDom tsb))) tsb *)

(* ToDo: use delayLimit to nondeterministically delay everything *)
fun medGeneralTransition :: "lnat \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a medMessage tsyn SB) set rev)" where
"medGeneralTransition delayLimit F (s,f) = (if sbeDom f = medInDom then 
    Rev {(s, tsynDelay n (medOut out)) | n s out. Fin n \<le>delayLimit \<and> (s, out)\<in>(medGeneralTransitionH F s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))} 
  else undefined)"

lift_definition medGeneralAut :: "lnat \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> (medState, 'a medMessage tsyn) ndAutomaton" is 
  "\<lambda>delayLimit F. (medGeneralTransition delayLimit F, Rev {(n, medOut - )| n. True}, Discr medInDom, Discr medOutDom)"
  by (simp add: medInDom_def)

definition medGeneral :: "lnat \<Rightarrow> ('a \<Rightarrow> ('a tsyn set)) \<Rightarrow> medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medGeneral delayLimit F n = nda_h (medGeneralAut delayLimit F) n"



definition medFair :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medFair = medGeneral 0 (\<lambda>s. {-})"  (* No delay, normal drop *)

definition medFairDelay :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medFairDelay = medGeneral \<infinity> (\<lambda>s. {-})"  (* arbitrary but finite delay, normal drop *)

definition medFairDelayTupel :: "medState \<Rightarrow> ('a\<times>'b) medMessage tsyn SPS" where
"medFairDelayTupel = medGeneral \<infinity> (\<lambda>(a,b). {Msg (undefined, b), -, Msg (a, undefined)})"  
  (* arbitrary but finite delay, drop can alter elements and only delete part of the information *)




lemma medfairaut_dom[simp]: "ndaDom\<cdot>medFairAut = medInDom"
  by (simp add: medFairAut.rep_eq ndaDom.rep_eq)

lemma medfairaut_ran[simp]: "ndaRan\<cdot>medFairAut = medOutDom"
  by (simp add: medFairAut.rep_eq ndaRan.rep_eq)


lemma medfair_transition_tick [simp]: "medFairTransition (state, (medInElem -)) = Rev {(state, medOut -)}"
  by(simp add: sbeNull.rep_eq medInDom_def medInElem.simps)

lemma medfair_transition_msg_suc [simp]: "medFairTransition (Suc n, (medInElem (Msg m))) = Rev {(n, medOut -)}"
  by(simp add: medInMsgElem.rep_eq medInDom_def medInElem.simps)

lemma medfair_transition_msg_0 [simp]: "medFairTransition (0, (medInElem (Msg m))) = Rev {(n, medOut (Msg m)) | n. True}"
  by(auto simp add: medInMsgElem.rep_eq medInDom_def image_iff medInElem.simps)

end