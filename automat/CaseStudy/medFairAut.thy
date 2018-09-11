theory medFairAut

imports PreludeMed

begin


(* Subset of the Unfair-Transition *)
fun medFairTransitionH :: "medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medFairTransitionH  state     -    = { (state,    -   )            }" |
"medFairTransitionH (Suc n) (Msg m) = { (  n  ,    -   )            }" |
"medFairTransitionH    0    (Msg m) = { (  n  , (Msg m)) | n . True }"

fun medFairTransition :: "(medState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a medMessage tsyn SB) set rev)" where
"medFairTransition (s,f) = (if sbeDom f = medInDom then 
    Rev ((\<lambda>(s,out). (s, medOut out)) ` (medFairTransitionH s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))) 
  else undefined)"

lift_definition medFairAut :: "(medState, 'a medMessage tsyn) ndAutomaton" is 
  "(medFairTransition, Rev {(n, medOut - )| n. True}, Discr medInDom, Discr medOutDom)"
  by (simp add: medInDom_def)

definition medFair :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medFair n = nda_h medFairAut n"





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