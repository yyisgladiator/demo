theory medUnfairAut

imports PreludeMed

begin


datatype medUnfairState = TheOne

(* Superset of the Fair-Transition *)
fun medUnfairTransitionH :: "medUnfairState \<Rightarrow> 'a tsyn \<Rightarrow> (medUnfairState \<times> 'a tsyn) set" where
"medUnfairTransitionH  _     -    = { (TheOne,    -   )            }" |
"medUnfairTransitionH _ (Msg m) = { (  TheOne  ,    -   ) , (TheOne, Msg m)    }" 

fun medUnfairTransition :: "(medUnfairState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medUnfairState \<times> 'a medMessage tsyn SB) set rev)" where
"medUnfairTransition (s,f) = (if sbeDom f = medInDom then 
    Rev ((\<lambda>(s,out). (s, medOut out)) ` (medUnfairTransitionH s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))) 
  else undefined)"

lift_definition medUnfairAut :: "(medUnfairState, 'a medMessage tsyn) ndAutomaton" is 
  "(medUnfairTransition, Rev {(n, medOut - )| n. True}, Discr medInDom, Discr medOutDom)"
  by (simp add: medInDom_def)

definition medUnfair :: "'a medMessage tsyn SPS" where
"medUnfair = nda_h medUnfairAut TheOne"





lemma medunfairaut_dom[simp]: "ndaDom\<cdot>medUnfairAut = medInDom"
  by (simp add: medUnfairAut.rep_eq ndaDom.rep_eq)

lemma medunfairaut_ran[simp]: "ndaRan\<cdot>medUnfairAut = medOutDom"
  by (simp add: medUnfairAut.rep_eq ndaRan.rep_eq)


lemma medunfair_transition_tick [simp]: "medUnfairTransition (TheOne, (medInElem -)) = Rev {(TheOne, medOut -)}"
  by(simp add: sbeNull.rep_eq medInDom_def medInElem.simps)

lemma medunfair_transition_msg [simp]: "medUnfairTransition (TheOne, (medInElem (Msg m))) = Rev {(TheOne, medOut -), (TheOne, medOut (Msg m))}"
  by(simp add: medInMsgElem.rep_eq medInDom_def medInElem.simps)


end