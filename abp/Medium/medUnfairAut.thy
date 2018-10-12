theory medUnfairAut

imports PreludeMed automat.ndAutomaton

begin


(* Superset of the Fair-Transition *)
fun medUnfairTransitionH :: "medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medUnfairTransitionH  state     -    = { (state,    -   )            }" |
"medUnfairTransitionH (Suc n) (Msg m) = { (  n  ,    -   )            }" |
"medUnfairTransitionH    0    (Msg m) = { (  n  , (Msg m)) | n . True } \<union> { (0, -) }"

fun medUnfairTransition :: "(medState \<times> 'a mediumMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a mediumMessage tsyn SB) set rev)" where
"medUnfairTransition (s,f) = (if sbeDom f = mediumDom then 
    Rev ((\<lambda>(s,out). (s, mediumOut_o out)) ` (medUnfairTransitionH s (mediumElem_get_i f))) 
  else undefined)"

lift_definition medUnfairAut :: "(medState, 'a mediumMessage tsyn) ndAutomaton" is 
  "(medUnfairTransition, Rev {(n, mediumOut_o - )| n. True}, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def)

definition medUnfair :: "medState \<Rightarrow> 'a mediumMessage tsyn SPS" where
"medUnfair n = nda_h medUnfairAut n"





lemma medunfairaut_dom[simp]: "ndaDom\<cdot>medUnfairAut = mediumDom"
  by (simp add: medUnfairAut.rep_eq ndaDom.rep_eq)

lemma medunfairaut_ran[simp]: "ndaRan\<cdot>medUnfairAut = mediumRan"
  by (simp add: medUnfairAut.rep_eq ndaRan.rep_eq)


lemma medunfair_transition_tick [simp]: "medUnfairTransition (state, (mediumElemIn_i -)) = Rev {(state, mediumOut_o -)}"
  by simp

lemma medunfair_transition_msg_suc [simp]: "medUnfairTransition (Suc n, (mediumElemIn_i (Msg m))) = Rev {(n, mediumOut_o -)}"
  by simp

lemma medunfair_transition_msg_0 [simp]: "medUnfairTransition (0, (mediumElemIn_i (Msg m))) = Rev ({(n, mediumOut_o (Msg m)) | n. True} \<union> { (0, mediumOut_o -) })"
  by auto


end