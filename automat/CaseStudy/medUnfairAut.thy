theory medUnfairAut

imports PreludeMed

begin


(* Superset of the Fair-Transition *)
fun medUnfairTransitionH :: "medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medUnfairTransitionH  state     -    = { (state,    -   )            }" |
"medUnfairTransitionH (Suc n) (Msg m) = { (  n  ,    -   )            }" |
"medUnfairTransitionH    0    (Msg m) = { (  n  , (Msg m)) | n . True } \<union> { (0, -) }"

fun medUnfairTransition :: "(medState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a medMessage tsyn SB) set rev)" where
"medUnfairTransition (s,f) = (if dom(Rep_sbElem f) = medInDom then 
    Rev ((\<lambda>(s,out). (s, medOut out)) ` (medUnfairTransitionH s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))) 
  else undefined)"

lift_definition medUnfairAut :: "(medState, 'a medMessage tsyn) ndAutomaton" is 
  "(medUnfairTransition, Rev {(n, medOut - )| n. True}, Discr medInDom, Discr medOutDom)"
  by (simp add: medInDom_def)

definition medUnfair :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medUnfair n = nda_h medUnfairAut n"





lemma medunfairaut_dom[simp]: "ndaDom\<cdot>medUnfairAut = medInDom"
  by (simp add: medUnfairAut.rep_eq ndaDom.rep_eq)

lemma medunfairaut_ran[simp]: "ndaRan\<cdot>medUnfairAut = medOutDom"
  by (simp add: medUnfairAut.rep_eq ndaRan.rep_eq)



end