theory medFairAut

imports PreludeMed

begin


(* Subset of the Unfair-Transition *)
fun medFairTransitionH :: "medState \<Rightarrow> 'a tsyn \<Rightarrow> (medState \<times> 'a tsyn) set" where
"medFairTransitionH  state     -    = { (state,    -   )            }" |
"medFairTransitionH (Suc n) (Msg m) = { (  n  ,    -   )            }" |
"medFairTransitionH    0    (Msg m) = { (  n  , (Msg m)) | n . True }"

fun medFairTransition :: "(medState \<times> 'a medMessage tsyn sbElem) \<Rightarrow> ((medState \<times> 'a medMessage tsyn SB) set rev)" where
"medFairTransition (s,f) = (if dom(Rep_sbElem f) = medInDom then 
    Rev ((\<lambda>(s,out). (s, medOut out)) ` (medFairTransitionH s (medMessageTransform ((Rep_sbElem f)\<rightharpoonup>(\<C> ''in''))))) 
  else undefined)"

lift_definition medFairAut :: "(medState, 'a medMessage tsyn) ndAutomaton" is 
  "(medFairTransition, Rev {(n, medOut - )| n. True}, Discr medInDom, Discr medOutDom)"
  by (simp add: medInDom_def)

definition medFair :: "medState \<Rightarrow> 'a medMessage tsyn SPS" where
"medFair n = nda_h medFairAut n"



end