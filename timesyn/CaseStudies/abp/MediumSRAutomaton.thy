(*
 * DO NOT MODIFY!
 * This file was generated from MediumSR.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Jun 29, 2018 5:23:56 PM by transformer 1.0.0
 *)
theory MediumSRAutomaton

imports "../AutomatonPrelude" "../../../untimed/CaseStudy/NDA"

begin

(* This are the actual states from MAA *)
datatype MediumSRSubstate = Single

(* And these have also the variables *)
datatype MediumSRState = State MediumSRSubstate (* c = *) "nat"

fun getSubState :: "MediumSRState \<Rightarrow> MediumSRSubstate" where
"getSubState (State state_s automaton_c) = state_s"

fun getC :: "MediumSRState \<Rightarrow> nat" where
"getC (State _ automaton_c) = automaton_c"
    


fun mediumSRTransitionH :: "(MediumSRState \<times> (abpMessage tsyn)) \<Rightarrow> ((MediumSRState \<times> abpMessage tsyn SB) set rev)" where
    "mediumSRTransitionH (State Single automaton_c, ((*ds\<mapsto>*)Msg (Pair_nat_bool a))) = 
       (if(automaton_c=0) then Rev {(State Single (c),(tsynbNull (\<C> ''dr'')))| (c). (c) < 50}
       else if(automaton_c>0) then Rev {(State Single (automaton_c-1),(tsynbNull (\<C> ''dr'')))}
       else if(True) then Rev {(State Single automaton_c,(tsynbNull (\<C> ''dr'')))}
       else Rev {(State Single automaton_c, ((tsynbNull (\<C> ''dr''))))})"  |

    "mediumSRTransitionH (State Single automaton_c, ((*ds\<mapsto>*)null)) = 
       (Rev {(State Single automaton_c,(tsynbNull (\<C> ''dr'')))})"  

fun mediumSRTransition :: "(MediumSRState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> ((MediumSRState \<times> abpMessage tsyn SB) set rev)" where
"mediumSRTransition (s,f) = (if dom(f) = {\<C> ''ds''} then mediumSRTransitionH (s,(f\<rightharpoonup>\<C> ''ds'')) else undefined)"

lift_definition MediumSRAutomaton :: "(MediumSRState, abpMessage tsyn) NDA" is "(mediumSRTransition, Rev {(State Single c, (tsynbNull (\<C> ''dr'')))| c. c < 50}, Discr {\<C> ''ds''}, Discr {\<C> ''dr''})"
  by simp

definition MediumSRSPF :: "abpMessage tsyn SPS" where
"MediumSRSPF = nda_H\<cdot>MediumSRAutomaton"

end