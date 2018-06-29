(*
 * DO NOT MODIFY!
 * This file was generated from MediumRS.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Jun 29, 2018 5:23:56 PM by transformer 1.0.0
 *)
theory MediumRSAutomaton

imports "../AutomatonPrelude" "../../../untimed/CaseStudy/NDA"

begin

(* This are the actual states from MAA *)
datatype MediumRSSubstate = Single

(* And these have also the variables *)
datatype MediumRSState = State MediumRSSubstate (* c = *) "nat"

fun getSubState :: "MediumRSState \<Rightarrow> MediumRSSubstate" where
"getSubState (State state_s automaton_c) = state_s"

fun getC :: "MediumRSState \<Rightarrow> nat" where
"getC (State _ automaton_c) = automaton_c"
    


fun mediumRSTransitionH :: "(MediumRSState \<times> (abpMessage tsyn)) \<Rightarrow> ((MediumRSState \<times> abpMessage tsyn SB) set rev)" where
    "mediumRSTransitionH (State Single automaton_c, ((*ar\<mapsto>*)Msg (Bool a))) = 
       (if(automaton_c=0) then Rev {(State Single (c),(tsynbNull (\<C> ''as'')))| (c). (c) < 50}
       else if(automaton_c>0) then Rev {(State Single (automaton_c-1),(tsynbNull (\<C> ''as'')))}
       else if(True) then Rev {(State Single automaton_c,(tsynbNull (\<C> ''as'')))}
       else Rev {(State Single automaton_c, ((tsynbNull (\<C> ''as''))))})"  |

    "mediumRSTransitionH (State Single automaton_c, ((*ar\<mapsto>*)null)) = 
       (Rev {(State Single automaton_c,(tsynbNull (\<C> ''as'')))})"  

fun mediumRSTransition :: "(MediumRSState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> ((MediumRSState \<times> abpMessage tsyn SB) set rev)" where
"mediumRSTransition (s,f) = (if dom(f) = {\<C> ''ar''} then mediumRSTransitionH (s,(f\<rightharpoonup>\<C> ''ar'')) else undefined)"

lift_definition MediumRSAutomaton :: "(MediumRSState, abpMessage tsyn) NDA" is "(mediumRSTransition, Rev {(State Single c, (tsynbNull (\<C> ''as'')))| c. c < 50}, Discr {\<C> ''ar''}, Discr {\<C> ''as''})"
  by simp

definition MediumRSSPF :: "abpMessage tsyn SPS" where
"MediumRSSPF = nda_H\<cdot>MediumRSAutomaton"

end