(*
 * DO NOT MODIFY!
 * This file was generated from MediumRS.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Aug 15, 2018 3:13:07 PM by isartransformer 1.0.0
 *)
theory MediumRSAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype MediumRSSubstate = Single

(* And these have also the variables *)
datatype MediumRSState = MediumRSState MediumRSSubstate (* c = *) "nat"

fun getMediumRSSubState :: "MediumRSState \<Rightarrow> MediumRSSubstate" where
"getMediumRSSubState (MediumRSState state_s automaton_c) = state_s"

fun getC :: "MediumRSState \<Rightarrow> nat" where
"getC (MediumRSState _ automaton_c) = automaton_c"
    


fun mediumRSTransitionH :: "(MediumRSState \<times> (abpMessage tsyn)) \<Rightarrow> ((MediumRSState \<times> abpMessage tsyn SB) set rev)" where
    "mediumRSTransitionH (MediumRSState Single automaton_c, ((*ar\<mapsto>*)Msg (ABPBool a))) = 
       (if(automaton_c>0) then Rev {(MediumRSState Single (automaton_c-1),(tsynbNull (\<C> ''as'')))}
       else if(automaton_c=0) then Rev {(MediumRSState Single (c),(createAsBundle (a)))| (c). True}
       else Rev {(MediumRSState Single automaton_c, ((tsynbNull (\<C> ''as''))))})"  |

    "mediumRSTransitionH (MediumRSState Single automaton_c, ((*ar\<mapsto>*)null)) = 
       (Rev {(MediumRSState Single automaton_c,(tsynbNull (\<C> ''as'')))})"  

fun mediumRSTransition :: "(MediumRSState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> ((MediumRSState \<times> abpMessage tsyn SB) set rev)" where
"mediumRSTransition (s,f) = (if dom(f) = {\<C> ''ar''} then mediumRSTransitionH (s,(f\<rightharpoonup>\<C> ''ar'')) else undefined)"

lift_definition MediumRSAutomaton :: "(MediumRSState, abpMessage tsyn) ndAutomaton" is "(mediumRSTransition, Rev {(MediumRSState Single c, (tsynbNull (\<C> ''as'')))| c. True}, Discr {\<C> ''ar''}, Discr {\<C> ''as''})"
  by simp

definition MediumRSSPF :: "abpMessage tsyn SPS" where
"MediumRSSPF = nda_H MediumRSAutomaton"

end