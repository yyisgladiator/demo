(*
 * DO NOT MODIFY!
 * This file was generated from MediumSR.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Aug 15, 2018 3:13:07 PM by isartransformer 1.0.0
 *)
theory MediumSRAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype MediumSRSubstate = Single

(* And these have also the variables *)
datatype MediumSRState = MediumSRState MediumSRSubstate (* c = *) "nat"

fun getMediumSRSubState :: "MediumSRState \<Rightarrow> MediumSRSubstate" where
"getMediumSRSubState (MediumSRState state_s automaton_c) = state_s"

fun getC :: "MediumSRState \<Rightarrow> nat" where
"getC (MediumSRState _ automaton_c) = automaton_c"
    


fun mediumSRTransitionH :: "(MediumSRState \<times> (abpMessage tsyn)) \<Rightarrow> ((MediumSRState \<times> abpMessage tsyn SB) set rev)" where
    "mediumSRTransitionH (MediumSRState Single automaton_c, ((*ds\<mapsto>*)Msg (ABPPair_nat_bool a))) = 
       (if(automaton_c>0) then Rev {(MediumSRState Single (automaton_c-1),(tsynbNull (\<C> ''dr'')))}
       else if(automaton_c=0) then Rev {(MediumSRState Single (c),(createDrBundle (a)))| (c). True}
       else Rev {(MediumSRState Single automaton_c, ((tsynbNull (\<C> ''dr''))))})"  |

    "mediumSRTransitionH (MediumSRState Single automaton_c, ((*ds\<mapsto>*)null)) = 
       (Rev {(MediumSRState Single automaton_c,(tsynbNull (\<C> ''dr'')))})"  

fun mediumSRTransition :: "(MediumSRState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> ((MediumSRState \<times> abpMessage tsyn SB) set rev)" where
"mediumSRTransition (s,f) = (if dom(f) = {\<C> ''ds''} then mediumSRTransitionH (s,(f\<rightharpoonup>\<C> ''ds'')) else undefined)"

lift_definition MediumSRAutomaton :: "(MediumSRState, abpMessage tsyn) ndAutomaton" is "(mediumSRTransition, Rev {(MediumSRState Single c, (tsynbNull (\<C> ''dr'')))| c. True}, Discr {\<C> ''ds''}, Discr {\<C> ''dr''})"
  by simp

definition MediumSRSPF :: "abpMessage tsyn SPS" where
"MediumSRSPF = nda_H MediumSRAutomaton"

end