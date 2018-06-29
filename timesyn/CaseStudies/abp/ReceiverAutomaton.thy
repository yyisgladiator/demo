(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Jun 29, 2018 5:23:56 PM by transformer 1.0.0
 *)
theory ReceiverAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = State ReceiverSubstate 

fun getSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
"getSubState (State state_s ) = state_s"



fun receiverTransitionH :: "(ReceiverState \<times> (abpMessage tsyn)) \<Rightarrow> (ReceiverState \<times> abpMessage tsyn SB)" where
    "receiverTransitionH (State Rf , ((*dr\<mapsto>*)Msg (Pair_nat_bool a))) = 
       (if((snd a)=False) then ((State Rt ,(createArBundle ((snd a))) \<uplus> (createOBundle ((fst a)))))
       else if((snd a)=True) then ((State Rf ,(createArBundle ((snd a))) \<uplus> (tsynbNull (\<C> ''o''))))
       else  (State Rf , ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))))"  |

    "receiverTransitionH (State Rf , ((*dr\<mapsto>*)null)) = 
       (State Rf ,(tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))"  |

    "receiverTransitionH (State Rt , ((*dr\<mapsto>*)Msg (Pair_nat_bool a))) = 
       (if((snd a)=True) then ((State Rf ,(createArBundle ((snd a))) \<uplus> (createOBundle ((fst a)))))
       else if((snd a)=False) then ((State Rt ,(createArBundle ((snd a))) \<uplus> (tsynbNull (\<C> ''o''))))
       else  (State Rt , ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))))"  |

    "receiverTransitionH (State Rt , ((*dr\<mapsto>*)null)) = 
       (State Rt ,(tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))"  

fun receiverTransition :: "(ReceiverState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (ReceiverState \<times> abpMessage tsyn SB)" where
"receiverTransition (s,f) = (if dom(f) = {\<C> ''dr''} then receiverTransitionH (s,(f\<rightharpoonup>\<C> ''dr'')) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, abpMessage tsyn) automaton" is "(receiverTransition, State Rt , (tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
sorry

definition ReceiverSPF :: "abpMessage tsyn SPF" where
"ReceiverSPF = H ReceiverAutomaton"

end