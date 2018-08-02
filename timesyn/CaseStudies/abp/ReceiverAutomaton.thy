(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Jul 9, 2018 2:06:12 PM by transformer 1.0.0
 *)
theory ReceiverAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = ReceiverState ReceiverSubstate 

fun getReceiverSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
"getReceiverSubState (ReceiverState state_s ) = state_s"



fun receiverTransitionH :: "(ReceiverState \<times> (abpMessage tsyn)) \<Rightarrow> (ReceiverState \<times> abpMessage tsyn SB)" where
    "receiverTransitionH (ReceiverState Rf , ((*dr\<mapsto>*)Msg (Pair_nat_bool a))) = 
       (if((snd a)=True) then ((ReceiverState Rf ,(createArBundle ((snd a))) \<uplus> (tsynbNull (\<C> ''o''))))
       else if((snd a)=False) then ((ReceiverState Rt ,(createArBundle ((snd a))) \<uplus> (createOBundle ((fst a)))))
       else  (ReceiverState Rf , ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))))"  |

    "receiverTransitionH (ReceiverState Rf , ((*dr\<mapsto>*)null)) = 
       (ReceiverState Rf ,(tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))"  |

    "receiverTransitionH (ReceiverState Rt , ((*dr\<mapsto>*)Msg (Pair_nat_bool a))) = 
       (if((snd a)=False) then ((ReceiverState Rt ,(createArBundle ((snd a))) \<uplus> (tsynbNull (\<C> ''o''))))
       else if((snd a)=True) then ((ReceiverState Rf ,(createArBundle ((snd a))) \<uplus> (createOBundle ((fst a)))))
       else  (ReceiverState Rt , ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))))"  |

    "receiverTransitionH (ReceiverState Rt , ((*dr\<mapsto>*)null)) = 
       (ReceiverState Rt ,(tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))"  

fun receiverTransition :: "(ReceiverState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (ReceiverState \<times> abpMessage tsyn SB)" where
"receiverTransition (s,f) = (if dom(f) = {\<C> ''dr''} then receiverTransitionH (s,(f\<rightharpoonup>\<C> ''dr'')) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, abpMessage tsyn) dAutomaton" is "(receiverTransition, ReceiverState Rt , (tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  by simp

definition ReceiverSPF :: "abpMessage tsyn SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"

end