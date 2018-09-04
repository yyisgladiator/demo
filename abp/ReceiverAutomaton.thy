(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Aug 15, 2018 3:13:07 PM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton

imports AutomatonPrelude

begin

(* These are the actual states from MAA *)
datatype ReceiverSubstate = Rt | Rf

(* And these have also the variables *)
datatype ReceiverState = ReceiverState ReceiverSubstate 

fun getReceiverSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
"getReceiverSubState (ReceiverState state_s ) = state_s"


fun receiverTransitionH :: "(ReceiverState \<times> (abpMessage tsyn)) \<Rightarrow> (ReceiverState \<times> abpMessage tsyn SB)" where
"receiverTransitionH (ReceiverState Rf, ((*dr\<mapsto>*)Msg (ABPPair_nat_bool a))) =
  (if((snd a)=True) then ((ReceiverState Rf, (createArBundle ((snd a)) \<uplus> tsynbNull (\<C> ''o''))))
   else if((snd a)=False) then ((ReceiverState Rt, (createArBundle ((snd a)) \<uplus> createOBundle ((fst a)))))
   else (ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))))" |

"receiverTransitionH (ReceiverState Rf, ((*dr\<mapsto>*)null)) =
  (
        ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))
)" |

"receiverTransitionH (ReceiverState Rt, ((*dr\<mapsto>*)Msg (ABPPair_nat_bool a))) =
  (if((snd a)=True) then ((ReceiverState Rf, (createArBundle ((snd a)) \<uplus> createOBundle ((fst a)))))
   else if((snd a)=False) then ((ReceiverState Rt, (createArBundle ((snd a)) \<uplus> tsynbNull (\<C> ''o''))))
   else (ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))))" |

"receiverTransitionH (ReceiverState Rt, ((*dr\<mapsto>*)null)) =
  (
        ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))
)"
        
fun receiverTransition :: "(ReceiverState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (ReceiverState \<times> abpMessage tsyn SB)" where
"receiverTransition (s,f) = (if dom(f) = {\<C> ''dr''} then receiverTransitionH (s,(f\<rightharpoonup>\<C> ''dr'')) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, abpMessage tsyn) dAutomaton" is "(receiverTransition, ReceiverState Rt , (tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  by simp

definition ReceiverSPF :: "abpMessage tsyn SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"

(* Line 18 in the MAA model *)
lemma tbd_0_0:
  assumes "(snd a)=True"
    shows "spfConcIn  (createDrBundle a)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (createArBundle ((snd a)) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 19 in the MAA model *)
lemma tbd_0_1:
  assumes "(snd a)=False"
    shows "spfConcIn  (createDrBundle a)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (createArBundle ((snd a)) \<uplus> createOBundle ((fst a)))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 17 in the MAA model *)
lemma tbd_1_0:
  assumes "True"
    shows "spfConcIn  (tsynbNull (\<C> ''dr''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 14 in the MAA model *)
lemma tbd_2_0:
  assumes "(snd a)=True"
    shows "spfConcIn  (createDrBundle a)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (createArBundle ((snd a)) \<uplus> createOBundle ((fst a)))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 15 in the MAA model *)
lemma tbd_2_1:
  assumes "(snd a)=False"
    shows "spfConcIn  (createDrBundle a)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (createArBundle ((snd a)) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 16 in the MAA model *)
lemma tbd_3_0:
  assumes "True"
    shows "spfConcIn  (tsynbNull (\<C> ''dr''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops


end