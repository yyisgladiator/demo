

theory ReceiverAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = State ReceiverSubstate 

fun getSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
    "getSubState (State state_s ) = state_s"



abbreviation input_dr_c2 :: "channel" ("\<guillemotright>dr") where
"\<guillemotright>dr \<equiv> c2"

abbreviation output_ar_c4 :: "channel" ("ar\<guillemotright>") where
"ar\<guillemotright> \<equiv> c4"

abbreviation output_o_c5 :: "channel" ("o\<guillemotright>") where
"o\<guillemotright> \<equiv> c5"


lift_definition createArOutput :: "bool \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ ar\<guillemotright> \<mapsto> \<up>(Msg (bool b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

lift_definition createOOutput :: "nat \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ o\<guillemotright> \<mapsto> \<up>(Msg (nat b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp


fun receiverTransitionH :: "(ReceiverState \<times> (Message tsyn)) \<Rightarrow> (ReceiverState \<times> Message tsyn SB)" where
    "receiverTransitionH (State Rf , (Msg (Pair_nat_bool a))) = 
       (if((snd a)=False) then ((State Rt ,(createArOutput ((snd a))) \<uplus> (createOOutput ((fst a)))))
       else if((snd a)=True) then ((State Rf ,(createArOutput ((snd a))) \<uplus> (tsynbNull o\<guillemotright>)))
       else  (State Rf , ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))))"  |

    "receiverTransitionH (State Rf , (null)) = 
       (State Rf ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"  |

    "receiverTransitionH (State Rt , (Msg (Pair_nat_bool a))) = 
       (if((snd a)=False) then ((State Rt ,(createArOutput ((snd a))) \<uplus> (tsynbNull o\<guillemotright>)))
       else if((snd a)=True) then ((State Rf ,(createArOutput ((snd a))) \<uplus> (createOOutput ((fst a)))))
       else  (State Rt , ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))))"  |

    "receiverTransitionH (State Rt , (null)) = 
       (State Rt ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"  

fun receiverTransition :: "(ReceiverState \<times> (channel \<rightharpoonup> Message tsyn)) \<Rightarrow> (ReceiverState \<times> Message tsyn SB)" where
"receiverTransition (s,f) = (if dom(f) = {\<guillemotright>dr} then receiverTransitionH (s,(f\<rightharpoonup>\<guillemotright>dr)) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, Message tsyn) automaton" is "(receiverTransition, State Rt , (tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>), {c2}, {c4,c5})"
sorry

definition ReceiverSPF :: "Message tsyn SPF" where
"ReceiverSPF = H ReceiverAutomaton"

end