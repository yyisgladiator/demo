theory ReceiverAutomaton

imports "../../../untimed/CaseStudy/Automaton" "../../tsynStream" "../../tsynBundle" 

begin

(* This are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = State ReceiverSubstate 

fun getSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
    "getSubState (State state_s ) = state_s"


datatype Receiver = C "nat" | B "bool" | A "(nat\<times>bool)"
instance Receiver :: countable
apply(intro_classes)
by(countable_datatype)

abbreviation input_dr_c1 :: "channel" ("\<guillemotright>dr") where
"\<guillemotright>dr \<equiv> c1"

abbreviation output_ar_c2 :: "channel" ("ar\<guillemotright>") where
"ar\<guillemotright> \<equiv> c2"

abbreviation output_o_c3 :: "channel" ("o\<guillemotright>") where
"o\<guillemotright> \<equiv> c3"

instantiation Receiver :: message
begin
fun ctype_Receiver :: "channel  \<Rightarrow> Receiver set" where
    "ctype_Receiver \<guillemotright>dr = range A" | 
    "ctype_Receiver ar\<guillemotright> = range B" | 
    "ctype_Receiver o\<guillemotright> = range C" 
instance
by(intro_classes)
end

lift_definition createArOutput :: "bool \<Rightarrow> Receiver tsyn SB" is
    "\<lambda>b. [ ar\<guillemotright> \<mapsto> \<up>(Msg (B b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

lift_definition createOOutput :: "nat \<Rightarrow> Receiver tsyn SB" is
    "\<lambda>b. [ o\<guillemotright> \<mapsto> \<up>(Msg (C b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp


fun receiverTransitionH :: "(ReceiverState \<times> (Receiver tsyn)) \<Rightarrow> (ReceiverState \<times> Receiver tsyn SB)" where
    "receiverTransitionH (State Rf , (Msg (A a))) = 
       (if((snd a)=False) then ((State Rt ,(createArOutput ((snd a))) \<uplus> (createOOutput ((fst a)))))
       else if((snd a)=True) then ((State Rf ,(createArOutput ((snd a))) \<uplus> (tsynbNull o\<guillemotright>)))
       else  (State Rf , ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))))"  |

    "receiverTransitionH (State Rf , (null)) = 
       (State Rf ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"  |

    "receiverTransitionH (State Rt , (Msg (A a))) = 
       (if((snd a)=False) then ((State Rt ,(createArOutput ((snd a))) \<uplus> (tsynbNull o\<guillemotright>)))
       else if((snd a)=True) then ((State Rf ,(createArOutput ((snd a))) \<uplus> (createOOutput ((fst a)))))
       else  (State Rt , ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))))"  |

    "receiverTransitionH (State Rt , (null)) = 
       (State Rt ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"  

fun receiverTransition :: "(ReceiverState \<times> (channel \<rightharpoonup> Receiver tsyn)) \<Rightarrow> (ReceiverState \<times> Receiver tsyn SB)" where
"receiverTransition (s,f) = (if dom(f) = {\<guillemotright>dr} then receiverTransitionH (s,(f\<rightharpoonup>\<guillemotright>dr)) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, Receiver tsyn) automaton" is "(receiverTransition, State Rt , (tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>), {c1}, {c2,c3})"
sorry

definition ReceiverSPF :: "Receiver tsyn SPF" where
"ReceiverSPF = H ReceiverAutomaton"

end