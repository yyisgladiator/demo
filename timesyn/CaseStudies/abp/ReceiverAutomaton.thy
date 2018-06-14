

theory ReceiverAutomaton

imports "../AutomatonPrelude"

  (* SWS: Hier hätte ich gerne mehr infos (auf english): 
     * Das es autogeneriert wurde (und vlt aus welchem Modell)
     * NICHT ANFASSEN ! ! ! ! Wenn was anders soll dann Modell ändern
     * Datum der Generierung
     * Versionierung des Generators
  *)
begin

(* This are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* SWS: in diesem fall haben wir keine Variablen *)
(* And these have also the variables *)
datatype ReceiverState = State ReceiverSubstate 

fun getSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
    "getSubState (State state_s ) = state_s"


(* SWS: keine abbreviations mehr, stattdessen direkt die Namen mit "\<C> ''Name''". 
  Das Problem an abbreviations kommt wenn man mehr als eine hat. Also Sender macht abbreviation "as\<guillemotright>" für channel c2 
  und Receiver nennt das gleiche "\<guillemotright>as". In theorien die sowohl Sender alsauch Receiver importieren kommt es zu Verwirrungen *)
abbreviation input_dr_c2 :: "channel" ("\<guillemotright>dr") where
"\<guillemotright>dr \<equiv> c2"

abbreviation output_ar_c4 :: "channel" ("ar\<guillemotright>") where
"ar\<guillemotright> \<equiv> c4"

abbreviation output_o_c5 :: "channel" ("o\<guillemotright>") where
"o\<guillemotright> \<equiv> c5"

(* SWS: das in den allgemeinen teil (AutomatonPrelude), das ist unabhängig von den Automaten. Dann halt nicht "_Output" nennen sondern nur
  tsynbCreate_ar (Oder irgendwie so) *)
lift_definition createArOutput :: "bool \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ ar\<guillemotright> \<mapsto> \<up>(Msg (bool b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

(* SWS: analog *)
lift_definition createOOutput :: "nat \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ o\<guillemotright> \<mapsto> \<up>(Msg (nat b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

(* SWS: Ich vermisse die informationen aus welchem channel die input-message kommt. Das level haben wir absichtlich
  entfernt damit "fun" klappt, aber der Nutzer soll es trotzdem schnell sehen. 
  Wir können das als Kommentar annotieren zB:  *)
fun receiverTransitionH :: "(ReceiverState \<times> ((* SWS: c2\<mapsto>*)Message tsyn)) \<Rightarrow> (ReceiverState \<times> Message tsyn SB)" where
    "receiverTransitionH (State Rf , ((* SWS: c2\<mapsto>*)Msg (Pair_nat_bool a))) = 
  (* SWS: du kannst das if-then-else in das patternmatching packen. 
    (Pair_nat_bool (m, True) zum Beispiel *)
       (if((snd a)=False) then ((State Rt ,(createArOutput ((snd a))) \<uplus> (createOOutput ((fst a)))))
       else if((snd a)=True) then ((State Rf ,(createArOutput ((snd a))) \<uplus> (tsynbNull o\<guillemotright>)))
       else  (State Rf , ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))))"  |

    "receiverTransitionH (State Rf , ((* SWS: c2\<mapsto>*)null)) = 
       (State Rf ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"  |

    "receiverTransitionH (State Rt , ((* SWS: c2\<mapsto>*)Msg (Pair_nat_bool a))) = 
       (if((snd a)=False) then ((State Rt ,(createArOutput ((snd a))) \<uplus> (tsynbNull o\<guillemotright>)))
       else if((snd a)=True) then ((State Rf ,(createArOutput ((snd a))) \<uplus> (createOOutput ((fst a)))))
       else  (State Rt , ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))))"  |

    "receiverTransitionH (State Rt , ((* SWS: c2\<mapsto>*)null)) = 
       (State Rt ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"  

fun receiverTransition :: "(ReceiverState \<times> (channel \<rightharpoonup> Message tsyn)) \<Rightarrow> (ReceiverState \<times> Message tsyn SB)" where
"receiverTransition (s,f) = (if dom(f) = {\<guillemotright>dr} then receiverTransitionH (s,(f\<rightharpoonup>\<guillemotright>dr)) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, Message tsyn) automaton" is (* SWS: Zeilenumbruch bitte *) "(receiverTransition, State Rt , (tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>), {c2}, {c4,c5})"
sorry

definition ReceiverSPF :: "Message tsyn SPF" where
"ReceiverSPF = H ReceiverAutomaton"

end