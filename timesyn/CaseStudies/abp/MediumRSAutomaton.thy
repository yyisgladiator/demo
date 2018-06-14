

theory MediumRSAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype MediumRSSubstate = Single

(* SWS: ins kommentar davor wie die Variable heißt *)
(* And these have also the variables *)
datatype MediumRSState = State MediumRSSubstate (* SWS: c=*)"nat"

fun getSubState :: "MediumRSState \<Rightarrow> MediumRSSubstate" where
    "getSubState (State state_s automaton_c) = state_s"

fun getC :: "MediumRSState \<Rightarrow> nat" where
"getC (State _ automaton_c) = automaton_c"
    

(* SWS: siehe receiver *)
abbreviation input_ar_c4 :: "channel" ("\<guillemotright>ar") where
"\<guillemotright>ar \<equiv> c4"

abbreviation output_as_c1 :: "channel" ("as\<guillemotright>") where
"as\<guillemotright> \<equiv> c1"

(* SWS: siehe receiver *)
lift_definition createAsOutput :: "bool \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ as\<guillemotright> \<mapsto> \<up>(Msg (bool b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

(* SWS: Das Medium ist nichtdeterministisch, siehe das Beispiel in "untimed/CaseStudy/Medium.thy" *)
fun mediumRSTransitionH :: "(MediumRSState \<times> (Message tsyn)) \<Rightarrow> (MediumRSState \<times> Message tsyn SB)" where
    "mediumRSTransitionH (State Single automaton_c, (Msg (bool a))) = 
       (if(automaton_c=0) then ((State Single (50),(tsynbNull as\<guillemotright>)))
       else if(automaton_c>0) then ((State Single (automaton_c-1),(tsynbNull as\<guillemotright>)))
       else if(True) then ((State Single automaton_c,(tsynbNull as\<guillemotright>)))
       else  (State Single automaton_c, ((tsynbNull as\<guillemotright>))))"  |

    "mediumRSTransitionH (State Single automaton_c, (null)) = 
       (State Single automaton_c,(tsynbNull as\<guillemotright>))"  

fun mediumRSTransition :: "(MediumRSState \<times> (channel \<rightharpoonup> Message tsyn)) \<Rightarrow> (MediumRSState \<times> Message tsyn SB)" where
"mediumRSTransition (s,f) = (if dom(f) = {\<guillemotright>ar} then mediumRSTransitionH (s,(f\<rightharpoonup>\<guillemotright>ar)) else undefined)"

lift_definition MediumRSAutomaton :: "(MediumRSState, Message tsyn) automaton" is "(mediumRSTransition, State Single 50, (tsynbNull as\<guillemotright>), {c4}, {c1})"
sorry

definition MediumRSSPF :: "Message tsyn SPF" where
"MediumRSSPF = H MediumRSAutomaton"

end