

theory MediumSRAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype MediumSRSubstate = Single

(* And these have also the variables *)
datatype MediumSRState = State MediumSRSubstate "nat"

fun getSubState :: "MediumSRState \<Rightarrow> MediumSRSubstate" where
    "getSubState (State state_s automaton_c) = state_s"

fun getC :: "MediumSRState \<Rightarrow> nat" where
"getC (State _ automaton_c) = automaton_c"
    


abbreviation input_ds_c3 :: "channel" ("\<guillemotright>ds") where
"\<guillemotright>ds \<equiv> c3"

abbreviation output_dr_c2 :: "channel" ("dr\<guillemotright>") where
"dr\<guillemotright> \<equiv> c2"


lift_definition createDrOutput :: "(nat\<times>bool) \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ dr\<guillemotright> \<mapsto> \<up>(Msg (Pair_nat_bool b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp


fun mediumSRTransitionH :: "(MediumSRState \<times> (Message tsyn)) \<Rightarrow> (MediumSRState \<times> Message tsyn SB)" where
    "mediumSRTransitionH (State Single automaton_c, (Msg (Pair_nat_bool a))) = 
       (if(automaton_c>0) then ((State Single (automaton_c-1),(tsynbNull dr\<guillemotright>)))
       else if(True) then ((State Single automaton_c,(tsynbNull dr\<guillemotright>)))
       else if(automaton_c=0) then ((State Single (50),(tsynbNull dr\<guillemotright>)))
       else  (State Single automaton_c, ((tsynbNull dr\<guillemotright>))))"  |

    "mediumSRTransitionH (State Single automaton_c, (null)) = 
       (State Single automaton_c,(tsynbNull dr\<guillemotright>))"  

fun mediumSRTransition :: "(MediumSRState \<times> (channel \<rightharpoonup> Message tsyn)) \<Rightarrow> (MediumSRState \<times> Message tsyn SB)" where
"mediumSRTransition (s,f) = (if dom(f) = {\<guillemotright>ds} then mediumSRTransitionH (s,(f\<rightharpoonup>\<guillemotright>ds)) else undefined)"

lift_definition MediumSRAutomaton :: "(MediumSRState, Message tsyn) automaton" is "(mediumSRTransition, State Single 50, (tsynbNull dr\<guillemotright>), {c3}, {c2})"
sorry

definition MediumSRSPF :: "Message tsyn SPF" where
"MediumSRSPF = H MediumSRAutomaton"

end