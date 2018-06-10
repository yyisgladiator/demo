theory Medium_SPS

imports "../SPS" "../../timesyn/tsynBundle"


(* Description: Rekursive Medium definition for Dennis group. Since the Medium does not yet exist
    as uspec the lemma will be "sorry" and proven later *)
begin 


(* This are the actual states from MAA *)
datatype MediumSubstate = TheOne (* Das MAA-Modell hat nur diesen einen State *)

(* And these have also the variables *)
datatype MediumState = State MediumSubstate nat

fun getSubState :: "MediumState \<Rightarrow> MediumSubstate" where
"getSubState (State automaton_s automaton_sum) = automaton_s"

fun getCounter :: "MediumState \<Rightarrow> nat" where
"getCounter (State automaton_s automaton_counter) = automaton_counter"


(* Zum Testen... die funktion setzt den Channel *)
definition makeOutput :: "'m::message \<Rightarrow> 'm tsyn SB" where
"makeOutput = undefined"






(* Platzhalter für das finale Medium h lemma *)
(* NEVER use h_MED_def instead use the following lemma *)
definition h_MED :: "MediumState \<Rightarrow> 'm SPS" where
"h_MED = undefined"


(* "abpMediumTransition (state, null)= Rev {(state, tsynbNull c2)}"  *)
(*lemma "h_MED state (tsynbNull c1) = tsynbNull c2"
  oops *)

end