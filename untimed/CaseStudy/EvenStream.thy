(*  Title:  EvenStream
    Author: Sebastian Stüber
    e-mail: sebastian.stueber@rwth-aachen.de

    Description: Part of a case Study for a generated Automaton. 
      This part only deals with (event) streams, bundles are somewhere else
*)


theory EvenStream

imports tsynStream

begin

(********************************)
    section \<open>Datentypen\<close>
(********************************)

(* This are the actual states from MAA *)
datatype EvenAutomatonSubstate = Odd | Even

instance EvenAutomatonSubstate :: countable
  apply(intro_classes)
  by(countable_datatype)

(* And these have also the variables *)
datatype EvenAutomatonState = State EvenAutomatonSubstate nat

instance EvenAutomatonState :: countable
  apply(intro_classes)
  by(countable_datatype)

fun getSubState :: "EvenAutomatonState \<Rightarrow> EvenAutomatonSubstate" where
"getSubState (State automaton_s automaton_sum) = automaton_s"

fun getSum :: "EvenAutomatonState \<Rightarrow> nat" where
"getSum (State automaton_s automaton_sum) = automaton_sum"


datatype EvenAutomaton = A  nat | B  bool

instance EvenAutomaton :: countable
  apply(intro_classes)
  by(countable_datatype)





(********************************)
    section \<open>Even Function\<close>
(********************************)

(* Helper function to make the transition a one-liner *)
fun evenMakeSubstate :: "bool \<Rightarrow> EvenAutomatonSubstate" where
"evenMakeSubstate True = Even" | 
"evenMakeSubstate False = Odd"

(* transition function for evenAutomaton on event streams *)
fun evenTransition :: "EvenAutomatonState \<Rightarrow> EvenAutomaton event \<Rightarrow> (EvenAutomaton event \<times> EvenAutomatonState)" where
"evenTransition s Tick = (Tick, s)" |

"evenTransition (State _ summe) (Msg (A input)) = (Msg (B (even (summe + input))), State (evenMakeSubstate (even (summe + input))) (summe+input)) " 



definition evenInitialState where
"evenInitialState = State Even 0"

abbreviation evenStream:: "EvenAutomaton event stream \<rightarrow> EvenAutomaton event stream" where
"evenStream \<equiv> sscanlA evenTransition evenInitialState"


lemma evenstream_bot: "sscanlA evenTransition state\<cdot>\<bottom> = \<bottom>"
  by simp

lemma evenstream_tick: "sscanlA evenTransition state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (sscanlA evenTransition state\<cdot>xs)"
  by simp

lemma evenstream_msg:  "sscanlA evenTransition (State ooo summe) \<cdot>(\<up>(Msg (A m)) \<bullet> xs) 
    = \<up>(Msg (B (even (summe + m)))) \<bullet> (sscanlA evenTransition (State (evenMakeSubstate (even (summe + m)))  (summe + m))\<cdot>xs)"
  by simp


(* convert the datatypes *)
abbreviation nat2even:: "nat event stream \<rightarrow> EvenAutomaton event stream" where
"nat2even \<equiv> tsynMap A"

(* convert the datatypes *)
abbreviation bool2even:: "bool event stream \<rightarrow> EvenAutomaton event stream" where
"bool2even \<equiv> tsynMap B"



(********************************)
    section \<open>Lemma\<close>
(********************************)
lemma "#(evenStream\<cdot>s) = #s"
  by simp

lemma evenstream_final_h: "sscanlA evenTransition (State ooo n)\<cdot>(nat2even\<cdot>s) = bool2even\<cdot>(tsynMap even\<cdot>(tsynScanl plus n\<cdot>s))"
  apply(induction arbitrary: n ooo rule: ind [of _ s])
    apply auto
  apply(rename_tac a s n ooo)
  apply(case_tac a)
  by auto

lemma evenstream_final: "evenStream\<cdot>(nat2even\<cdot>s) = bool2even\<cdot>(tsynMap even\<cdot>(tsynSum\<cdot>s))"
  by (simp add: evenInitialState_def tsynSum_def evenstream_final_h)

end