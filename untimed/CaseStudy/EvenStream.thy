theory EvenStream

imports "../../untimed/Streams" "../../inc/Event" "Sum"

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

fun evenTransition :: "EvenAutomatonState \<Rightarrow> EvenAutomaton event \<Rightarrow> (EvenAutomaton event \<times> EvenAutomatonState)" where
"evenTransition s Tick = (Tick, s)" |

"evenTransition (State _ summe) (Msg (A input)) = (Msg (B (even (summe + input))), State (evenMakeSubstate (even (summe + input))) (summe+input)) " 



definition evenInitialState where
"evenInitialState = State Even 0"

abbreviation evenStream:: "EvenAutomaton event stream \<rightarrow> EvenAutomaton event stream" where
"evenStream \<equiv> sscanlA evenTransition evenInitialState"



(********************************)
    section \<open>Lemma\<close>
(********************************)
lemma "#(evenStream\<cdot>s) = #s"
  by simp

(* TODO generalize the smap (\<lambda> m. case m of (Msg n) \<Rightarrow> Msg (B (even n)) | Tick \<Rightarrow> Tick) *)

lemma "evenStream\<cdot>(smap (\<lambda> m. case m of (Msg n) \<Rightarrow> Msg (A n) | Tick \<Rightarrow> Tick)\<cdot>s) 
      = smap (\<lambda> m. case m of (Msg n) \<Rightarrow> Msg (B (even n)) | Tick \<Rightarrow> Tick)\<cdot>(sum\<cdot>s)"
  oops

end