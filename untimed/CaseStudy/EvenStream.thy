theory EvenStream

imports "../../untimed/Streams"

begin

(********************************)
    section \<open>Datentypen\<close>
(********************************)

(* This are the actual states from MAA *)
datatype EvenAutomatonSubstate = Odd | Even

(* And these have also the variables *)
datatype EvenAutomatonState = State EvenAutomatonSubstate nat

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





end