(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
*)

theory Automaton
imports SPF
begin
default_sort type
declare [[show_types]]
declare [[show_consts]]


section \<open>Backend Signatures\<close>
(* This stuff is only here until the functions are defined in the backend, they will be in SPF.thy *)


(* VERY Basic automaton type *)
(* ToDo: initial step, wellformed condition *)

(* FYI: in the non-deterministic case the automaton will be a cpo *)
typedef ('state::type, 'm::message) automaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB. True}"
  sorry

definition getInitialState :: "('s, 'm::message) automaton \<Rightarrow> 's" where
"getInitialState automat = fst (snd (Rep_automaton automat))"


setup_lifting type_definition_automaton

(* HK is defining this. returns the fixpoint *)
definition myFixer :: "(('s \<Rightarrow> 'm SPF)\<rightarrow>('s \<Rightarrow> 'm SPF)) \<rightarrow> ('s \<Rightarrow> 'm SPF)" where
"myFixer = undefined"

(* a modified version of spfStep. The real signature will be different ! ! *)
definition spfStep :: "('s \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep = undefined"

definition h :: "('s::type, 'm::message) automaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"h automat = myFixer\<cdot>(\<Lambda> h. (\<lambda>s. spfStep\<cdot>h))"

(* This function also prerepends the first SB ... *)
(* But basically she just calls h *)
definition H :: "('s, 'm::message) automaton \<Rightarrow> 'm SPF" where
"H automat = h automat (getInitialState automat)"




(* From here everything should be automatically transformed from MontiArc-Automaton *)
section \<open>Automaton Datatypes\<close>

(* Only on idea how the states could be implemented *)
datatype substate = even | odd  (* This are the actual states from MAA *)
datatype myState = State substate nat bool (* And these have also the variables *)

fun getVarI :: "myState \<Rightarrow> nat" where
"getVarI (State s n b) = n"

fun getSubState :: "myState \<Rightarrow> substate" where
"getSubState (State s n b) = s"


datatype myM = N nat | B bool

instance myM :: countable
apply(intro_classes)
by(countable_datatype)


instantiation myM :: message
begin
  fun ctype_myM :: "channel \<Rightarrow> myM set" where
  "ctype_myM c1 = range N"  |
  "ctype_myM c2 = range B"

instance
by(intro_classes)
end



section \<open>Automaton Functions\<close>

(* Somehow define the transition function *)
definition myTransition :: "(myState \<times>(channel \<rightharpoonup> myM)) \<Rightarrow> (myState \<times> myM SB)" where
"myTransition = undefined"

lift_definition myAutomaton :: "(myState, myM) automaton" is "(myTransition, State even 0 True, sbLeast {})"
  sorry (* In the final form of the automaton datatype we will have to proof stuff *)

definition mySPF :: "myM SPF" where
"mySPF = H myAutomaton"




section \<open>Automaton Lemma\<close>


end
