(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
*)

theory Automaton
imports SPF SpfStep SPF_JB
begin
default_sort type


section \<open>Backend Signatures\<close>
(* This stuff is only here until the functions are defined in the backend, they will be in SPF.thy *)


(* VERY Basic automaton type *)
(* ToDo: wellformed condition *)

(* FYI: in the non-deterministic case the automaton will be a cpo *)

(* The content is:
  transition function \<times> initial state \<times> initial Output \<times> input domain \<times> output domain *)
typedef ('state::type, 'm::message) automaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set. True}"
  sorry

definition getTransition :: "('s, 'm::message) automaton \<Rightarrow>(('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('s \<times> 'm SB))" where
"getTransition automat = fst (Rep_automaton automat)"

definition getInitialState :: "('s, 'm::message) automaton \<Rightarrow> 's" where
"getInitialState automat = fst (snd (Rep_automaton automat))"

definition getInitialOutput :: "('s, 'm::message) automaton \<Rightarrow> 'm SB" where
"getInitialOutput automat = fst (snd (snd (Rep_automaton automat)))"

definition getDom :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getDom automat = fst (snd (snd (snd (Rep_automaton automat))))"

definition getRan :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getRan automat = (snd (snd (snd (snd (Rep_automaton automat)))))"

setup_lifting type_definition_automaton

(* HK is defining this. returns the fixpoint *)
thm spfStateFix_def
(* definition myFixer :: "channel set \<Rightarrow> channel set \<Rightarrow> (('s \<Rightarrow> 'm::message SPF)\<rightarrow>('s \<Rightarrow> 'm SPF)) \<rightarrow> ('s \<Rightarrow> 'm SPF)" where
"myFixer = spfStateFix" *)


(* Defined by SWS *)
thm spfApplyIn_def
thm spfRt_def
(* 
definition spfRt :: "'m SPF \<rightarrow> 'm SPF" where
"spfRt = undefined"
*)


thm spfConc_def
(*
(* Defined by JCB *)
definition spfCons :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfCons = undefined"
*)

(* Converter function. *)
  (* definition should be right, but needs to be nicer *)
definition helper:: "(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 'm SPF) \<rightarrow> ('e \<Rightarrow> 'm SPF)" where
"helper f s \<equiv> \<Lambda> h. (\<lambda> e. spfRt\<cdot>(spfConc (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))" 

lemma helper_cont: "cont (\<lambda>h. (\<lambda> e. spfConc (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))"
  by simp

(* As defined in Rum96 *)
definition h :: "('s::type, 'm::message) automaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"h automat = spfStateFix (getDom automat)(getRan automat)\<cdot>
     (\<Lambda> h. (\<lambda>s. spfStep  (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>h)))"

lemma h_cont: "cont (\<lambda> h. (\<lambda>s. spfStep  (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>h)))"
  by simp

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition H :: "('s, 'm::message) automaton \<Rightarrow> 'm SPF" where
"H automat = spfConc (getInitialOutput automat)\<cdot>(h automat (getInitialState automat))"




section \<open>stuff i need in spfStep\<close>
lemma spfstep_dom [simp]: "spfDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  sorry

lemma spfstep_ran [simp]: "spfRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  sorry

lemma stepstep_step: "spfStep In Out\<cdot>f\<rightleftharpoons>sb = (f ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<rightleftharpoons>sb"
  sorry




section \<open>Lemma about h\<close>

lemma h_unfolding: "(h automat s) = spfStep (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>(h automat))"
  by (metis (no_types, lifting) Abs_cfun_inverse2 h_cont h_def spfStateFix_fix spfstep_dom spfstep_ran)

lemma h_step: "(h automat s)\<rightleftharpoons>sb = ((helper (getTransition automat) s\<cdot>(h automat)) ((inv convDiscrUp)(sbHdElem\<cdot>sb))) \<rightleftharpoons>sb"
  by (simp add: h_unfolding stepstep_step)

definition autGetNextState:: "('s::type, 'm::message) automaton \<Rightarrow> 's \<Rightarrow>  ((channel \<rightharpoonup> 'm)) \<Rightarrow> 's" where
"autGetNextState aut s m = fst ((getTransition aut) (s,m))"

definition autGetNextOutput:: "('s::type, 'm::message) automaton \<Rightarrow> 's \<Rightarrow>  ((channel \<rightharpoonup> 'm)) \<Rightarrow>  'm SB" where
"autGetNextOutput aut s m = snd ((getTransition aut) (s,m))"

(* ToDo: make a bit more readable *)
lemma h_final: "(h automat s)\<rightleftharpoons>sb = 
  spfConc (autGetNextOutput automat s ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<cdot>(spfRt\<cdot>(h automat (autGetNextState automat s ((inv convDiscrUp)(sbHdElem\<cdot>sb))))) \<rightleftharpoons>sb"
  unfolding h_step
  by(simp add: helper_def autGetNextOutput_def autGetNextState_def)
  

section \<open>Lemma about H\<close>








(* From here everything should be automatically transformed from MontiArc-Automaton *)
section \<open>Automaton Datatypes\<close>

(* Only on idea how the states could be implemented *)
datatype substate = singleState | \<NN>  (* This are the actual states from MAA *)
datatype myState = State substate nat (* And these have also the variables *)

fun getVarI :: "myState \<Rightarrow> nat" where
"getVarI (State s n ) = n"

fun getSubState :: "myState \<Rightarrow> substate" where
"getSubState (State s n ) = s"


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

(* Creates a fitting SB given the right output values *)
(* Parameter: 
  channel set \<Rightarrow> domain of the output
  nat         \<Rightarrow> maps to channel c1, in MAA called "XXXX"
  bool        \<Rightarrow> maps to channel c2, in MAA calles "YYYY" *)
fun createOutput :: "channel set \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> myM SB" where
"createOutput cs n var = Abs_SB(\<lambda>c. (c \<in> cs) \<leadsto> \<up>(B (((n + var) mod 2) = 0) ))"

definition myTr_h::"(channel \<rightharpoonup> myM) \<Rightarrow> channel \<Rightarrow> nat" where
"myTr_h f c =  (THE a. Some (N a) =(f c))"
(* Somehow define the transition function *)
(* use the createOutput function *)
definition myTransition :: "(myState \<times>(channel \<rightharpoonup> myM)) \<Rightarrow> (myState \<times> myM SB)" where
"myTransition x =   (if  ((getSubState (fst x) = singleState) \<and> (snd x c1 \<noteq> None)) 
                     then (State singleState (myTr_h (snd x) c1 + getVarI (fst x)), 
                            (createOutput {c1} (getVarI (fst x)) (myTr_h(snd x) c1)))
                     else (State \<NN> 0, (sbLeast {c1})))"

lift_definition myAutomaton :: "(myState, myM) automaton" is "(myTransition, State singleState 0, sbLeast {}, {}, {})"
 by simp

definition mySPF :: "myM SPF" where
"mySPF = H myAutomaton"




section \<open>Automaton Lemma\<close>


end
