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
(* ToDo: wellformed condition *)

(* FYI: in the non-deterministic case the automaton will be a cpo *)

(* The content is:
  transition function \<times> initial state \<times> initial Output \<times> input domain \<times> output domain *)
typedef ('state::type, 'm::message) automaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set. True}"
  sorry

definition getInitialState :: "('s, 'm::message) automaton \<Rightarrow> 's" where
"getInitialState automat = fst (snd (Rep_automaton automat))"

definition getDom :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getDom = undefined" (* todo *)

definition getRan :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getRan = undefined" (* todo *)

setup_lifting type_definition_automaton

(* HK is defining this. returns the fixpoint *)
definition myFixer :: "channel set \<Rightarrow> channel set \<Rightarrow> (('s \<Rightarrow> 'm SPF)\<rightarrow>('s \<Rightarrow> 'm SPF)) \<rightarrow> ('s \<Rightarrow> 'm SPF)" where
"myFixer = undefined"

definition spfLeast::"channel set \<Rightarrow> channel set \<Rightarrow> 'm::message SPF" where
"spfLeast cin cout = Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = cin) \<leadsto> sbLeast cout)"

definition spfStep_h2::"(channel\<rightharpoonup>'m::message discr\<^sub>\<bottom>) \<Rightarrow> (channel\<rightharpoonup>'m)" where
"spfStep_h2 = (\<lambda>f. (\<lambda>c. (c \<in> dom f) \<leadsto> (THE a. updis a = f \<rightharpoonup> c)))"

definition spfStep_h1::"channel set \<Rightarrow> channel set \<Rightarrow>((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<Rightarrow>((channel\<rightharpoonup>'m discr\<^sub>\<bottom>)\<rightarrow> 'm SPF)" where
"spfStep_h1 In Out= (\<lambda> h. (\<Lambda> f. if (\<forall>c. (c \<in> In \<longrightarrow> (f \<rightharpoonup> c \<noteq> \<bottom>))) then h (spfStep_h2 f) else spfLeast In Out))"

(* Skeleton of spfStep. Returns the SPF that switches depending on input *)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) "

(* Defined by SWS *)
definition spfRt :: "'m SPF \<rightarrow> 'm SPF" where
"spfRt = undefined"

(* Defined by JCB *)
definition spfCons :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfCons = undefined"

(* Converter function. *)
  (* definition should be right, but needs to be nicer *)
definition helper:: "(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 'm SPF) \<rightarrow> ('e \<Rightarrow> 'm SPF)" where
"helper f s \<equiv> \<Lambda> h. (\<lambda> e. spfRt\<cdot>(spfCons (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))" 

lemma "cont (\<lambda>h. (\<lambda> e. spfCons (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))"
  oops

(* As defined in Rum96 *)
definition h :: "('s::type, 'm::message) automaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"h automat = myFixer (getDom automat)(getRan automat)\<cdot>(\<Lambda> h. (\<lambda>s. spfStep{}{}\<cdot>(helper undefined s\<cdot>h)))"

lemma "cont (\<lambda> h. (\<lambda>s. spfStep{}{}\<cdot>(helper automat s\<cdot>h)))"
  by simp

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition H :: "('s, 'm::message) automaton \<Rightarrow> 'm SPF" where
"H automat = h automat (getInitialState automat)"






(* From here everything should be automatically transformed from MontiArc-Automaton *)
section \<open>Automaton Datatypes\<close>

(* Only on idea how the states could be implemented *)
datatype substate = singleState  (* This are the actual states from MAA *)
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
                     else ((fst x), (sbLeast {c1})))"

lift_definition myAutomaton :: "(myState, myM) automaton" is "(myTransition, State singleState 0, sbLeast {}, {}, {})"
 by simp

definition mySPF :: "myM SPF" where
"mySPF = H myAutomaton"




section \<open>Automaton Lemma\<close>


end
