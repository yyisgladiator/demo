(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
*)

theory Automaton
imports SPS
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
  by blast
setup_lifting type_definition_automaton

definition getTransition :: "('s, 'm::message) automaton \<Rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('s \<times> 'm SB))" where
"getTransition automat = fst (Rep_automaton automat)"

definition getInitialState :: "('s, 'm::message) automaton \<Rightarrow> 's" where
"getInitialState automat = fst (snd (Rep_automaton automat))"

definition getDom :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getDom = undefined" (* todo *)

definition getRan :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getRan = undefined" (* todo *)




(* HK is defining this. returns the fixpoint *)
definition myFixer :: "channel set \<Rightarrow> channel set \<Rightarrow> (('s \<Rightarrow> 'm SPF)\<rightarrow>('s \<Rightarrow> 'm SPF)) \<rightarrow> ('s \<Rightarrow> 'm SPF)" where
"myFixer = undefined"

definition spfLeast::"channel set \<Rightarrow> channel set \<Rightarrow> 'm::message SPF" where
"spfLeast cin cout = Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = cin) \<leadsto> sbLeast cout)"

(* Skeleton of spfStep. Returns the SPF that switches depending on input *)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep cin cout \<equiv> \<Lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = cin) \<leadsto> undefined)"

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

lemma "cont (\<lambda>h. (\<lambda> e. spfRt\<cdot>(spfCons (snd (f (s,e)))\<cdot>(h (fst (f (s,e)))))))"
  by simp



(* As defined in Rum96 *)
definition h :: "('s::type, 'm::message) automaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"h automat = myFixer (getDom automat)(getRan automat)\<cdot>
    (\<Lambda> h. (\<lambda>s. spfStep (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>h)))"

lemma "cont (\<lambda> h. (\<lambda>s. spfStep (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>h)))"
  by simp

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition H :: "('s, 'm::message) automaton \<Rightarrow> 'm SPF" where
"H automat = h automat (getInitialState automat)"










(* From here everything should be automatically transformed from MontiArc-Automaton *)
section \<open>Automaton Datatypes\<close>

(* Only on idea how the states could be implemented *)
datatype substate = even | odd  (* This are the actual states from MAA *)
datatype myState = State substate nat bool (* And these have also the variables *)

fun getVarI :: "myState \<Rightarrow> nat" where
"getVarI (State _ n _) = n"

fun getSubState :: "myState \<Rightarrow> substate" where
"getSubState (State s _ _) = s"


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
  nat         \<Rightarrow> maps to channel c1, in MAA called "XXXX"
  bool        \<Rightarrow> maps to channel c2, in MAA calles "YYYY" *)
lift_definition createOutput :: "nat \<Rightarrow> bool \<Rightarrow> myM SB" is
"\<lambda>n b. ([c1 \<mapsto> \<up>(N n), c2 \<mapsto> \<up>(B b)])"
  by(auto simp add: sb_well_def)

function test4 :: "(channel \<rightharpoonup> nat stream) \<Rightarrow> bool" where
  "test4 [c1 \<mapsto> a] = True" |
  "dom f \<noteq> {c1} \<Longrightarrow> test4 f = False" 
  sorry

(* Somehow define the transition function *)
(* use the createOutput function *)
function myTransition :: "(myState \<times>(channel \<rightharpoonup> myM)) \<Rightarrow> (myState \<times> myM SB)" where
"myTransition (State even n b,  [c1 \<mapsto> N z])= ((State odd n b), createOutput 1 True)" |
"myTransition (State odd n b, [c1 \<mapsto> N z]) = ((State even n b), createOutput 0 False)"  |

"myTransition (_, [c1 \<mapsto> B z]) = undefined"  |
"dom f\<noteq> {c1} \<Longrightarrow> myTransition (_,f) = undefined"
  apply auto
  apply (smt dom_eq_singleton_conv getSubState.elims myM.exhaust substate.exhaust)
  apply (meson map_upd_eqD1 myM.distinct(1))
  apply (meson option.distinct(1))
  apply (meson map_upd_eqD1 myM.distinct(1))
  by (metis option.simps(3))

lift_definition myAutomaton :: "(myState, myM) automaton" is "(myTransition, State even 0 True, sbLeast {}, {}, {})"
  by blast  (* In the final form of the automaton datatype we will have to proof stuff *)

definition mySPF :: "myM SPF" where
"mySPF = H myAutomaton"




section \<open>Automaton Lemma\<close>








section \<open>Non Deterministic Case \<close>

(* FYI: Non-deterministic version *)
typedef ('state::type, 'm::message) NDA = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('state \<times> 'm SB) set)) \<times> ('state \<times> 'm SB) set \<times> channel set \<times> channel set. True}"
  by blast

(* relation based on transition function and initial set *)
instantiation NDA :: (type, message) po
begin
  fun below_NDA :: "('a, 'b) NDA \<Rightarrow> ('a, 'b) NDA \<Rightarrow> bool" where
  "below_NDA n1 n2 = ((fst (Rep_NDA n1) \<sqsubseteq>  fst (Rep_NDA n2))  (* Transition function is subset *)
                  \<and>   (fst (snd (Rep_NDA n1)) \<sqsubseteq>  fst (snd (Rep_NDA n2)))  (* Initial states subset *)
                  \<and>   (fst (snd (snd (Rep_NDA n1))) =  fst (snd (snd (Rep_NDA n2))))  (* input domain identical *)
                  \<and>   (     (snd (snd (snd (Rep_NDA n1)))) =  (snd (snd (snd (Rep_NDA n2))))) )" (* output domain identical *)

instance
  apply(intro_classes)
    apply simp
  apply simp
  apply (meson below_trans)
  by (meson Rep_NDA_inject below_NDA.elims(2) below_antisym prod.expand)
end  

instance NDA :: (type, message) cpo 
  apply(intro_classes)
  apply (rule, rule is_lubI)
  sorry


definition ndaTransition :: "('s, 'm::message) NDA \<rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('s \<times> 'm SB) set))" where
"ndaTransition \<equiv> \<Lambda> nda. fst (Rep_NDA nda)"

definition ndaInitialState :: "('s, 'm::message) NDA \<rightarrow> ('s \<times> 'm SB) set" where
"ndaInitialState = undefined"

definition ndaDom :: "('s, 'm::message) NDA \<rightarrow> channel set" where
"ndaDom = undefined" (* todo *)

definition ndaRan :: "('s, 'm::message) NDA \<rightarrow> channel set" where
"ndaRan = undefined" (* todo *)



definition spsFix :: "('a \<rightarrow> 'a) \<rightarrow> 'a" where
"spsFix = undefined"  (* Die ganze function ist natürlich grober unsinn *)

(* like spfStep, only on SPS *)
definition spsStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep cin cout \<equiv> undefined"


(* ToDo *)
definition spsHelper:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set) \<rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where
"spsHelper s \<equiv> undefined (* \<Lambda> h. (\<lambda> e. (h (fst (f (s,e))))) *)"

(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) NDA \<rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h \<equiv>  \<Lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"

lemma "cont (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  oops

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition nda_H :: "('s, 'm::message) NDA \<rightarrow> 'm SPF set" where
"nda_H \<equiv> \<Lambda> nda. undefined"





end