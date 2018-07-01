(* Draft for Non-Deterministic Automaton *)

theory NDA

imports "../../USpec" "../SpsStep" NDA_functions "../SPS"

begin

default_sort type


fun ndaWell::"((('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr) \<Rightarrow> bool " where
"ndaWell (transition, initialState, Discr chIn, Discr chOut) = finite chIn"

(* FYI: Non-deterministic version *)
cpodef ('state::type, 'm::message) ndAutomaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr. ndaWell f}"
  sorry

setup_lifting type_definition_ndAutomaton



definition ndaTransition :: "('s, 'm::message) ndAutomaton \<rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('s \<times> 'm SB) set rev))" where
"ndaTransition \<equiv> \<Lambda> nda. fst (Rep_ndAutomaton nda)"

definition ndaInitialState :: "('s, 'm::message) ndAutomaton \<rightarrow> ('s \<times> 'm SB) set rev" where
"ndaInitialState = (\<Lambda> nda. fst (snd (Rep_ndAutomaton nda)))"

definition ndaDom :: "('s, 'm::message) ndAutomaton \<rightarrow> channel set discr" where
"ndaDom = (\<Lambda> nda. fst (snd (snd (Rep_ndAutomaton nda))))"

definition ndaRan :: "('s, 'm::message) ndAutomaton \<rightarrow> channel set discr" where
"ndaRan =  (\<Lambda> nda. snd (snd (snd (Rep_ndAutomaton nda))))" 

(* ToDo *)
(* Very Very similar to helper over automaton *)
thm helper_def

(* Es klappt aber nicht.... Der nichtdeterminismus wird nicht berücksichtigt! 
  und ich laufe immer wieder in das problem: https://git.rwth-aachen.de/montibelle/automaton/core/issues/68 *)



(* thats the equivalent to the deterministic version ... so no nondeterminism *)
definition ndaHelper:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) (*set rev*)) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where
"ndaHelper s transition \<equiv>  \<Lambda> h. (\<lambda>e. spsRtIn\<cdot>(spsConcOut (snd (transition (s,e)))\<cdot>(h (fst (transition (s,e))))))"     


(* nondeterministic... but is it cont in h ? *)
definition ndaHelper2:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where
"ndaHelper2 s transition \<equiv>  \<Lambda> h. (\<lambda>e. uspecFlatten undefined undefined (*TODO remove undefined *)
    (setrevImage (\<lambda>(nextState::'s, nextOut::'m SB). spsRtIn\<cdot>(spsConcOut nextOut\<cdot>(h nextState))::'m SPS) (transition (s,e))))"



section \<open>lemma over ndaHelper2\<close>

(* definitely not injective... some_h is to general *)
lemma "inj (\<lambda>(nextState::'s, nextOut::'m::message SB). (spsConcOut nextOut\<cdot>(some_h nextState)))"
  oops




(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h nda \<equiv> let dom = (undiscr(ndaDom\<cdot>nda));
                 ran = (undiscr(ndaRan\<cdot>nda)) in 
  uspecStateFix dom ran\<cdot>(\<Lambda> h. (\<lambda>s. spsStep dom ran\<cdot>(ndaHelper2 s (ndaTransition\<cdot>nda)\<cdot>h)))"



definition nda_H :: "('s, 'm::message) ndAutomaton \<Rightarrow> 'm SPS" where
"nda_H nda \<equiv> uspecFlatten (undiscr(ndaDom\<cdot>nda))(undiscr(ndaRan\<cdot>nda)) 
                (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(nda_h nda state)) (ndaInitialState\<cdot>nda))" 


lemma nda_rep_cont[simp]: "cont Rep_ndAutomaton"
  by (simp add: cont_Rep_ndAutomaton)


lemma "cont (\<lambda>nda. fst (Rep_ndAutomaton nda))"
  by simp


(*
lemma "cont (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep some suff\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  by simp

lemma "cont (\<lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"
  by simp
*)

end