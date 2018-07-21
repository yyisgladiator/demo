(* Draft for Non-Deterministic Automaton *)

theory ndAutomaton

imports "../../USpec" "../SpsStep"  "../SPS" NDA_functions


begin

default_sort type


fun ndaWell::"((('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr) \<Rightarrow> bool " where
"ndaWell (transition, initialState, Discr chIn, Discr chOut) = finite chIn"

(* FYI: Non-deterministic version *)
cpodef ('state::type, 'm::message) ndAutomaton = 
  "{f::(('state \<times>'m sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr. ndaWell f}"
  sorry

setup_lifting type_definition_ndAutomaton



definition ndaTransition :: "('s, 'm::message) ndAutomaton \<rightarrow> (('s \<times>'m sbElem) \<Rightarrow> (('s \<times> 'm SB) set rev))" where
"ndaTransition \<equiv> \<Lambda> nda. fst (Rep_ndAutomaton nda)"

definition ndaInitialState :: "('s, 'm::message) ndAutomaton \<rightarrow> ('s \<times> 'm SB) set rev" where
"ndaInitialState = (\<Lambda> nda. fst (snd (Rep_ndAutomaton nda)))"

definition ndaDom :: "('s, 'm::message) ndAutomaton \<rightarrow> channel set" where
"ndaDom = (\<Lambda> nda. undiscr(fst (snd (snd (Rep_ndAutomaton nda)))))"

definition ndaRan :: "('s, 'm::message) ndAutomaton \<rightarrow> channel set" where
"ndaRan =  (\<Lambda> nda. undiscr(snd (snd (snd (Rep_ndAutomaton nda)))))" 

(* ToDo *)
(* Very Very similar to helper over automaton *)
thm da_helper_def

  (* nondeterministic... but is it cont in h ? *)
definition ndaToDo:: "channel set \<Rightarrow> channel set \<Rightarrow> ('s \<times> 'm::message SB) set rev \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"ndaToDo In Out S \<equiv> \<Lambda> h. uspecFlatten In Out 
                (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(h state)) S)"

(* Goals *)
lemma (* assumes "\<And>s c. s\<in>((inv Rev) S) \<Longrightarrow> c\<in>ubDom\<cdot>(snd s) \<Longrightarrow> # ((snd s) . c) < \<infinity>" *)
  shows  "monofun(\<lambda> h. uspecFlatten In Out (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(h state)) S))"
  apply(rule monofunI)
  oops

lemma "cont(\<lambda> h. uspecFlatten In Out (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(h state)) S))"
  oops

lemma "monofun (\<lambda> S. uspecFlatten In Out (setrevImage (\<lambda>(state, sb). spsConcOut sb\<cdot>(some_h state)) S))"
  oops



definition ndaHelper2:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<Rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where
"ndaHelper2 s transition \<equiv> \<Lambda> h. (\<lambda>e. ndaToDo undefined undefined (transition (s,e))\<cdot>h)"



(* delete first input element. This is here because "spfStep" does not call "sbRt" and the
  ndaHelper2 should be injektive and more general *)
definition ndaAnotherHelper :: "('s \<Rightarrow> 'm::message SPS) \<rightarrow> ('s \<Rightarrow> 'm SPS)" where
"ndaAnotherHelper \<equiv> (\<Lambda> h. (\<lambda> s. spsRtIn\<cdot>(h s)))"

lemma "cont (\<lambda> h. (\<lambda> s. spsRtIn\<cdot>(h s)))"
  by simp



(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) ndAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h nda \<equiv> let dom = (ndaDom\<cdot>nda);
                 ran = (ndaRan\<cdot>nda) in 
  uspecStateFix dom ran\<cdot>(\<Lambda> h. (\<lambda>s. spsStep dom ran\<cdot>(ndaAnotherHelper\<cdot>(ndaHelper2 s (ndaTransition\<cdot>nda)\<cdot>h))))"



definition nda_H :: "('s, 'm::message) ndAutomaton \<Rightarrow> 'm SPS" where
"nda_H nda \<equiv> ndaToDo (ndaDom\<cdot>nda)(ndaRan\<cdot>nda) (ndaInitialState\<cdot>nda)\<cdot>(nda_h nda)" 


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