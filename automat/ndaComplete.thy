(*  Title:        ndaTotal
    Author:       David Duong
Description: 
  We want to totalise the given nda (if it is not total). It will be used to calculate its semantic
  Steps: 
    1. Define a predicate to prove that the given nda is total
    2. Update nda if it is not total using different techniques: 
      2.1 Error: the automaton will switch to the error state, stay in that state and
                   will not produce any output
      2.2 Reattach: the automaton will switch to an specific state 
                    and also produce an abitrary output
      2.3 Ignore: the automaton will stay in the same state and produce nothing.
      2.4 Chaos: the automaton will switch to an arbitrary state and also produce an abitrary output 

*)

theory ndaComplete

imports ndAutomaton

begin

type_synonym ('state, 'm) ndaTrans = "(('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev))"
type_synonym ('state, 'm) ndaInit = "(('state \<times> 'm SB) set rev)"
(*
type_synonym ('state, 'm) nda2TransF = "('state, 'm) ndAutomaton \<Rightarrow>
    (('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev))"

type_synonym ('state, 'm) nda2InitStateF = "('state, 'm) ndAutomaton \<Rightarrow> (('state \<times> 'm SB) set rev)"
*)
(*******************************************************************)
section \<open>Definition\<close>
(*******************************************************************)

subsection \<open>predicate\<close>

definition transIsComplete:: "(('state \<times> 'm::message sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<Rightarrow>
  bool" where 
"transIsComplete \<equiv> \<lambda> trans. \<forall> state sbe. trans (state, sbe) \<noteq> Rev {}"

definition ndaIsComplete:: "('state::type, 'm::message) ndAutomaton \<Rightarrow> bool" where
"ndaIsComplete \<equiv> \<lambda> nda. transIsComplete (ndaTransition\<cdot>nda) \<and> ndaInitialState\<cdot>nda \<noteq> Rev {}"   




subsection \<open>InitStateCompletion\<close>
definition errorInit_h::  "'state  \<Rightarrow> ('state, 'm::message) ndaInit" where
"errorInit_h \<equiv> \<lambda> state. Rev {(state, ubLeast UNIV)}"

definition chaosInit_h:: "('state, 'm::message) ndaInit" where
"chaosInit_h \<equiv> Rev UNIV"

definition initCompletion:: "'s set rev \<Rightarrow> 's set rev \<Rightarrow> 's set rev"
  where "initCompletion completeInit oldInit\<equiv> if (oldInit = Rev {}) then completeInit else oldInit"



subsection \<open>transCompletion\<close>

(* Ignore completion: stay in the same state and produce empty SB *)
definition ignoreTrans_h:: "('state::type \<times> 'm::message sbElem) \<Rightarrow> ('state \<times> 'm SB) set rev" where
"ignoreTrans_h \<equiv> \<lambda> (state, sbe). Rev {(state, ubLeast UNIV)}"

(* Chaos completion: switch to an abitrary state and produce abitrary output *)
definition chaosTrans_h:: "('state::type \<times> 'm::message sbElem) \<Rightarrow> ('state \<times> 'm SB) set rev" where
"chaosTrans_h \<equiv>  \<lambda> (state, sbe). Rev UNIV"

definition transCompletion:: "('s, 'm::message) ndaTrans \<Rightarrow> ('s, 'm::message) ndaTrans \<Rightarrow> ('s, 'm::message) ndaTrans" where 
"transCompletion complete transition \<equiv> (\<lambda> (state, sbe). initCompletion (complete (state, sbe)) (transition (state,sbe)))"

(* DD: error completion - unknown transition will cause the automaton to switch to error state and
and it will stay there and produce no output (empty SB). To ensure that it will only produce no output,
it will stay in the error state for ever (see Steffen's MD)  *)
definition errorTransCompletion:: "'state::type \<Rightarrow> ('state, 'm::message) ndAutomaton \<Rightarrow> ('state, 'm::message) ndaTrans"
  where "errorTransCompletion errorState nda \<equiv> 
let errorStateP = (\<lambda> trans (state, sbe). trans (state,sbe)  = Rev {} \<or>
                                         state = errorState)
in (\<lambda> (state, sbe). if (errorStateP (ndaTransition\<cdot>nda) (state,sbe)) then 
                Rev {(errorState, ubLeast UNIV)} else ((ndaTransition\<cdot>nda) (state,sbe)))"

abbreviation ignorerTransCompletion:: "('s, 'm::message) ndaTrans \<Rightarrow> ('s, 'm::message) ndaTrans"
  where "ignorerTransCompletion \<equiv> \<lambda> trans. transCompletion ignoreTrans_h trans"

abbreviation chaosTransCompletion:: "('s, 'm::message) ndaTrans \<Rightarrow> ('s, 'm::message) ndaTrans"
  where "chaosTransCompletion \<equiv> \<lambda> trans. transCompletion chaosTrans_h trans"

lift_definition ndaCompletion:: "(('state, 'm::message) ndaTrans \<Rightarrow> ('s, 'n::message) ndaTrans) \<Rightarrow>
  (('state, 'm::message) ndaInit \<Rightarrow> ('s, 'n::message) ndaInit) \<Rightarrow>
  ('state::type, 'm::message) ndAutomaton 
  \<Rightarrow> ('s::type, 'n::message) ndAutomaton"
  is
"\<lambda> (transCompletion::((('state, 'm::message) ndaTrans) \<Rightarrow> (('s, 'n::message) ndaTrans)))
   (initCompletion::(('state, 'm::message) ndaInit \<Rightarrow> ('s, 'n::message) ndaInit))
   (nda::('state::type, 'm::message) ndAutomaton). 
  ( transCompletion (ndaTransition\<cdot>nda), (initCompletion (ndaInitialState\<cdot>nda)), Discr (ndaDom\<cdot>nda),  Discr (ndaRan\<cdot>nda))"
  by simp

definition ndaChaosCompletion:: "('state::type, 'm::message) ndAutomaton \<Rightarrow> ('state::type, 'm::message) ndAutomaton" where
"ndaChaosCompletion \<equiv> ndaCompletion chaosTransCompletion (initCompletion chaosInit_h)"

(*
definition ndaErrorCompletion:: "'state \<Rightarrow> ('state::type, 'm::message) ndAutomaton \<Rightarrow> ('state::type, 'm::message) ndAutomaton" where
"ndaErrorCompletion state \<equiv> ndaCompletion (errorTransCompletion state) (initCompletion (errorInit_h state))"
*)

(*******************************************************************)
section \<open>Lemma\<close>
(*******************************************************************)

lemma ndaiscomplI: assumes "transIsComplete (ndaTransition\<cdot>nda)"
  and "ndaInitialState\<cdot>nda \<noteq> Rev {}"
  shows "ndaIsComplete nda"
  by (simp add: assms(1) assms(2) ndaIsComplete_def)

lemma traniscomplI: assumes "\<And> state sbe. transition (state, sbe) \<noteq> Rev {}"
  shows "transIsComplete transition"
  by (simp add: assms ndaIsComplete_def transIsComplete_def)


lemma errortranscompl_compl: "transIsComplete (errorTransCompletion state transition)"
  apply (simp add: transIsComplete_def)
  apply (rule allI) +
  by (simp add: errorTransCompletion_def)

lemma transcompl_complI: assumes "transIsComplete f"
  shows "transIsComplete (transCompletion f ndaTrans)"
  apply (simp add: transIsComplete_def)
  apply (rule allI) +
  apply (simp add: transCompletion_def initCompletion_def)
  by (meson assms transIsComplete_def)

lemma ndachaos_trans[simp]: "ndaTransition\<cdot>(ndaChaosCompletion nda) = chaosTransCompletion (ndaTransition\<cdot>nda)"
  by(simp add: ndaChaosCompletion_def ndaTransition.rep_eq ndaCompletion.rep_eq)

lemma ndachaos_init[simp]: "ndaInitialState\<cdot>(ndaChaosCompletion nda) = (initCompletion chaosInit_h) (ndaInitialState\<cdot>nda)"
  by(simp add: ndaChaosCompletion_def ndaInitialState.rep_eq ndaCompletion.rep_eq)

lemma ndachaos_dom[simp]: "ndaDom\<cdot>(ndaChaosCompletion nda) = ndaDom\<cdot>nda"
  by(simp add: ndaChaosCompletion_def ndaDom.rep_eq ndaCompletion.rep_eq)

lemma ndachaos_ran[simp]: "ndaRan\<cdot>(ndaChaosCompletion nda) = ndaRan\<cdot>nda"
  by(simp add: ndaChaosCompletion_def ndaRan.rep_eq ndaCompletion.rep_eq)

lemma ndachaostrans_complete[simp]: "chaosTransCompletion f s \<noteq> Rev {}"
  by(simp add: transCompletion_def chaosTrans_h_def initCompletion_def)

lemma ndachaosinit_complete[simp]: "initCompletion chaosInit_h init \<noteq> Rev {}"
  by(simp add: initCompletion_def chaosInit_h_def )

lemma ndachaos_complete[simp]: "ndaIsComplete (ndaChaosCompletion nda)"
  apply (rule ndaiscomplI)
   apply (simp_all add: ndaChaosCompletion_def ndaCompletion.rep_eq ndaTransition_def)
  apply (simp add: chaosTrans_h_def traniscomplI transcompl_complI)
  apply (simp add: ndaCompletion.rep_eq ndaInitialState.rep_eq initCompletion_def)
  by (simp add: chaosInit_h_def)

(*
lemma ndaErrorCompletion_true: "ndaIsComplete (ndaErrorCompletion state nda)"
  by (simp add: errorInit_h_def errortranscompl_compl initCompletion_def ndaCompletion.rep_eq 
      ndaInitialState.rep_eq ndaIsComplete_def ndaTransition.rep_eq)
*)

end