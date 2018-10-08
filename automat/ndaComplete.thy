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

type_synonym ('state, 'm) nda2TransF = "('state, 'm) ndAutomaton \<Rightarrow>
    (('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev))"

type_synonym ('state, 'm) nda2InitStateF = "('state, 'm) ndAutomaton \<Rightarrow> (('state \<times> 'm SB) set rev)"

(*******************************************************************)
section \<open>Definition\<close>
(*******************************************************************)

subsection \<open>predicate\<close>

definition transIsComplete:: "(('state \<times> 'm::message sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<Rightarrow>
  bool" where 
"transIsComplete \<equiv> \<lambda> trans. \<forall> state sbe. trans (state, sbe) \<noteq> Rev {}"

definition ndaIsComplete:: "('state::type, 'm::message) ndAutomaton \<Rightarrow> bool" where
"ndaIsComplete \<equiv> \<lambda> nda. transIsComplete (ndaTransition\<cdot>nda) \<and> ndaInitialState\<cdot>nda \<noteq> Rev {}"   


subsection \<open>transCompletion\<close>

(* Ignore completion: stay in the same state and produce empty SB *)
definition ignoreTrans_h:: "('state::type \<times> 'm::message sbElem) \<Rightarrow>
    ('state \<times> 'm SB) set rev" where
"ignoreTrans_h \<equiv> \<lambda> (state, sbe). Rev {(state, ubLeast UNIV)}"

(* Chaos completion: switch to an abitrary state and produce abitrary output *)
definition chaosTrans_h:: "('state::type \<times> 'm::message sbElem) \<Rightarrow>
    ('state \<times> 'm SB) set rev" where
"chaosTrans_h \<equiv>  \<lambda> (state, sbe). Rev UNIV"

(* *)
definition transCompletion:: "(('state::type \<times> 'm::message sbElem) \<Rightarrow> ('state \<times> 'm SB) set rev) 
  \<Rightarrow> ('state, 'm::message) nda2TransF"
  where "transCompletion f \<equiv> (\<lambda> nda. (\<lambda> (state, sbe). if ((ndaTransition\<cdot>nda) (state,sbe)  = Rev {}) then 
                f (state, sbe) else ((ndaTransition\<cdot>nda) (state,sbe))))"

(* DD: error completion - unknown transition will cause the automaton to switch to error state and
and it will stay there and produce no output (empty SB). To ensure that it will only produce no output,
it will stay in the error state for ever (see Steffen's MD)  *)
definition errorTransCompletion:: "'state::type \<Rightarrow> ('state, 'm::message) nda2TransF"
  where "errorTransCompletion errorState nda \<equiv> 
let errorStateP = (\<lambda> trans (state, sbe). trans (state,sbe)  = Rev {} \<or>
                                         state = errorState)
in (\<lambda> (state, sbe). if (errorStateP (ndaTransition\<cdot>nda) (state,sbe)) then 
                Rev {(errorState, ubLeast UNIV)} else ((ndaTransition\<cdot>nda) (state,sbe)))"

abbreviation ignorerTransCompletion:: "('state, 'm::message) nda2TransF"
  where "ignorerTransCompletion \<equiv> \<lambda> trans. transCompletion ignoreTrans_h trans"

abbreviation chaosTransCompletion:: "('state, 'm::message) nda2TransF"
  where "chaosTransCompletion \<equiv> \<lambda> trans. transCompletion ignoreTrans_h trans"


subsection \<open>InitStateCompletion\<close>
definition errorInit_h::  "'state  \<Rightarrow> (('state \<times> 'm::message SB) set rev)" where
"errorInit_h \<equiv> \<lambda> state. Rev {(state, ubLeast UNIV)}"

definition chaosInit_h:: "(('state \<times> 'm SB) set rev)" where
"chaosInit_h \<equiv> Rev UNIV"

definition initCompletion:: "(('state \<times> 'm SB) set rev) \<Rightarrow> 
   ('state::type, 'm::message) nda2InitStateF"
  where "initCompletion \<equiv> \<lambda> otherInit nda.  if (ndaInitialState\<cdot>nda = Rev {}) then otherInit else
                                    ndaInitialState\<cdot>nda"

lift_definition ndaCompletion:: "('state::type, 'm::message) nda2TransF \<Rightarrow>
  ('state::type, 'm::message) nda2InitStateF \<Rightarrow>
  ('state::type, 'm::message) ndAutomaton 
  \<Rightarrow> ('state::type, 'm::message) ndAutomaton"
  is
"\<lambda> (transComplete::('state::type, 'm::message) nda2TransF) (initComplete::('state, 'm) nda2InitStateF) nda. 
  (transComplete nda, initComplete nda, Discr (ndaDom\<cdot>nda),  Discr (ndaRan\<cdot>nda))"
  by simp

abbreviation ndaChaosCompletion:: "('state::type, 'm::message) ndAutomaton 
  \<Rightarrow> ('state::type, 'm::message) ndAutomaton"
  where
"ndaChaosCompletion \<equiv> ndaCompletion chaosTransCompletion (initCompletion chaosInit_h)"

abbreviation ndaErrorCompletion:: "'state \<Rightarrow>('state::type, 'm::message) ndAutomaton 
  \<Rightarrow> ('state::type, 'm::message) ndAutomaton"
  where
"ndaErrorCompletion state \<equiv> ndaCompletion (errorTransCompletion state) (initCompletion (errorInit_h state))"


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
  apply (simp add: transCompletion_def)
  by (meson assms transIsComplete_def)

lemma ndaChaosCompletion_true: "ndaIsComplete (ndaChaosCompletion nda)"
  apply (rule ndaiscomplI)
   apply (simp_all add: ndaCompletion_def ndaTransition_def)
   apply (metis (no_types) Rep_ndAutomaton_inverse eq_fst_iff ignoreTrans_h_def insert_not_empty inv_rev_rev ndaCompletion.rep_eq old.prod.case transIsComplete_def transcompl_complI)
  by (simp add: Abs_ndAutomaton_inverse chaosInit_h_def initCompletion_def ndaInitialState.rep_eq)

lemma ndaErrorCompletion_true: "ndaIsComplete (ndaErrorCompletion state nda)"
  by (simp add: errorInit_h_def errortranscompl_compl initCompletion_def ndaCompletion.rep_eq 
      ndaInitialState.rep_eq ndaIsComplete_def ndaTransition.rep_eq)


end