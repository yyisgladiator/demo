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

type_synonym ('state, 'm) trans2TransFunc = "(('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<Rightarrow>
    (('state \<times> 'm sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev))"

(*******************************************************************)
section \<open>Definition\<close>
(*******************************************************************)

datatype CompletionType = Error | Reattach | Ignore | Chaos

subsection \<open>predicate\<close>

definition transIsComplete:: "(('state \<times> 'm::message sbElem) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<Rightarrow>
  bool" where 
"transIsComplete \<equiv> \<lambda> trans. \<forall> state sbe. trans (state, sbe) \<noteq> Rev {}"

definition ndaIsComplete:: "('state::type, 'm::message) ndAutomaton \<Rightarrow> bool" where
"ndaIsComplete \<equiv> \<lambda> nda. transIsComplete (ndaTransition\<cdot>nda)"  (* SWS: und initialState \<noteq> {} *)

subsection \<open>completion\<close>

definition ignoreComplete:: "('state::type \<times> 'm::message sbElem) \<Rightarrow>
    ('state \<times> 'm SB) set rev" where
"ignoreComplete \<equiv> \<lambda> (state, sbe). Rev {(state, ubclLeast (sbeDom sbe))}"
(* SWS: Allgemein ndaDom \<noteq> ndaRan *)

definition chaosComplete:: "('state::type \<times> 'm::message sbElem) \<Rightarrow>
    ('state \<times> 'm SB) set rev" where
"chaosComplete \<equiv> 
  \<lambda> (state, sbe). Rev UNIV"

definition transCompletion:: "(('state::type \<times> 'm::message sbElem) \<Rightarrow>
    ('state \<times> 'm SB) set rev) \<Rightarrow> ('state, 'm::message) trans2TransFunc"
  where "transCompletion f \<equiv> (\<lambda> trans. (\<lambda> (state, sbe). if (trans (state,sbe)  = Rev {}) then 
                f (state, sbe) else (trans (state,sbe))))"

definition errorTransCompletion:: "'state::type \<Rightarrow> ('state, 'm::message) trans2TransFunc"
  where "errorTransCompletion errorState \<equiv> 
let errorStateP = (\<lambda> trans (state, sbe). trans (state,sbe)  = Rev {} \<or>
                                         state = errorState)
in (\<lambda> trans. (\<lambda> (state, sbe). if (errorStateP trans (state,sbe)) then 
                Rev {(errorState, ubclLeast (sbeDom sbe))} else (trans (state,sbe))))"
(* SWS: Allgemein ndaDom \<noteq> ndaRan *)
(* SWS: Von dem Error-State kommt man nie wieder weg? Wieso? *)

abbreviation ignorerTransCompletion:: "('state, 'm::message) trans2TransFunc"
  where "ignorerTransCompletion \<equiv> \<lambda> trans. transCompletion ignoreComplete trans"

abbreviation chaosTransCompletion:: "('state, 'm::message) trans2TransFunc"
  where "chaosTransCompletion \<equiv> \<lambda> trans. transCompletion chaosComplete trans"


(* SWS: Bei completion chaos auch den InitialState-Completen *)
lift_definition ndaCompletion:: "('state::type, 'm::message) trans2TransFunc \<Rightarrow>
  ('state::type, 'm::message) ndAutomaton 
  \<Rightarrow> ('state::type, 'm::message) ndAutomaton"
  is
"\<lambda> (f::('state::type, 'm::message) trans2TransFunc) nda. 
  (f (ndaTransition\<cdot>nda), ndaInitialState\<cdot>nda, Discr (ndaDom\<cdot>nda),  Discr (ndaRan\<cdot>nda))"
  by simp

(* SWS: Ich hatte gedacht man generiert einfach "chaosTransCompletion" vor die Transitionsfunktion.
        Aber ich mag diesen Ansatz auch. Dann kann man mehr allgemein zeigen *)

(*******************************************************************)
section \<open>Lemma\<close>
(*******************************************************************)

lemma ndaiscompleI: assumes "\<And> state sbe. (ndaTransition\<cdot>nda) (state, sbe) \<noteq> Rev {}"
  shows "ndaIsComplete nda"
  by (simp add: assms ndaIsComplete_def transIsComplete_def)

lemma traniscompleI: assumes "\<And> state sbe. transition (state, sbe) \<noteq> Rev {}"
  shows "transIsComplete transition"
  by (simp add: assms ndaIsComplete_def transIsComplete_def)


lemma errortranscomplete_complete: "transIsComplete (errorTransCompletion state transition)"
  apply (simp add: transIsComplete_def)
  apply (rule allI) +
  by (simp add: errorTransCompletion_def)

lemma transcompletion_completeI: assumes "\<And>state sbe. f (state, sbe) \<noteq> Rev {}"
  shows "transIsComplete (transCompletion f ndaTrans)"
  apply (simp add: transIsComplete_def)
  apply (rule allI) +
  by (simp add: assms transCompletion_def)

lemma ndacomplete_complete:  assumes "\<And> transition. transIsComplete (f transition)" 
  shows "ndaIsComplete (ndaCompletion f nda)"
  by (simp add: assms ndaCompletion.rep_eq ndaIsComplete_def ndaTransition.rep_eq)



end