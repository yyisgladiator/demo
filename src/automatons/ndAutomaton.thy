theory ndAutomaton

imports bundle.SB_fin spf.SPF
begin

section \<open>Non-Deterministic Automaton\<close>
default_sort "chan"

subsection \<open>Non-Deterministic Automaton definition \<close>

(* Doesn't like type constraints*)
type_synonym ('state, 'in, 'out) "ndAutomaton" = "(('state::type \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) \<times> ('state \<times>'out\<^sup>\<Omega>)set)"

definition ndaTransition::"('state::type, 'in, 'out) ndAutomaton \<rightarrow> ('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set)" where
"ndaTransition = (\<Lambda> aut. fst(aut))"

definition ndaInitConfig::"('state::type, 'in, 'out) ndAutomaton \<rightarrow> ('state \<times>'out\<^sup>\<Omega>)set" where
"ndaInitConfig = (\<Lambda> aut. (snd(aut)))"
(*
definition ndaInitStates::"('state::type, 'in, 'out) ndAutomaton \<Rightarrow> 'state set" where
"ndaInitStates aut = fst `(snd(aut))"

definition ndaInitOuts::"('state::type, 'in, 'out) ndAutomaton \<Rightarrow> ('out\<^sup>\<Omega>) set" where
"ndaInitOuts aut = snd `(snd(aut))"
*)
definition  ndaStateSem :: "('s::type, 'in, 'out) ndAutomaton \<rightarrow> ('s \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set)" where
"ndaStateSem \<equiv> fix\<cdot>(\<Lambda> h. undefined)"

definition ndaSem :: "('s::type, 'in, 'out) ndAutomaton \<rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaSem  \<equiv> (\<Lambda> nda. undefined (ndaInitConfig\<cdot>nda) (ndaStateSem\<cdot>nda))"
                           
end