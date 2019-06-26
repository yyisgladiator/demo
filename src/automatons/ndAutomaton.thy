theory ndAutomaton

imports bundle.SB_fin spf.SPF dAutomaton
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

lift_definition nda2daSet::" ('state::type, 'in, 'out) ndAutomaton \<rightarrow>  ('state, 'in, 'out) dAutomaton set"is (* only cont if state and in finite?*)
"\<lambda> nda. {da | da. \<forall>s sbe. ((daTransition da) s sbe) \<in> ((ndaTransition\<cdot>nda) s sbe) \<and> 
                      (daInitState da,daInitOut da) \<in> (ndaInitConfig\<cdot>nda)}"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply(simp add: ndaTransition_def ndaInitConfig_def,auto)
   apply(simp_all add: less_set_def)
  apply auto[1]
  apply (metis SetPcpo.less_set_def fun_below_iff in_mono)
  apply(simp add: lub_fun contlub_cfun_arg contlub_cfun_fun setify_def set_cpo_simps Union_is_lub)
  apply(subst lub_fun)
  using ch2ch_Rep_cfunR ch2ch_fun apply fastforce
apply(simp add: lub_fun contlub_cfun_arg contlub_cfun_fun set_cpo_simps Union_is_lub ndaTransition_def ndaInitConfig_def)
  apply auto
  sorry
(*
definition ndaInitStates::"('state::type, 'in, 'out) ndAutomaton \<Rightarrow> 'state set" where
"ndaInitStates aut = fst `(snd(aut))"

definition ndaInitOuts::"('state::type, 'in, 'out) ndAutomaton \<Rightarrow> ('out\<^sup>\<Omega>) set" where
"ndaInitOuts aut = snd `(snd(aut))"
*)
lift_definition  ndaStateSem :: "('s::type, 'in::{chan,finite}, 'out) ndAutomaton \<rightarrow> ('s \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set)"is
"\<lambda> nda. (\<lambda>s.  {daStateSem da s| da. da \<in> nda2daSet\<cdot>nda})"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
   apply(rule monofunI)
  apply(rule fun_belowI)
   apply (smt Collect_mono SetPcpo.less_set_def cont_pref_eq1I subsetD)
  apply(rule fun_belowI)
  apply(simp add: lub_fun contlub_cfun_arg contlub_cfun_fun set_cpo_simps Union_is_lub)
  by auto
  

definition ndaSem :: "('s::type, 'in::{chan,finite}, 'out) ndAutomaton \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaSem  \<equiv> (\<lambda> nda. {(\<Lambda> sb. iout \<bullet>\<^sup>\<Omega> (spf\<cdot>sb)) | iout spf s. (s,iout)\<in>(ndaInitConfig\<cdot>nda) \<and> spf\<in>((ndaStateSem\<cdot>nda)s)})"

end