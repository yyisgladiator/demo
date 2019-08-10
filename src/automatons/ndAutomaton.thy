(*<*)(*:maxLineLen=68:*)
theory ndAutomaton
  imports bundle.SB_fin (* dAutomaton *)
begin
(*>*)

section \<open>Non-Deterministic Automaton\<close>
default_sort "chan"

subsection \<open>Non-Deterministic Automaton definition \<close>

(* Doesn't like type constraints*)
(* type_synonym ('state, 'in, 'out) "ndAutomaton" = "(('state::type \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) \<times> ('state \<times>'out\<^sup>\<Omega>)set)"
*)

text \<open>Incomplete automatons. The transition-function might return the empty set.\<close>
record ('state::type, 'in::"{chan, finite}", 'out::chan) ndAutomaton_incomplete  =
  ndaiTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set))"
  ndaiInitConfig :: "('state \<times> 'out\<^sup>\<Omega>) set"

cpodef ('state::type, 'in::"{chan, finite}", 'out::chan) ndAutomaton  =
  "{(transition::(('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set))), initialConfig::('state \<times> 'out\<^sup>\<Omega>) set)
    | transition initialConfig.
      (\<forall>sbe state. transition state sbe\<noteq> {})
    \<and> initialConfig \<noteq> {}}"
   apply auto[1]
  apply(subst UU_eq_empty[symmetric])+
  apply(rule admI)
  apply(simp add: lub_prod)
  apply (auto simp add: lub_eq_Union)
  sorry

definition ndaTransition::"('state::type, 'in::{chan, finite}, 'out) ndAutomaton \<rightarrow> ('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set)" where
"ndaTransition = (\<Lambda> aut. fst(Rep_ndAutomaton aut))"

definition ndaInitConfig::"('state::type, 'in::{chan, finite}, 'out) ndAutomaton \<rightarrow> ('state \<times>'out\<^sup>\<Omega>)set" where
"ndaInitConfig = (\<Lambda> aut. (snd(Rep_ndAutomaton aut)))"

lemma ndastatesem_mono[simp]:"mono (\<lambda>h state. {sb_split\<cdot>(\<lambda>sbe. \<Lambda> sb.
    (let (nextSPF, output) = f' sbe in
                            output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb))

  | f f'.  \<forall>sbe . ((f sbe) \<in> (((ndaTransition\<cdot>nda) state) sbe))
        \<and> ( \<forall>sbe . snd (f' sbe) = snd (f sbe) \<and> fst (f' sbe) \<in> h (fst (f sbe)))})"
  apply(rule monoI)
  apply(simp add: prod.case_eq_if)
  apply(simp add: le_fun_def)
  apply auto
  apply(rule_tac x="f"in exI)
  apply(rule_tac x="f'" in exI)
  by auto

definition ndaStateSem :: "('s::type, 'in::{chan, finite}, 'out) ndAutomaton \<Rightarrow> ('s \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set)" where
"ndaStateSem nda \<equiv> gfp (\<lambda>h state. {sb_split\<cdot>(\<lambda> sbe. \<Lambda> sb.
    (let (nextSPF, output) = f' sbe in
                            output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb))

  | f f'.  \<forall>sbe . ((f sbe) \<in> (((ndaTransition\<cdot>nda) state) sbe))
        \<and> ( \<forall>sbe . snd (f' sbe) = snd (f sbe) \<and> fst (f' sbe) \<in> h (fst (f sbe)))})"
    (* TODO: Schöner! *)

lemma ndastatesem_unfold:"ndaStateSem nda s = {sb_split\<cdot>(\<lambda> sbe. \<Lambda> sb. let (nextSPF, output) = f' sbe in output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb)|
     f f' .(\<forall>sbe. f sbe \<in> (ndaTransition\<cdot>nda) s sbe \<and>
            (\<forall>sbe. snd (f' sbe) = snd (f sbe) \<and> fst (f' sbe) \<in> ndaStateSem nda (fst (f sbe))))}"
  unfolding ndaStateSem_def
  apply(subst gfp_unfold)
  using ndastatesem_mono apply auto[1]
  by auto

definition ndaSem :: "('s::type, 'in::{chan, finite}, 'out) ndAutomaton \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaSem  nda \<equiv> {(\<Lambda> sb. initOut \<bullet>\<^sup>\<Omega> spf\<cdot>sb) | initOut initState spf.
    (initState,initOut)\<in>ndaInitConfig\<cdot>nda \<and> spf\<in>(ndaStateSem nda initState)}"

(*<*)
end
(*>*)