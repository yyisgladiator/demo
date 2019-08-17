(*<*)(*:maxLineLen=68:*)
theory ndAutomaton
  imports bundle.SB_fin (* dAutomaton *)
begin
default_sort "chan"

(*>*)

subsection \<open>Non-Deterministic Automaton\<close> text\<open>\label{sub:ndaut}\<close>

text \<open>Incomplete automatons. The transition-function might return 
the empty set.\<close>

record ('state::type,'in::"{chan, finite}", 'out::chan) 
ndAutomaton_incomplete  =
  ndaiTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set))"
  ndaiInitConfig :: "('state \<times> 'out\<^sup>\<Omega>) set"

cpodef ('state::type,'in::"{chan, finite}",'out::chan)ndAutomaton  =
  "{(transition::(('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set)))
    , initialConfig::('state \<times> 'out\<^sup>\<Omega>) set)
    | transition initialConfig.
      (\<forall>state sbe. transition state sbe \<noteq> {})
    \<and> initialConfig \<noteq> {}}"
  apply auto[1]
  apply (subst UU_eq_empty[symmetric])+
  apply (rule admI)
  apply (simp add: lub_prod)
  apply (rule, rule, rule)
  apply (simp_all add: lub_eq_bottom_iff mem_Times_iff)
proof -
  fix Y :: "nat \<Rightarrow> 
  ('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) \<times> ('state \<times> 'out\<^sup>\<Omega>) set" 
  and state :: 'state and sbe :: "'in\<^sup>\<surd>"
  assume a1: "\<forall>i. (\<forall>state sbe. fst (Y i) state sbe \<noteq> \<bottom>) \<and> 
                               snd (Y i)           \<noteq> \<bottom>"
  assume "chain Y"
  then have "chain (\<lambda>n. fst (Y n))"
    using ch2ch_fst by blast
  then show "(\<Squnion>n. fst (Y n)) state sbe \<noteq> \<bottom>"
    using a1 by (simp add: fun_chain_iff lub_eq_bottom_iff lub_fun)
qed

definition ndaTransition::
"('state::type, 'in::{chan, finite}, 'out) ndAutomaton \<rightarrow> 
('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set)" where
"ndaTransition = (\<Lambda> aut. fst(Rep_ndAutomaton aut))"

definition ndaInitConfig::
"('state::type, 'in::{chan, finite}, 'out) ndAutomaton \<rightarrow> 
('state \<times>'out\<^sup>\<Omega>)set" where
"ndaInitConfig = (\<Lambda> aut. (snd(Rep_ndAutomaton aut)))"

subsubsection\<open>Semantic\<close>

lemma ndastatesem_mono[simp]:"mono (\<lambda>h state. {sb_split\<cdot>(\<lambda>sbe. \<Lambda> sb.
    (let (nextSPF, output) = f' sbe in
                            output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb))

  | f f'.  \<forall>sbe . ((f sbe) \<in> (((ndaTransition\<cdot>nda) state) sbe))
        \<and> ( \<forall>sbe . snd (f' sbe) = snd (f sbe) \<and> 
                   fst (f' sbe) \<in> h (fst (f sbe)))})"
  apply(rule monoI)
  apply(simp add: prod.case_eq_if)
  apply(simp add: le_fun_def)
  apply auto
  apply(rule_tac x="f"in exI)
  apply(rule_tac x="f'" in exI)
  by auto

definition ndaStateSem ::
 "('s::type, 'in::{chan, finite}, 'out) ndAutomaton 
\<Rightarrow> ('s \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set)" where
"ndaStateSem nda \<equiv> gfp (\<lambda>h state. {sb_split\<cdot>(\<lambda> sbe. \<Lambda> sb.
    (let (nextSPF, output) = f' sbe in
                            output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb))

  | f f'.  \<forall>sbe . ((f sbe) \<in> (((ndaTransition\<cdot>nda) state) sbe))
        \<and> ( \<forall>sbe . snd (f' sbe) = snd (f sbe) \<and> 
                   fst (f' sbe) \<in> h (fst (f sbe)))})"
    (* TODO: Schöner! *)

lemma ndastatesem_unfold:"ndaStateSem nda s = {sb_split\<cdot>(\<lambda> sbe. 
\<Lambda> sb. let (nextSPF, output) = f' sbe in output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb)|
     f f' .(\<forall>sbe. f sbe \<in> (ndaTransition\<cdot>nda) s sbe \<and>
            (\<forall>sbe. snd (f' sbe) = snd (f sbe) \<and> 
                   fst (f' sbe) \<in> ndaStateSem nda (fst (f sbe))))}"
  unfolding ndaStateSem_def
  apply(subst gfp_unfold)
  using ndastatesem_mono apply auto[1]
  by auto

definition ndaSem :: 
"('s::type, 'in::{chan, finite}, 'out) ndAutomaton 
\<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaSem  nda \<equiv> {(\<Lambda> sb. initOut \<bullet>\<^sup>\<Omega> spf\<cdot>sb) | initOut initState spf.
    (initState,initOut)\<in>ndaInitConfig\<cdot>nda \<and> 
                    spf\<in>(ndaStateSem nda initState)}"

(*<*)
end
(*>*)