(*<*)(*:maxLineLen=68:*)
theory ndAutomaton
  imports bundle.SB_fin (* dAutomaton *)
begin
default_sort "chan"

(*>*)

subsection \<open>Non-Deterministic Automaton\<close> text\<open>\label{sub:ndaut}\<close>

text\<open>Non-deterministic automatons can model behaviours of
incomplete systems or components since their behaviour could be
arbitrary, we cannot use automatons with a deterministic transition
function. Thus, the non-deterministic automatons transition function
maps to a set that represents all possible behaviours of the system.
Furthermore, we also might have different combinations of initial
states and outputs for a under-specified system, hence we define the
initial configuration of a non-deterministic automaton as a set of 
tuples, where each tuple represents an initial state and an initial
output. Deterministic automatons are a special case of 
non-deterministic automatons where the transition function maps to a
singleton and the initial configuration is also a singleton.\<close>

text\<open>This first interpretation of non-deterministic automatons 
allows the initial configuration or the output of the transition
function to be empty. We define these as incomplete automatons.\<close>

record ('state::type,'in, 'out) 
ndAutomaton_incomplete  =
  ndaiTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set))"
  ndaiInitConfig :: "('state \<times> 'out\<^sup>\<Omega>) set"

text\<open>A complete automaton has a defined behaviour in all cases. One
can complete the automatons with incomplete behaviour using
different approaches. The Chaos approach, where the automaton
behaves completely arbitrary, will be presented after instantiating
complete non-deterministic automatons as a \gls{cpo}.\<close>

cpodef ('state::type,'in,'out)ndAutomaton  =
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

setup_lifting type_definition_ndAutomaton

text\<open>The chaos completion is realized using the universal set \<open>UNIV\<close>
that contains all possible elements. If the initial configuration is
empty, it is replaced by \<open>UNIV\<close>. If the transition function of the
incomplete automaton would map to the empty set, it will instead map
to \<open>UNIV\<close>. Thus, the resulting automaton is completed by the chaos
completion.\<close>

lift_definition ndai2ndac::
"('state::type,'in, 'out) ndAutomaton_incomplete
\<Rightarrow>('state::type,'in, 'out) ndAutomaton " is
"\<lambda>auti. ((\<lambda> s sbe. let out = ndaiTransition auti s sbe in
                   if out = {} then UNIV else out),
                   if ndaiInitConfig auti = {} 
                               then UNIV else ndaiInitConfig auti)"
  apply auto
  by (metis (mono_tags) empty_not_UNIV)

text\<open>For obtaining the transitions function or the initial 
configuration two getters are defined.\<close>

definition ndaTransition::
"('state::type, 'in, 'out) ndAutomaton \<rightarrow> 
('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set)" where
"ndaTransition = (\<Lambda> aut. fst(Rep_ndAutomaton aut))"

definition ndaInitConfig::
"('state::type, 'in, 'out) ndAutomaton \<rightarrow> 
('state \<times>'out\<^sup>\<Omega>)set" where
"ndaInitConfig = (\<Lambda> aut. (snd(Rep_ndAutomaton aut)))"

subsubsection\<open>Semantic\<close>

text\<open>The semantic of a non-deterministic automaton can not be
described by a single \gls{spf} because it would have a
deterministic behaviour. Instead, the semantic is a \gls{sps} where
each \gls{spf} describes a possible behaviour of the automaton.\<close>

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

text\<open>Similar to the deterministic semantic mappings we define a 
non-deterministic state semantic mapping and then use it to define 
the semantic mapping of an automaton. The semantic mapping is 
defined greatest fixed point to characterize the greatest 
possible behaviour of a component.\<close>

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

text\<open>All resulting \glspl{spf} in the semantic iterate over the
input and then decide in each step depending on the current state of
the automaton how to process its input. The output is then an
element of the output from the transition function. Hence, it is
possible for a \gls{spf} to produce different output, even if the 
state and input of the automaton did not change. This represents the
non-determinism of the component.\<close>

lemma ndastatesem_unfold:"ndaStateSem nda s = {sb_split\<cdot>(\<lambda> sbe. 
\<Lambda> sb. let (nextSPF, output) = f' sbe in output \<bullet>\<^sup>\<Omega> nextSPF\<cdot>sb)|
     f f' .(\<forall>sbe. f sbe \<in> (ndaTransition\<cdot>nda) s sbe \<and>
            (\<forall>sbe. snd (f' sbe) = snd (f sbe) \<and> 
                   fst (f' sbe) \<in> ndaStateSem nda (fst (f sbe))))}"
  unfolding ndaStateSem_def
  apply(subst gfp_unfold)
  using ndastatesem_mono apply auto[1]
  by auto

text\<open>Since there can be more than one initial configuration the 
semantic contains \glspl{spf} representing each initial
configuration.\<close>

definition ndaSem :: 
"('s::type, 'in::{chan, finite}, 'out) ndAutomaton 
\<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaSem  nda \<equiv> {(\<Lambda> sb. initOut \<bullet>\<^sup>\<Omega> spf\<cdot>sb) | initOut initState spf.
    (initState,initOut)\<in>ndaInitConfig\<cdot>nda \<and> 
                    spf\<in>(ndaStateSem nda initState)}"

(*<*)
end
(*>*)