theory dAutomaton

imports "../bundle/SB_fin" spf.SPF
begin

section \<open>Deterministic Automaton\<close>
default_sort "chan"

subsection \<open>Deterministic Automaton definition \<close>
record ('state::type, 'in, 'out) dAutomaton  =
  daTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>))"
  daInitState :: "'state"
  daInitOut:: "'out\<^sup>\<Omega>"

subsubsection \<open>Deterministic Automaton general functions\<close>

definition daNextState:: "('s::type,'c ,'d) dAutomaton \<Rightarrow> 's \<Rightarrow>  'c\<^sup>\<surd> \<Rightarrow> 's" where
"daNextState aut s m = fst ((daTransition aut) s m)"

definition daNextOut:: "('s, 'c,'d) dAutomaton \<Rightarrow> 's \<Rightarrow>  'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<Omega>" where
"daNextOut aut s m = snd ((daTransition aut) s m)"

subsection \<open>Semantic for deterministic Automaton \<close>

subsubsection \<open>Semantic helper functions \<close>

lift_definition spfStep::" (('c::{chan,finite})\<^sup>\<surd> \<rightarrow> ('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>))\<rightarrow>('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>)" is
"(\<lambda> h. (\<Lambda> sb. sb_case\<cdot>sb\<cdot>h))"
  by(simp add: cfun_def)

definition dahelper:: "('s::type \<Rightarrow>'e::cpo \<Rightarrow> ('s \<times> 'O\<^sup>\<Omega>)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)) \<rightarrow> ('e \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"dahelper f s \<equiv> \<Lambda> h. (\<Lambda> e. (\<Lambda> sb. (((snd (f s e)))\<bullet>\<^sup>\<Omega>((h (fst (f s e)))\<cdot>sb))))"

subsubsection \<open>Semantic helper functions lemmas\<close>

lemma spfstep_insert:"spfStep\<cdot>h\<cdot>sb = sb_case\<cdot>sb\<cdot>h"
  by(simp add: spfStep.rep_eq)

lemma spfstep_sbstep:assumes"\<forall>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c \<noteq> \<epsilon>"
  shows "(spfStep\<cdot>f)\<cdot>sb = (f\<cdot>(sbHdElem sb))\<cdot>(sbRt\<cdot>sb)"
  oops

lemma spfstep_sbestep:
shows "spfStep\<cdot>f\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = f\<cdot>sbe\<cdot>(sb)"
  oops

lemma spfstep_inj:"inj (Rep_cfun spfStep)"
  oops

subsubsection \<open>Sematntic\<close>

definition daStateSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"daStateSem automat = fix\<cdot>(\<Lambda> h. (\<lambda>s. spfStep \<cdot>(dahelper (daTransition automat) s\<cdot>h)))"

definition daSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem automat = (\<Lambda> sb. (daInitOut automat)\<bullet>\<^sup>\<Omega>((daStateSem automat (daInitState automat))\<cdot>sb))"

subsubsection \<open>Statesematntic lemmas\<close>

lemma dastatesem_unfolding: "(daStateSem automat s) = spfStep\<cdot>(dahelper (daTransition automat) s\<cdot>(daStateSem automat))"
  oops

lemma dastatesem_bottom:assumes "\<exists>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c = \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb = \<bottom>"
  oops

lemma dastatesem_strict:
  shows "(daStateSem automat s)\<cdot>\<bottom> = \<bottom>"
  oops

lemma dastatesem_step: assumes "\<forall>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c \<noteq> \<epsilon>"
            shows "(daStateSem automat s)\<cdot>sb = ((dahelper (daTransition automat) s\<cdot>(daStateSem automat))\<cdot>(sbHdElem sb))\<cdot>sb"
  oops

lemma dastatesem_final:assumes "\<forall>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c \<noteq> \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb =
  (daNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> (((daStateSem automat (daNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  oops

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons\<cdot>sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  oops

lemma dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "(daStateSem da s)\<cdot>(sbECons\<cdot>sbe\<cdot>sb) = out  \<bullet>\<^sup>\<Omega> ((daStateSem da nextState)\<cdot>sb)"
  oops


(*
lemma dastatesem_strict[simp]: "spfIsStrict (daStateSem da state)"
  oops
*)

lemma dastatesem_weak: 
  assumes "\<And>state sbe. 1 \<le> sbLen (daNextOut automat state sbe)"
  shows     "weak_well (daStateSem automat s)"
  oops

lemma dastatesem_least: assumes"(\<lambda>s. spfStep\<cdot>(dahelper (daTransition X) s\<cdot>Z)) \<sqsubseteq> Z"
                  shows"daStateSem X \<sqsubseteq> Z"
  oops


subsubsection \<open>Sematntic lemmas\<close>

lemma dasem_insert:
  "daSem automat\<cdot>sb = (daInitOut automat) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daInitState automat))\<cdot>sb)"
  by (simp add: daSem_def)

lemma dasem_bottom:
  shows "daSem automat\<cdot>\<bottom> = daInitOut automat"
  oops

lemma dasem_strong:
  assumes "weak_well(daStateSem automat (daInitState automat))"
  and     "1 \<le> sbLen (daInitOut automat)"
  shows "strong_well (daSem automat)"
  oops

subsection \<open>Deterministic Weak Automata definition\<close>

record ('state::type, 'in, 'out, 'initOut) dAutomaton_weak  =
  dawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>))"
  dawInitState :: "'state"
  dawInitOut:: "'initOut\<^sup>\<surd>"

definition daw2da::"('state::type, 'in, 'out,'initOut) dAutomaton_weak \<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da \<equiv> \<lambda>aut. (| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),sbe2sb\<cdot>(snd(dawTransition aut s sbe)))), 
                 daInitState = dawInitState(aut), daInitOut = (sbe2sb\<cdot>(dawInitOut aut)\<star>) |)"


subsection \<open>Weak Automaton Semantic options\<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_weak::"('state::type, 'in::{chan,finite}, 'out::chan, 'initOut) dAutomaton_weak \<Rightarrow> ('in,'out)spfw"where
"semantik_weak autw = Abs_spfw(daSem(daw2da autw))"


subsubsection \<open>Rum96 Automaton Semantic\<close>

function Rum_tap::"('s::type, 'in,'out,'initOut) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('in,'out) spfw) set" where
"Rum_tap aut = {h | h. \<forall>m s. \<exists>t out . ((snd(dawTransition aut s m)) = out) \<and> 
                    (\<exists>h2\<in> (Rum_tap aut). \<forall>i .
          (Rep_spfw(h s))\<cdot>(m \<bullet>\<^sup>\<surd> i) = out \<bullet>\<^sup>\<surd> ((Rep_spfw(h2 t))\<cdot>i))}"
  by(simp)+

(*Termination for Rum_tap necessary?*)

fun Rum_ta::"('s::type, 'in,'out,'initOut) dAutomaton_weak \<Rightarrow> (('in,'out) spfw) set"where
"Rum_ta aut = {g | g. \<exists>h\<in>(Rum_tap aut). \<exists> s (out::'initOut\<^sup>\<surd>). \<forall>i. 
              (Rep_spfw g)\<cdot>i = ((sbe2sb\<cdot>out)\<star>)\<bullet>\<^sup>\<Omega>((Rep_spfw(h s))\<cdot>i)}"

subsection \<open>Strong Deterministic Automaton Definition \<close>

type_synonym ('s,'in,'out)dAutomaton_strong = "('s,'in,'out,'out)dAutomaton_weak"


subsection \<open>Strong Automaton Semantic options \<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_strong::"('s::type, 'in::{finite,chan}, 'out) dAutomaton_strong \<Rightarrow> ('in,'out)spfs"where
"semantik_strong auts = Abs_spfs(semantik_weak auts)"

subsection \<open>Rum96 Automaton Semantic \<close>

fun Rum_ta_strong::"('s::type, 'in,'out) dAutomaton_strong \<Rightarrow> (('in,'out) spfs) set"where
"Rum_ta_strong aut = Abs_spfs `(Rum_ta aut)"

end