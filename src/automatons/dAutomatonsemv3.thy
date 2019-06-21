theory dAutomatonsemv3

imports "../bundle/SBv3" "../spf/SPFv3"
begin

section \<open>Deterministic Automaton\<close>


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

definition spfStep_h::" ((('c::{chan,finite})\<^sup>\<surd>) u \<rightarrow> ('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>))\<rightarrow>('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>)" where
"spfStep_h \<equiv> (\<Lambda> h. (\<Lambda> sb. h\<cdot>(sbHdElem_h_cont\<cdot>sb)\<cdot>sb))"

lift_definition spfStep::" (('c::{chan,finite})\<^sup>\<surd> \<rightarrow> ('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>))\<rightarrow>('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>)" is
"(\<lambda> h. (\<Lambda> sb. spfStep_h\<cdot>(fup\<cdot>h)\<cdot>sb))"
  by(simp add: cfun_def)

definition da_helper:: "('s::type \<Rightarrow>'e::cpo \<Rightarrow> ('s \<times> 'O\<^sup>\<Omega>)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)) \<rightarrow> ('e \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"da_helper f s \<equiv> \<Lambda> h. (\<Lambda> e. (\<Lambda> sb. ( (sbRt\<cdot>(snd (f s e)))\<bullet>\<^sup>\<Omega>((h (fst (f s e)))\<cdot>sb))))"


subsubsection \<open>Sematntic\<close>

definition daStateSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"daStateSem automat = fix\<cdot>(\<Lambda> h. (\<lambda>s. spfStep \<cdot>(da_helper (daTransition automat) s\<cdot>h)))"

definition daSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem automat = (\<Lambda> sb. (daInitOut automat)\<bullet>\<^sup>\<Omega>((daStateSem automat (daInitState automat))\<cdot>sb))"

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