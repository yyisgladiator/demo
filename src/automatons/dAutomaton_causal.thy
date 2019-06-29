(*<*)
theory dAutomaton_causal
  imports dAutomaton spf.SPF
begin
(*>*)

section \<open>Deterministic Weak Automata\<close>

record ('state::type, 'in::"{chan,finite}", 'out, 'initOut) dAutomaton_weak  =
  dawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>))"
  dawInitState :: "'state"
  dawInitOut:: "'initOut\<^sup>\<surd>"

definition daw2da::"('state::type, 'in::{chan,finite}, 'out,'initOut) dAutomaton_weak \<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da \<equiv> \<lambda>aut. (| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),sbe2sb\<cdot>(snd(dawTransition aut s sbe)))),
                 daInitState = dawInitState(aut), daInitOut = (sbe2sb\<cdot>(dawInitOut aut)\<star>) |)"

subsection \<open>Weak Automaton Semantic options\<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_weak::"('state::type, 'in::{chan,finite}, 'out::chan, 'initOut) dAutomaton_weak \<Rightarrow> ('in,'out)spfw"where
"semantik_weak autw = Abs_spfw(daSem(daw2da autw))"


subsubsection \<open>Rum96 Automaton Semantic\<close>

function Rum_tap::"('s::type, 'in::{chan,finite},'out,'initOut) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('in,'out) spfw) set" where
"Rum_tap aut = {h | h. \<forall>m s. \<exists>t out . ((snd(dawTransition aut s m)) = out) \<and>
                    (\<exists>h2\<in> (Rum_tap aut). \<forall>i .
          (Rep_spfw(h s))\<cdot>(m \<bullet>\<^sup>\<surd> i) = out \<bullet>\<^sup>\<surd> ((Rep_spfw(h2 t))\<cdot>i))}"
  by(simp)+

(*Termination for Rum_tap necessary?*)

fun Rum_ta::"('s::type, 'in::{chan,finite},'out,'initOut) dAutomaton_weak \<Rightarrow> (('in,'out) spfw) set"where
"Rum_ta aut = {g | g. \<exists>h\<in>(Rum_tap aut). \<exists> s (out::'initOut\<^sup>\<surd>). \<forall>i.
              (Rep_spfw g)\<cdot>i = ((sbe2sb\<cdot>out)\<star>)\<bullet>\<^sup>\<Omega>((Rep_spfw(h s))\<cdot>i)}"

section \<open>Deterministic strong Automaton\<close>

type_synonym ('s,'in,'out)dAutomaton_strong = "('s,'in,'out,'out)dAutomaton_weak"


subsection \<open>Strong Automaton Semantic options \<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_strong::"('s::type, 'in::{finite,chan}, 'out) dAutomaton_strong \<Rightarrow> ('in,'out)spfs"where
"semantik_strong auts = Abs_spfs(semantik_weak auts)"

subsection \<open>Rum96 Automaton Semantic \<close>

fun Rum_ta_strong::"('s::type, 'in::{chan,finite},'out) dAutomaton_strong \<Rightarrow> (('in,'out) spfs) set"where
"Rum_ta_strong aut = Abs_spfs `(Rum_ta aut)"


(*<*)
end
(*>*)