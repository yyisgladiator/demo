(*<*)
theory dAutomaton_causal
  imports dAutomaton spf.SPF
begin
(*>*)

section \<open>Deterministic Weak Automata\<close>

record ('state::type, 'in, 'out, 'initOut) dAutomaton_weak  =
  dawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>))"
  dawInitState :: "'state"
  dawInitOut:: "'initOut\<^sup>\<surd>"

definition daw2da::"('state::type, 'in::{chan,finite}, 'out,'initOut) dAutomaton_weak \<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da \<equiv> \<lambda>aut. (| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),sbe2sb (snd(dawTransition aut s sbe)))),
                 daInitState = dawInitState(aut), daInitOut = (sbe2sb (dawInitOut aut)\<star>) |)"

subsection \<open>Weak Automaton Semantic options\<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_weak::"('state::type, 'in::{chan,finite}, 'out::chan, 'initOut) dAutomaton_weak \<Rightarrow> ('in,'out)spfw"where
"semantik_weak autw = Abs_spfw(daSem(daw2da autw))"


definition dawStateSem :: "('s::type, 'I::{finite,chan},'O,'initO) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"dawStateSem da = fix\<cdot>(\<Lambda> h. (\<lambda> state. sb_case\<cdot>
                        (\<lambda>sbe. \<Lambda> sb.
                          let (nextState, output) = dawTransition da state sbe in
                            output \<bullet>\<^sup>\<surd> h nextState\<cdot>sb)
                      ))"

definition dawSem :: "('s::type, 'I::{finite,chan},'O,'initO) dAutomaton_weak \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dawSem da = (\<Lambda> sb. ((dawStateSem da (dawInitState da))\<cdot>sb))"

subsubsection \<open>Rum96 Automaton Semantic\<close>

function Rum_tap::"('s::type, 'in::{chan,finite},'out,'initOut) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('in,'out) spfw) set" where
"Rum_tap aut = {h | h. \<forall>m s. \<exists>t out . ((snd(dawTransition aut s m)) = out) \<and>
                    (\<exists>h2\<in> (Rum_tap aut). \<forall>i .
          (Rep_spfw(h s))\<cdot>(m \<bullet>\<^sup>\<surd> i) = out \<bullet>\<^sup>\<surd> ((Rep_spfw(h2 t))\<cdot>i))}"
  by(simp)+

(*Termination for Rum_tap necessary?*)

fun Rum_ta::"('s::type, 'in::{chan,finite},'out,'initOut) dAutomaton_weak \<Rightarrow> (('in,'out) spfw) set"where
"Rum_ta aut = {g | g. \<exists>h\<in>(Rum_tap aut). \<exists> s (out::'initOut\<^sup>\<surd>). \<forall>i.
              (Rep_spfw g)\<cdot>i = ((sbe2sb out)\<star>)\<bullet>\<^sup>\<Omega>((Rep_spfw(h s))\<cdot>i)}"

section \<open>Deterministic strong Automaton\<close>

type_synonym ('s,'in,'out)dAutomaton_strong = "('s,'in,'out,'out)dAutomaton_weak"


subsection \<open>Strong Automaton Semantic options \<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_strong::"('s::type, 'in::{finite,chan}, 'out) dAutomaton_strong \<Rightarrow> ('in,'out)spfs"where
"semantik_strong auts = Abs_spfs(semantik_weak auts)"

definition dasSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton_strong \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dasSem da = (\<Lambda> sb. (dawInitOut da) \<bullet>\<^sup>\<surd> ((dawStateSem da (dawInitState da))\<cdot>sb))"


subsection \<open>Rum96 Automaton Semantic \<close>

fun Rum_ta_strong::"('s::type, 'in::{chan,finite},'out) dAutomaton_strong \<Rightarrow> (('in,'out) spfs) set"where
"Rum_ta_strong aut = Abs_spfs `(Rum_ta aut)"


section \<open>automaton to sscanl equivalence locale\<close>

locale sscanlGen =
  fixes da::"('state::countable, 'in::{chan, finite}, 'out::{chan,finite}, 'initOut::chan) dAutomaton_weak"
  and fin::"'a::countable \<Rightarrow> 'in \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out \<Rightarrow> M"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

abbreviation "sscanlTransition \<equiv> (\<lambda> s a. 
  let (nextState, nextOut) = dawTransition da s (sbeGen.setter fin a) in
     (nextState, sbeGen.getter fout nextOut)
)"

lemma daut2sscanl:"dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(sscanlAsnd sscanlTransition state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  sorry

lemma daut2sscnalinit:"range(Rep::'out \<Rightarrow> channel) = range(Rep::'initOut\<Rightarrow> channel) \<Longrightarrow> dawSem da\<cdot>input = 
  sbeConvert(dawInitOut da) \<bullet>\<^sup>\<surd> dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>)"
  sorry

(* TODO: initiale ausgabe ... "sscanlA" kann nichts partielles ausgben.
  dh alles oder nichts. Das kann man durch den typ abfangen!
    * weak = "chIstEmpty" als assumption (oder besser, dafür eine klasse anlegen)
    * strong = gleicher typ wie ausgabe
*)

end

section \<open>automaton to smap equivalence locale\<close>

locale smapGen =
 fixes da::"('state::countable, 'in::{chan, finite}, 'out::{chan,finite}, 'initOut::chan) dAutomaton_weak"
  and fin::"'a::countable \<Rightarrow> 'in \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out \<Rightarrow> M"
  and loopState::"'state"
  assumes scscanlgenf:"sscanlGen fin fout"
  and singlestate:"\<And>sbe. fst((dawTransition da) loopState sbe) = loopState"
begin

abbreviation "smapTransition \<equiv> (\<lambda>a::'a. 
  let nextOut = snd((dawTransition da) loopState (sbeGen.setter fin a)) in
     sbeGen.getter fout nextOut)"

lemma daut2smap:"dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(smap smapTransition\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  sorry

end

sublocale  smapGen \<subseteq> sscanlGen
  by (simp add: scscanlgenf)


(*<*)
end
(*>*)