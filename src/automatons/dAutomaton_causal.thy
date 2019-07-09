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


subsection \<open>*Causal Sem lemmas \<close>

lemma dawstatesem_unfolding: "(dawStateSem automat s) = sb_case\<cdot>(\<lambda>sbe. \<Lambda> sb .
                                                  let (nextState, output) = dawTransition automat s sbe in
                            output \<bullet>\<^sup>\<surd> ((dawStateSem automat) nextState\<cdot>sb))"
  unfolding dawStateSem_def
  apply(subst fix_eq)
  apply(subst beta_cfun)
  apply(intro cont2cont; simp)
  by auto

(* TODO: einheitliche assumption für diesen fall, KEIN rohes exists ! *)
lemma dawstatesem_bottom:assumes "\<exists>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c = \<epsilon>"
  shows "(dawStateSem automat s)\<cdot>sb = \<bottom>"
  sorry

lemma dawstatesem_strict:
  shows "(dawStateSem automat s)\<cdot>\<bottom> = \<bottom>"
  oops  (* gilt nicht für cEmpty-Bündel *)

lemma dawstatesem_step: assumes "\<And>c . sb \<^enum> c \<noteq> \<epsilon>"
  shows "(dawStateSem automat s)\<cdot>sb = snd (dawTransition da state (sbHdElem sb)) \<bullet>\<^sup>\<surd> h (fst (dawTransition da state (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  oops

lemma dawstatesem_final:assumes "\<And>c . sb \<^enum> c \<noteq> \<epsilon>"  (* Todo: einheitliche assumption *)
  shows "(dawStateSem automat s)\<cdot>sb =
  (dawNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<surd> (((dawStateSem automat (dawNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  oops

lemma dawstatesem_final_h2:
  shows "(dawStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =
  (dawNextOut automat s sbe) \<bullet>\<^sup>\<surd> ((dawStateSem automat (dawNextState automat s sbe))\<cdot>sb)"
  oops (* Das soll gehen mit "by(simp add: dastatesem_step)". Wenn nicht, mehr in den simplifier packen *)

lemma dastatesem_stepI:
  assumes "(dawNextOut da s sbe) = out"
      and "(dawNextState da s sbe) = nextState"
  shows "(dawStateSem da s)\<cdot>(sbECons sbe\<cdot>sb) = out  \<bullet>\<^sup>\<surd> ((dawStateSem da nextState)\<cdot>sb)"
  oops


(*
lemma dastatesem_strict[simp]: "spfIsStrict (daStateSem da state)"
  oops
*)

lemma dawstatesem_weak:
  shows     "weak_well (dawStateSem automat s)"
  oops

lemma dassem_insert:
  "dasSem automat\<cdot>sb = (dawInitOut automat) \<bullet>\<^sup>\<surd> ((dawStateSem automat (dawInitState automat))\<cdot>sb)"
  by (simp add: dasSem_def)

lemma dassem_bottom:
  shows "dasSem automat\<cdot>\<bottom> = sbe2sb (dawInitOut automat)"
  oops

lemma dassem_strong:
  shows "strong_well (dasSem automat)"
  oops

section \<open>automaton to sscanl equivalence locale\<close>

locale sscanlGen =
  fixes daTransition::"'state::countable \<Rightarrow> 'a::countable \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState::"'state"
  and   daInitialOut::"'b"    (* TODO, schwach kausal = keine initiale ausgabe! *)
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  and emptytype::"'c itself"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
      and emptytypeempty:"chIsEmpty emptytype"
begin

definition daTransitionH::"'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>)" where
"daTransitionH state sbe = (let (s,output) = daTransition state (sbeGen.getter fin sbe) in 
  (s, sbeGen.setter fout output))"

definition "da = \<lparr> dawTransition = daTransitionH,
                 dawInitState =daInitialState, dawInitOut =  (sbeGen.setter fout daInitialOut) \<rparr>"

definition "(daw::('state, 'in, 'out, 'c) dAutomaton_weak) = \<lparr> dawTransition = daTransitionH,
                 dawInitState =daInitialState, dawInitOut =  Abs_sbElem(None)\<rparr>"

lemma daut2sscanl:"dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(sscanlAsnd daTransition state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
proof(induction input)
  case adm
  then show ?case
    by simp
next
  case (least input)
  then show ?case
    apply(simp add: sbIsLeast_def)
    apply(cases "chIsEmpty TYPE('in)")
     apply auto defer
    apply(subst dawstatesem_bottom)
    sorry
next
  case (sbeCons sbe input)
  then show ?case 
    apply(subst sbeGen.gettersb_unfold,simp add: sbegenfin)
    sorry
qed

fun stateSemList::"'state \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"stateSemList _ [] = []" |
"stateSemList state (l#ls) = snd(daTransition state l) # stateSemList (fst (daTransition state l)) ls"

lemma "dawStateSem da state\<cdot>(sbeGen.setterList fin input) = sbeGen.setterList fout (stateSemList state input)"
  sorry
(* TODO: initiale ausgabe ... "sscanlA" kann nichts partielles ausgben.
  dh alles oder nichts. Das kann man durch den typ abfangen!
    * weak = "chIstEmpty" als assumption (oder besser, dafür eine klasse anlegen)
    * strong = gleicher typ wie ausgabe
*)

end

section \<open>automaton to smap equivalence locale\<close>

locale smapGen =
  fixes daTransition::"'state::countable \<Rightarrow> 'a::countable \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState::"'state"
  and   daInitialOut::"'b"    (* TODO, schwach kausal = keine initiale ausgabe! *)
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  and emptytype::"'c itself"
  and loopState::"'state"
  assumes scscanlgenf:"sscanlGen fin fout emptytype"
  and singlestate:"\<And>sbe. fst(daTransition loopState sbe) = loopState"
begin

(*Move to stream.thy. Is there already a lemma like this?*)
lemma sscanl2smap:
  assumes "\<And>e. fst(f s e) = s"
  and "g = (\<lambda>a. snd(f s a))"
shows"sscanlAsnd f s = smap g"
  apply(rule cfun_eqI)
  by(induct_tac x rule: ind,simp_all add: assms)

lemma daut2smap:"dawStateSem (sscanlGen.da daTransition daInitialState daInitialOut fin fout) loopState\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(smap (\<lambda>e. snd(daTransition loopState e))\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  apply(subst sscanlGen.daut2sscanl)
  using scscanlgenf sscanlGen.sbegenfin apply auto[1]
  apply(subst sscanl2smap[of daTransition loopState "(\<lambda>e. snd(daTransition loopState e))"])
  using singlestate by auto

end

sublocale  smapGen \<subseteq> sscanlGen
  by (simp add: scscanlgenf)


(*<*)
end
(*>*)