(*<*)(*:maxLineLen=68:*)
theory dAutomaton_causal
  imports dAutomaton spf.SPF
begin

default_sort "chan"
(*>*)

section \<open>Deterministic Weak Automata\<close>

record ('state::type, 'in, 'out) dAutomaton_weak  =
  dawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>))"
  dawInitState :: "'state"

record ('state::type,'in,'out)dAutomaton_strong = "('state::type, 'in, 'out) dAutomaton_weak" 
                                                  + dasInitOut:: "'out\<^sup>\<surd>"

definition daw2das::"('state::type, 'in, 'out) dAutomaton_weak \<Rightarrow> 'out\<^sup>\<surd> \<Rightarrow> ('state::type, 'in, 'out) dAutomaton_strong"where
"daw2das daw initout\<equiv> (dAutomaton_weak.extend daw (dAutomaton_strong.fields initout))"

definition daw2da::"('state::type, 'in, 'out) dAutomaton_weak \<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da \<equiv> \<lambda>aut. (| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),sbe2sb (snd(dawTransition aut s sbe)))),
                 daInitState = dawInitState(aut), daInitOut = \<bottom> |)"

definition das2da::"('state::type, 'in, 'out) dAutomaton_strong \<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"das2da \<equiv> \<lambda>aut. (| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),sbe2sb (snd(dawTransition aut s sbe)))),
                 daInitState = dawInitState(aut), daInitOut = sbe2sb(dasInitOut aut) |)"

subsection \<open>Weak Automaton Semantic options\<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_weak::"('state::type, 'in::{chan,finite}, 'out) dAutomaton_weak \<Rightarrow> ('in,'out)spfw"where
"semantik_weak autw = Abs_spfw(daSem(daw2da autw))"


definition dawStateSem :: "('s::type, 'I::{chan,finite},'O) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"dawStateSem da = daStateSem (daw2da da)"

definition dawSem :: "('s::type, 'I::{chan,finite},'O) dAutomaton_weak \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dawSem da = (\<Lambda> sb. ((dawStateSem da (dawInitState da))\<cdot>sb))"


subsubsection \<open>Rum96 Automaton Semantic\<close>

function Rum_tap::"('s::type, 'in,'out) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('in,'out) spfw) set" where
"Rum_tap aut = {h | h. \<forall>m s. \<exists>t out . ((snd(dawTransition aut s m)) = out) \<and>
                    (\<exists>h2\<in> (Rum_tap aut). \<forall>i .
          (Rep_spfw(h s))\<cdot>(m \<bullet>\<^sup>\<surd> i) = out \<bullet>\<^sup>\<surd> ((Rep_spfw(h2 t))\<cdot>i))}"
  by(simp)+

(*Termination for Rum_tap necessary?*)

fun Rum_ta::"('s::type, 'in,'out) dAutomaton_weak \<Rightarrow> (('in,'out) spfw) set"where
"Rum_ta aut = {g | g. \<exists>h\<in>(Rum_tap aut). \<exists> s (out::'out\<^sup>\<surd>). \<forall>i.
              (Rep_spfw g)\<cdot>i = out\<bullet>\<^sup>\<surd>((Rep_spfw(h s))\<cdot>i)}"

section \<open>Deterministic strong Automaton\<close>

subsection \<open>Strong Automaton Semantic options \<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_strong::"('s::type, 'in::{chan,finite}, 'out) dAutomaton_strong \<Rightarrow> ('in,'out)spfs"where
"semantik_strong auts = Abs_spfs(semantik_weak (dAutomaton_weak.truncate auts))"


definition dasSem :: "('s::type, 'I::{chan,finite},'O) dAutomaton_strong \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dasSem da = daSem(das2da da)"


subsection \<open>Rum96 Automaton Semantic \<close>

fun Rum_ta_strong::"('s::type, 'in::{chan,finite},'out) dAutomaton_strong \<Rightarrow> (('in,'out) spfs) set"where
"Rum_ta_strong aut = Abs_spfs `(Rum_ta (dAutomaton_weak.truncate aut))"


subsection \<open>*Causal Sem lemmas \<close>

lemma dawstatesem_unfolding: "(dawStateSem automat s) = sb_split\<cdot>(\<lambda>sbe. \<Lambda> sb .
                                                  let (nextState, output) = dawTransition automat s sbe in
                            output \<bullet>\<^sup>\<surd> ((dawStateSem automat) nextState\<cdot>sb))"
  by(simp add: dawStateSem_def daw2da_def,subst dastatesem_unfolding,simp add: sbECons_def prod.case_eq_if)

lemma dawNextOut:
  shows "sbe2sb (snd ((dawTransition automat) s (sbe))) = daNextOut (daw2da automat) s (sbe)"
  by (simp add: daNextOut_def daw2da_def)

lemma dawNextState:
  shows "(fst (dawTransition automat s (sbe))) = daNextState (daw2da automat) s (sbe)"
  by  (simp add: daNextState_def daw2da_def)

lemma dawstatesem_bottom:
  assumes "\<not>sbHdElemWell (sb::('b::{finite,chan})\<^sup>\<Omega>)"
  and "\<not> chDomEmpty TYPE('b)"
  shows "(dawStateSem automat s)\<cdot>sb = \<bottom>"
  by  (simp_all add: assms dawStateSem_def dastatesem_bottom)

lemma dawstatesem_strict:
  assumes "\<not> chDomEmpty TYPE('b::{finite, chan})"
  shows "(dawStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dawStateSem_def dastatesem_strict)

lemma dawstatesem_step:
  assumes "sbHdElemWell sb"
  shows "(dawStateSem da s)\<cdot>sb = snd (dawTransition da s (sbHdElem sb)) \<bullet>\<^sup>\<surd> dawStateSem da (fst (dawTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  by (simp_all add: dawStateSem_def sbECons_def assms daNextState_def[symmetric] dawNextState[symmetric] daNextOut_def[symmetric] dawNextOut dastatesem_step)

lemma dawstatesem_final:
  assumes "sbHdElemWell sb"
  shows "(dawStateSem automat s)\<cdot>sb = (let (nextState, output) = dawTransition automat s (sbHdElem sb) in
  output \<bullet>\<^sup>\<surd> dawStateSem automat nextState\<cdot>(sbRt\<cdot>sb))"
  by (simp add: case_prod_unfold Let_def dawStateSem_def sbECons_def dawNextOut dawNextState dastatesem_final assms)

lemma dawstatesem_final_h2:
  shows "(dawStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =(let (nextState, output) = dawTransition automat s sbe in
                            output \<bullet>\<^sup>\<surd> dawStateSem automat nextState\<cdot>sb)"
  apply (simp add: case_prod_unfold Let_def dawStateSem_def)
  apply (subst (2) sbECons_def)
  by (simp add: dawNextOut dawNextState dastatesem_final_h2)

lemma dawstatesem_weak:
  fixes automat::"('s,'I::{chan,finite},'O)dAutomaton_weak"
  shows  "weak_well (dawStateSem automat s)"
  apply (simp add: dawStateSem_def)
  apply (rule dastatesem_weak)
  apply (simp add: daw2da_def daNextOut_def)
  by (cases "chDomEmpty TYPE('O)",auto)
  
lemma dassem_insert:
  "dasSem automat\<cdot>sb = (dasInitOut automat) \<bullet>\<^sup>\<surd> ((dawStateSem (dAutomaton_weak.truncate automat) (dawInitState automat))\<cdot>sb)"
  by (simp add:  dasSem_def dawSem_def dAutomaton_weak.defs dAutomaton_strong.defs sbECons_def  dasem_insert das2da_def dawStateSem_def daw2da_def daStateSem_def)

lemma dasinitout_well:"(dasInitOut
         (dAutomaton_weak.extend daw
           (dAutomaton_strong.fields
             sbe))) = sbe"
  by(simp add: dAutomaton_weak.defs dAutomaton_strong.defs)

lemma das2daw_trunc_well:"dAutomaton_weak.truncate
                (dAutomaton_weak.extend da
                  (dAutomaton_strong.fields sbe)) = da" 
  by(simp add: dAutomaton_weak.defs dAutomaton_strong.defs)

lemma dassem_bottom:
  assumes "\<not> chDomEmpty TYPE('b::{finite,chan})"
  shows "dasSem automat\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = sbe2sb (dasInitOut automat)"
  by (simp add: dasSem_def dasem_bottom assms das2da_def)

lemma dassem_strong:
fixes sautomat::"('s,'I::{chan,finite},'O)dAutomaton_strong"
shows "strong_well (dasSem sautomat)"
  apply (simp add: strong_well_def dassem_insert SB.sbecons_len)
  using dawstatesem_weak weak_well_def by blast

section \<open>automaton to sscanl equivalence locale\<close>

locale sscanlGen =
  fixes daTransition::"'state::countable \<Rightarrow> 'a::countable \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState::"'state"
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

definition daTransitionH::"'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>)" where
"daTransitionH state sbe = (let (s,output) = daTransition state (sbeGen.getter fin sbe) in 
  (s, sbeGen.setter fout output))"

definition "da = \<lparr> dawTransition = daTransitionH,
                 dawInitState =daInitialState \<rparr>"

lemma daut2sscanl: 
  assumes "\<not>chDomEmpty(TYPE('out))"
  and "\<not>chDomEmpty(TYPE('in))"
  shows"sbeGen.getterSB fout \<cdot>(dawStateSem da state\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  sscanlAsnd daTransition state\<cdot>input"
using assms
proof(induction input arbitrary: state rule: ind)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    by (simp add: assms sbeGen.gettersb_realboteps sbeGen.settersb_strict sbegenfin sbegenfout dawstatesem_strict)
next
  case (3 a s)
  then show ?case                                                                      
    by (simp add: sbeGen.get_set dawstatesem_final_h2 sbegenfin sbegenfout 
         sbeGen.settersb_unfold prod.case_eq_if sbeGen.gettersb_unfold da_def daTransitionH_def)
qed

lemma emptychan_eq[simp]:"chDomEmpty TYPE('out) \<Longrightarrow> (sb1::'out\<^sup>\<Omega>) = sb2"
  by (metis (full_types)sbtypeepmpty_sbbot)

lemma daut2sscanl:"(dawStateSem da state\<cdot>input) =
                   sbeGen.setterSB fout\<cdot>(sscanlAsnd daTransition state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  apply(cases "chDomEmpty(TYPE('out))",simp_all)
  apply(insert daut2sscanl[of state "sbeGen.getterSB fin\<cdot>input"],auto)
  oops

fun stateSemList::"'state \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"stateSemList _ [] = []" |
"stateSemList state (l#ls) = snd(daTransition state l) # stateSemList (fst (daTransition state l)) ls"

lemma "dawStateSem da state\<cdot>(sbeGen.setterList fin input) = sbeGen.setterList fout (stateSemList state input)"
  oops
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
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  and loopState::"'state"
  assumes scscanlgenf:"sscanlGen fin fout"
  and singlestate:"\<And>sbe. fst(daTransition loopState sbe) = loopState"
begin

abbreviation "smapTransition \<equiv> (\<lambda>e. snd(daTransition loopState e))" 

lemma daut2smap:
  assumes "\<not>chDomEmpty(TYPE('out))"
  and "\<not>chDomEmpty(TYPE('in))"
  shows"sbeGen.getterSB fout\<cdot>(dawStateSem (sscanlGen.da daTransition daInitialState fin fout) loopState\<cdot>(sbeGen.setterSB fin \<cdot>input)) = 
       smap smapTransition\<cdot>input"
  apply(subst sscanlGen.daut2sscanl)
  using scscanlgenf sscanlGen.sbegenfin assms  apply auto[2]
  by (simp_all add: assms singlestate sscanl2smap)

end

sublocale  smapGen \<subseteq> sscanlGen
  by (simp add: scscanlgenf)


(*<*)
end
(*>*)