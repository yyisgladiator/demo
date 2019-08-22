(*<*)(*:maxLineLen=68:*)
theory dAutomaton_causal
  imports dAutomaton spf.SPF
begin

default_sort "chan"
(*>*)

subsection \<open>Deterministic Causal Automaton\<close> text\<open>\label{cauaut}\<close>

text\<open>Since the causality properties are an important factor for the
realizability of a component we introduce two automaton types that
work similar to our general deterministic automaton, but always have
a causal semantic. From the general causality theorems we can see
directly how to comply with their assumptions. First, we define the 
output of a transition function as a @{type sbElem}. This leads
directly the weakness of an automaton.\<close>

record ('state::type, 'in, 'out) dAutomaton_weak  =
  dawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>))"
  dawInitState :: "'state"

text\<open>The semantic of a weak automaton will never be strong, because
it has no initial output. But expanding it with an initial output in
from of a @{type sbElem} will directly fulfill necessary assumptions
for its strong semantic. Hence, we define the extension of the weak
automaton type as the strong automaton type.\<close>

record ('state::type,'in,'out)dAutomaton_strong = 
      "('state::type,'in,'out)dAutomaton_weak" + dasInitOut::"'out\<^sup>\<surd>"

text\<open>Records directly provide functions for arbitrary type 
extensions, we use them for the defined type extension from weak to
strong automatons.\<close>

definition daw2das::
"('state::type, 'in, 'out) dAutomaton_weak 
\<Rightarrow> 'out\<^sup>\<surd> \<Rightarrow> ('state::type, 'in, 'out) dAutomaton_strong"where
"daw2das daw initout\<equiv> dAutomaton_weak.extend daw 
                      (dAutomaton_strong.fields initout)"

text\<open>Furthermore, the next two functions convert our causal
automatons to equivalent general automatons\ref{sub:detaut}.\<close>

definition daw2da::"('state::type, 'in, 'out) dAutomaton_weak 
\<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da \<equiv> \<lambda>aut. 
(| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),
                           sbe2sb (snd(dawTransition aut s sbe)))),
   daInitState  = dawInitState(aut), 
   daInitOut    = \<bottom> |)"

text\<open>The only difference in those converters is the initial output.
It is the empty bundle for weak automatons.\<close>

definition das2da::"('state::type, 'in, 'out) dAutomaton_strong 
\<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"das2da \<equiv> \<lambda>aut. 
(| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),
                           sbe2sb (snd(dawTransition aut s sbe)))),
   daInitState  = dawInitState(aut), 
    daInitOut   = sbe2sb(dasInitOut aut) |)"

text\<open>The semantic mapping of our causal automatons use the 
converters to apply our general state semantic mapping 
@{const daStateSem} to our converted automatons.\<close>

definition dawStateSem::
"('s::type,'I::{chan,finite},'O) dAutomaton_weak 
\<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"dawStateSem da \<equiv> daStateSem (daw2da da)"

text\<open>Since our weak Automatons have no initial output, the complete
semantic mapping only maps the state semantic to the corresponding
\gls{spf} of the initial state. Alternatively we could also use
@{const daSem}\ref{subsub:sem} and our converter to accomplish the
same.\<close>

definition dawSem::
"('s::type, 'I::{chan,finite},'O) dAutomaton_weak 
\<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dawSem da \<equiv> dawStateSem da (dawInitState da)"

text\<open>Our strong semantic does exactly this.\<close>

definition dasSem::
"('s::type, 'I::{chan,finite},'O) dAutomaton_strong 
\<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dasSem da \<equiv> daSem(das2da da)"
(*<*)
subsubsection  \<open>Rum96 Automaton Semantic\<close>

function Rum_tap::"('s::type, 'in,'out) dAutomaton_weak 
\<Rightarrow> ('s \<Rightarrow> ('in,'out) spfw) set" where
"Rum_tap aut = 
{h | h. \<forall>m s. \<exists>t out . snd(dawTransition aut s m) = out \<and>
                       (\<exists>h2\<in> (Rum_tap aut). \<forall>i .
          Rep_spfw(h s)\<cdot>(m \<bullet>\<^sup>\<surd> i) = out \<bullet>\<^sup>\<surd> (Rep_spfw(h2 t))\<cdot>i)}"
  by(simp)+

fun Rum_ta::"('s::type, 'in,'out) dAutomaton_weak 
\<Rightarrow> (('in,'out) spfw) set"where
"Rum_ta aut = {g | g. \<exists>h\<in>(Rum_tap aut). \<exists> s (out::'out\<^sup>\<surd>). \<forall>i.
              (Rep_spfw g)\<cdot>i = out\<bullet>\<^sup>\<surd>((Rep_spfw(h s))\<cdot>i)}"

fun Rum_ta_strong::
"('s::type, 'in::{chan,finite},'out) dAutomaton_strong 
\<Rightarrow> (('in,'out) spfs) set"where
"Rum_ta_strong aut = Abs_spfs`Rum_ta (dAutomaton_weak.truncate aut)"

(*>*)
paragraph \<open>Causal Sem lemmas \\\<close>

text\<open>The causal automaton types work very similar to our general
automatons. Firstly, the semantic iteration terminates, if the input
\gls{sb} has not bundle element.\<close>

lemma dawstatesem_unfolding:
"dawStateSem automat s = sb_split\<cdot>(\<lambda>sbe. \<Lambda> sb .
           let (nextState, output) = dawTransition automat s sbe in
           output \<bullet>\<^sup>\<surd> ((dawStateSem automat) nextState\<cdot>sb))"
  apply(simp add: dawStateSem_def daw2da_def)
  apply(subst dastatesem_unfolding)
  by(simp add: sbECons_def prod.case_eq_if)

lemma dawNextOut:
  shows "sbe2sb (snd ((dawTransition automat) s sbe)) = 
         daNextOut (daw2da automat) s sbe"
  by (simp add: daNextOut_def daw2da_def)

lemma dawNextState:
  shows "fst (dawTransition automat s sbe) = 
         daNextState (daw2da automat) s sbe"
  by  (simp add: daNextState_def daw2da_def)

theorem dawstatesem_bottom:
  assumes "\<not>sbHdElemWell (sb::'b::{finite,chan}\<^sup>\<Omega>)"
  and "\<not> chDomEmpty TYPE('b)"
  shows "(dawStateSem automat s)\<cdot>sb = \<bottom>"
  by  (simp_all add: assms dawStateSem_def dastatesem_bottom)

lemma dawstatesem_strict:
  assumes "\<not> chDomEmpty TYPE('b::{finite, chan})"
  shows "(dawStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dawStateSem_def dastatesem_strict)

lemma dawstatesem_step:
  assumes "sbHdElemWell sb"
  shows "(dawStateSem da s)\<cdot>sb = 
  snd (dawTransition da s (sbHdElem sb)) \<bullet>\<^sup>\<surd> 
  dawStateSem da (fst (dawTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  by (simp_all add: dawStateSem_def sbECons_def assms 
      daNextState_def[symmetric] dawNextState[symmetric] 
      daNextOut_def[symmetric] dawNextOut dastatesem_step)

lemma dawstatesem_final:
  assumes "sbHdElemWell sb"
  shows "dawStateSem automat s\<cdot>sb = 
(let (nextState, output) = dawTransition automat s (sbHdElem sb) in
                  output \<bullet>\<^sup>\<surd> dawStateSem automat nextState\<cdot>(sbRt\<cdot>sb))"
  by (simp add: case_prod_unfold Let_def dawStateSem_def sbECons_def
      dawNextOut dawNextState dastatesem_final assms)


text\<open>Furthermore, process every input bundle element similar to the
general automatons, but produce exactly one bundle element as 
output for every input element.\<close>

theorem dawstatesem_final_h2:
  shows "(dawStateSem automat s)\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) =
          (let (nextState, output) = dawTransition automat s sbe in
                         output \<bullet>\<^sup>\<surd> dawStateSem automat nextState\<cdot>sb)"
  apply (simp add: case_prod_unfold Let_def dawStateSem_def)
  apply (subst (2) sbECons_def)
  by (simp add: dawNextOut dawNextState dastatesem_final_h2)

text\<open>Thus, the length of the output is equal to the length of the
input. This leads directly to the weakness of any weak automaton 
semantic.\<close>

lemma dawsem_len:
  fixes automat::"('s::type,'I::{chan,finite},'O)dAutomaton_weak"
  assumes "\<not>chDomEmpty TYPE('O)"  
  shows "sbLen (dawStateSem automat s\<cdot>sb) = sbLen sb"
proof (cases "chDomEmpty TYPE('I)")
  case True
  have "\<And>s sbe. sbLen (sbe2sb (snd ((dawTransition automat) s sbe))) = 1"
    by (simp add: assms)
  thus ?thesis
    by (metis (mono_tags, lifting) True dastatesem_inempty_len
        dawNextOut dawStateSem_def min.orderI min_def sblen_empty
        sbtypeepmpty_sbbot)
next
  case False
  have "\<And>s sbe. sbLen (sbe2sb (snd ((dawTransition automat) s sbe))) = 1"
    by (simp add: assms)
  hence nextout_len: "\<And>s sbe. sbLen (daNextOut (daw2da automat) s sbe) = 1"
    by (simp add: dawNextOut)
  have "sbLen sb < \<infinity> \<Longrightarrow> sbLen sb = sbLen (dawStateSem automat s\<cdot>sb)"
  proof-
    assume sb_len: "sbLen sb < \<infinity>"
    thus ?thesis
    proof (induction sb arbitrary: s rule: sb_finind)
      case 1
      then show ?case
        using sb_len by blast
    next
      case (2 sb)
      then show ?case
        by (metis False assms botsbleast dawstatesem_bottom lnzero_def sbleast2sblenempty)
    next
      case (3 sbe sb)
      then show ?case
        by (metis dawstatesem_step fold_inf inf_less_eq le_less_linear
            lnat.con_rews lnzero_def sbecons_len sbleast2sblenempty sbrt_sbecons)
    qed
  qed
  thus ?thesis
    by (metis dastatesem_weak dawStateSem_def inf_less_eq
        le_less_linear less_irrefl nextout_len weak_well_def)
qed

lemma dawstatesem_weak:
  shows  "weak_well (dawStateSem automat s)"
  apply (simp add: dawStateSem_def)
  apply (rule dastatesem_weak)
  apply (simp add: daw2da_def daNextOut_def)
  by (cases "chDomEmpty TYPE('b)",auto)

theorem dawsem_weak[simp]:
  fixes automat::"('s::type,'I::{chan,finite},'O)dAutomaton_weak"
  shows  "weak_well (dawSem automat)"
  apply (simp add: dawSem_def)
  by (simp add: dawstatesem_weak eta_cfun)
  
lemma dassem_insert:
"dasSem automat\<cdot>sb = dasInitOut automat \<bullet>\<^sup>\<surd> 
                     dawStateSem (dAutomaton_weak.truncate automat)
                     (dawInitState automat)\<cdot>sb"
  by (simp add:  dasSem_def dawSem_def dAutomaton_weak.defs 
      dAutomaton_strong.defs sbECons_def  dasem_insert das2da_def 
      dawStateSem_def daw2da_def daStateSem_def)

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

text\<open>Of course the strong automatons are then immediately strong,
since they have an additional initial output element.\<close>

lemma dassem_len:
  fixes automat::"('s::type,'I::{chan,finite},'O)dAutomaton_strong"
  assumes "\<not>chDomEmpty TYPE('O)"  
  shows  "sbLen (dasSem automat\<cdot>sb) = lnsuc\<cdot>(sbLen sb)"
  by (simp add: assms dassem_insert dawsem_len sbecons_len)

theorem dassem_strong:
shows "strong_well (dasSem automat)"
  apply (simp add: strong_well_def dassem_insert SB.sbecons_len)
  by (meson dawstatesem_weak weak_well_def)

paragraph \<open>Lifted semantic \\\<close>

text\<open>We can then provide lifted semantics for strong and weak
automatons. The lifted versions of @{const dawSem} and 
@{const dasSem} map to well formed causal \glspl{spf}.\<close>

lift_definition semantic_weak::
"('state::type,'in::{chan,finite},'out) dAutomaton_weak 
\<Rightarrow> ('in,'out)spfw" is "dawSem"
  by %visible simp

lift_definition semantic_strong::
"('s::type, 'in::{chan,finite}, 'out) dAutomaton_strong 
\<Rightarrow> ('in,'out)spfs"is "\<lambda>auts. Abs_spfw(dasSem auts)"
  by %visible (simp add: Abs_spfw_inverse dassem_strong strong2weak)

subsubsection \<open>Causal Automaton Locales\<close>

text\<open>The semantic mapping allows us to verify the behaviour of
components with \glspl{spf}. Since these components are modeled as 
automatons, we introduce two locals for constructing and
transforming automatons. These locals are used in the generation
process, where a MontiArc model provides the information about the
automatons components. Hence, they provide us with a state type,
message types, the transition function directly obtained from the
model and an initial state. Since the MontiArc model has no
\glspl{sb}, @{type sbElem}s or the @{type M}, the transition 
function also does not use any of these things. Instead it uses 
exactly the types from its model. But the message types do not have 
to be in type @{type M} to construct an automaton in Isabelle,
because our locals @{locale sbeGen} and @{locale sbGen} are also 
interpreted with constructors provided by the generator and we can
utilize them to define the automaton internally and independently.\<close>

locale sscanlGen =
  fixes daTransition::"'state::countable \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState::"'state"
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

text\<open>Using the setter, getter and MontiArc transition function we
define the corresponding transition function for our automaton by
applying the provided getter to its input @{type sbElem}, running
the MontiArc transition function and then using the setter to 
convert its output back to a @{type sbElem}. The state type is not
converted.\<close> 

definition daTransitionH::"'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>)" where
"daTransitionH state sbe = 
     (let (s,output) = daTransition state (sbeGen.getter fin sbe) in 
                       (s, sbeGen.setter fout output))"

text\<open>Then the deterministic automaton is defined with the initial
state and @{const daTransitionH}.\<close>

definition "da = \<lparr> dawTransition = daTransitionH,
                 dawInitState =daInitialState \<rparr>"

text\<open>Often components output behaviour depends on the input. These
components have a non-empty input and output domain and so does
their semantic. We can then represent their components behaviour by
reducing its semantic with the setter and getter to a 
@{const sscanlAsnd} mapping that uses the MontiArc transition
function and works completely over streams. This is an important 
part of the verification process because it is often easier to proof
properties directly for the streams of a bundle and not for the
bundle itself. If the input domain is empty, the components output 
is independent from the input.\<close>

theorem daut2sscanl: 
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows"sbeGen.getterSB fout \<cdot>
  (dawStateSem da state\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  
   sscanlAsnd daTransition state\<cdot>input"
using assms
proof(induction input arbitrary: state rule: ind)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    by (simp add: assms sbeGen.gettersb_realboteps 
        sbeGen.settersb_strict sbegenfin sbegenfout 
        dawstatesem_strict)
next
  case (3 a s)
  then show ?case                                                                      
    by (simp add: sbeGen.get_set dawstatesem_final_h2 sbegenfin 
        sbegenfout sbeGen.settersb_unfold prod.case_eq_if 
        sbeGen.gettersb_unfold da_def daTransitionH_def)
qed

lemma daut2sscanl2: 
  shows"(dawStateSem da state\<cdot>input) =  
   sbeGen.setterSB fout\<cdot>(sscanlAsnd daTransition state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  apply(induction input arbitrary: state)
    apply simp_all
  apply(cases "chDomEmpty TYPE('in)")
    apply (simp add: sbegenfin sbegenfout sbeGen.gettersb_empty_inf)
  defer
    apply (simp add: sbegenfin sbegenfout sbeGen.gettersb_boteps)
    apply (simp add: dawstatesem_bottom sbeGen.settersb_strict sbegenfout)
    apply (simp add: sbegenfin sbegenfout sbeGen.gettersb_unfold dawstatesem_final_h2)(* TODO: anstatt "case" ein lemma mit "fst"/"snd" anlegen *)
  apply (simp add: case_prod_beta daTransitionH_def da_def sbeGen.settersb_unfold sbegenfout) 
  oops

lemma emptychan_eq[simp]:
  "chDomEmpty TYPE('out) \<Longrightarrow> (sb1::'out\<^sup>\<Omega>) = sb2"
  by (metis (full_types)sbtypeepmpty_sbbot)

lemma daut2sscanl:
"(dawStateSem da state\<cdot>input) = sbeGen.setterSB fout\<cdot>
(sscanlAsnd daTransition state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  apply(cases "chDomEmpty(TYPE('out))",simp_all)
  apply(insert daut2sscanl[of state "sbeGen.getterSB fin\<cdot>input"])
  oops

fun %invisible stateSemList::"'state \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"stateSemList _ [] = []" |
"stateSemList state (l#ls) = snd(daTransition state l) # 
                      stateSemList (fst (daTransition state l)) ls"

lemma "dawStateSem da state\<cdot>(sbeGen.setterList fin input) = 
        sbeGen.setterList fout (stateSemList state input)"
  oops
(* TODO: initiale ausgabe ... "sscanlA" kann nichts partielles 
ausgben. dh alles oder nichts. Das kann man durch den typ abfangen!
    * weak = "chIstEmpty" als assumption (oder besser, dafür eine 
klasse anlegen)
    * strong = gleicher typ wie ausgabe
*)

end

text\<open>Some automatons contains a self looping state that will never 
be left again. If such an automaton reaches a self looping state on 
its run, its behaviour can be reduced to an easier transition
function. For such cases we provide a sub local of 
@{locale sscanlGen} which provides an additional behaviour 
translation.\<close>

locale smapGen =
  fixes daTransition::"'state::countable \<Rightarrow> 'a::countable \<Rightarrow> 
                      ('state\<times>'b::countable)"
  and   daInitialState::"'state"
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  and loopState::"'state"
  assumes scscanlgenf:"sscanlGen fin fout"
  and singlestate:"\<And>sbe. fst(daTransition loopState sbe)=loopState"
begin

text\<open>The looping state is used for defining a mapping \<open> 'a \<Rightarrow> 'b\<close>
from the MontiArc transition function.\<close>

abbreviation "smapTransition \<equiv> (\<lambda>e. snd(daTransition loopState e))" 

text\<open>Using this, we can reduce the semantic with setter and getter
to a @{const smap} mapping over streams from the moment its looping 
state is reached.\<close>

theorem daut2smap:
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows"sbeGen.getterSB fout\<cdot>(dawStateSem 
        (sscanlGen.da daTransition daInitialState fin fout) 
        loopState\<cdot>(sbeGen.setterSB fin \<cdot>input)) = 
        smap smapTransition\<cdot>input"
  apply(subst sscanlGen.daut2sscanl)
  using scscanlgenf sscanlGen.sbegenfin assms  apply auto[2]
  by (simp_all add: assms singlestate sscanl2smap)

text\<open>In case of a previous reduction to the @{const sscanlAsnd}
mapping an additional theorem is provided, that allows the further
reduction to @{const smap} if a looping state is reached at any
point.\<close>

theorem step2smap:
  assumes "\<not>chDomEmpty TYPE('out)"
  and     "\<not>chDomEmpty TYPE('in)"
  shows   "sscanlAsnd daTransition loopState\<cdot>input = 
           smap smapTransition\<cdot>input"
  using scscanlgenf sscanlGen.sbegenfin assms apply auto
  by (simp_all add: assms singlestate sscanl2smap)


end

text\<open>A @{locale smapGen} interpretation should also automatically 
provide all properties and definitions from the @{locale sscanlGen}
locale. This is done be instantiating @{locale smapGen} as a
sub locale of @{locale sscanlGen}.\<close>

sublocale smapGen \<subseteq> sscanlGen
  by %visible (simp add: scscanlgenf)


(*<*)
end
(*>*)