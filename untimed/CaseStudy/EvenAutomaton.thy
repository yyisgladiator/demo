theory EvenAutomaton

imports Automaton

begin


(* BEGIN: tsynBundle *)
  (* Copied here, because importing leads to an ML-Error *)
  (* TODO: import it ! ! ! *)
lift_definition tsynbOneTick:: "channel \<Rightarrow> 'm::message event SB" is
"\<lambda>c. [c \<mapsto> \<up>Tick]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_event_def
  by simp

lemma tsynbonetick_dom [simp]: "ubDom\<cdot>(tsynbOneTick c) = {c}"
  by (simp add: tsynbOneTick.rep_eq ubdom_insert)

(* END: tsynBundle *)



(* This are the actual states from MAA *)
datatype EvenAutomatonSubstate = Even | Odd

(* And these have also the variables *)
datatype EvenAutomatonState = State EvenAutomatonSubstate nat

fun getSubState :: "EvenAutomatonState \<Rightarrow> EvenAutomatonSubstate" where
"getSubState (State automaton_s automaton_sum) = automaton_s"

fun getSum :: "EvenAutomatonState \<Rightarrow> nat" where
"getSum (State automaton_s automaton_sum) = automaton_sum"


datatype EvenAutomaton = A  nat | B  bool
instance EvenAutomaton :: countable
apply(intro_classes)
by(countable_datatype)


instantiation EvenAutomaton :: message
begin
    fun ctype_EvenAutomaton :: "channel \<Rightarrow> EvenAutomaton set" where
        "ctype_EvenAutomaton c1 = range A" | 
        "ctype_EvenAutomaton c2 = range B" 
instance
by(intro_classes)
end

lift_definition createC2Output :: "bool \<Rightarrow> EvenAutomaton event SB" is
  "\<lambda>b. [ c2 \<mapsto> \<up>(Msg (B b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
by simp


(* tsynbOneTick is defined in: timesyn/tsynBundle *)
function evenAutomatonTransition :: "(EvenAutomatonState \<times> (channel \<rightharpoonup> EvenAutomaton event)) \<Rightarrow> (EvenAutomatonState \<times> EvenAutomaton event SB)" where
  "evenAutomatonTransition (State Even automaton_sum, [c1 \<mapsto> Msg a]) = (case a of A b
      \<Rightarrow> 
  (
    if((b+automaton_sum) mod 2 = 1) then ((State Odd (b+automaton_sum),(createC2Output False)))
    else if((b+automaton_sum) mod 2 = 0) then ((State Even (b+automaton_sum),(createC2Output True)))
    else undefined
  )
  | _ \<Rightarrow> undefined)" |

 "evenAutomatonTransition (State Even automaton_sum, [c1 \<mapsto> Tick]) = (State Even (automaton_sum), (tsynbOneTick c2))"  |

 "evenAutomatonTransition (State Odd automaton_sum, [c1 \<mapsto> Msg a]) = (case a of A b
      \<Rightarrow> 
  (
    if((b+automaton_sum) mod 2 = 1) then ((State Even (b+automaton_sum),(createC2Output True)))
    else if((b+automaton_sum) mod 2 = 0) then ((State Odd (b+automaton_sum),(createC2Output False)))
    else undefined
  )
  | _ \<Rightarrow> undefined)" |

 "evenAutomatonTransition (State Odd automaton_sum, [c1 \<mapsto> Tick]) = (State Odd (automaton_sum), (tsynbOneTick c2))"  |

"dom f\<noteq> {c1} \<Longrightarrow>  evenAutomatonTransition (_,f) = undefined"

apply auto
apply (smt EvenAutomatonSubstate.exhaust dom_eq_singleton_conv event.exhaust getSubState.cases)
using fun_upd_eqD apply fastforce
using map_upd_eqD1 apply force
apply (meson option.distinct(1))
apply (metis option.simps(3))
using map_upd_eqD1 apply fastforce
apply (meson event.distinct(1) map_upd_eqD1)
apply (meson option.distinct(1))
by (metis option.simps(3))

lift_definition EvenAutomatonAutomaton :: "(EvenAutomatonState, EvenAutomaton event) automaton" is 
  "(evenAutomatonTransition, State Even 0,(tsynbOneTick c2), {c1}, {c2})"
  apply(rule automaton_wellI,simp)
proof-
  fix s::EvenAutomatonState
  fix f::"channel \<Rightarrow> EvenAutomaton event option"
  show "dom f = {c1} \<Longrightarrow> ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
    apply(subst evenAutomatonTransition.pinduct, simp_all)
    sorry
qed
  
definition EvenAutomatonSPF :: "EvenAutomaton event SPF" where
"EvenAutomatonSPF = H EvenAutomatonAutomaton"

lemma evenStreamBundle_well[simp]:assumes "sdom\<cdot>s \<subseteq> ctype c" shows "ubWell ([c \<mapsto> s::EvenAutomaton event stream])"
by(simp add: ubWell_def usclOkay_stream_def assms)


definition EvenStream::"EvenAutomatonState \<Rightarrow> EvenAutomaton event stream \<rightarrow> EvenAutomaton event stream" where
"EvenStream state \<equiv> (\<Lambda> s. ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> s])) . c2)"

fun evenMakeSubstate :: "bool \<Rightarrow> EvenAutomatonSubstate" where
"evenMakeSubstate True = Even" | 
"evenMakeSubstate False = Odd"

lemma evenStream_insert:"EvenStream state\<cdot>s = ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> s])) . c2"
  apply(simp add: EvenStream_def,rule beta_cfun)
proof(rule Cont.contI2)
  show"monofun (\<lambda>x::EvenAutomaton event stream. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> x])  .  c2)"
   apply(rule monofunI)
    sorry
next
  fix Y:: "nat \<Rightarrow>EvenAutomaton event stream"
  assume a1: "chain Y"
  assume a2:"chain (\<lambda>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> Y i])  .  c2)"
  have "\<And>i. sdom\<cdot>(Y i) \<subseteq> ctype c1"
    sorry
  have h1:"(Abs_ubundle [c1 \<mapsto> \<Squnion>i. Y i]) = (\<Squnion>i. Abs_ubundle [c1 \<mapsto>  Y i])"
    sorry
  have h2:"chain (\<lambda>i::nat. Abs_ubundle [c1 \<mapsto> Y i])"
    sorry
  show "(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> \<Squnion>i::nat. Y i])  .  c2 \<sqsubseteq> 
          (\<Squnion>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> Y i])  .  c2)"
    apply(simp add: h1, subst contlub_cfun_arg, simp add: h2)
    sorry
qed
  

lemma  msg_assms: "EvenStream (State ooo summe)\<cdot>(\<up>(Msg (A m)) \<bullet> xs)
                 = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (EvenStream (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
  sorry
(*  proof(induction arbitrary: ooo summe rule: tsyn_ind [of _xs])
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case sorry
  next
    case (3 a s)
    then show ?case sorry
  next
    case (4 s)
    then show ?case sorry
  qed*)

lemma tick_assms: "EvenStream state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (f state\<cdot>xs)"
  sorry
(*proof(induction rule: tsyn_ind [of _xs])
  case 1
  then show ?case by simp
next
  case 2
  then show ?case sorry
next
  case (3 a s)
  then show ?case sorry
next
  case (4 s)
  then show ?case sorry
qed*)
      
lemma bot_assms: "EvenStream state\<cdot>\<bottom> = \<bottom>"
  apply(simp add: evenStream_insert)
  apply(subst h_bottom, simp add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def)
  apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
  apply(subst ubgetch_ubrep_eq, auto)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq ubclLeast_ubundle_def)
    
end