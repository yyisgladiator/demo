theory EvenAutomaton

imports Automaton "../../timesyn/tsynStream" "../../timesyn/tsynBundle"

begin


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

lemma createc2output_dom[simp]: "ubDom\<cdot>(createC2Output b) = {c2}" (*Can be generated*)
  by (simp add: ubdom_insert createC2Output.rep_eq)


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
    if((b+automaton_sum) mod 2 = 1) then ((State Odd (b+automaton_sum),(createC2Output False)))
    else if((b+automaton_sum) mod 2 = 0) then ((State Even (b+automaton_sum),(createC2Output True)))
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
termination by lexicographic_order
 
(*Transition can be generated*)
lemma evenTraTick[simp]:"evenAutomatonTransition (state, [c1 \<mapsto> \<surd>]) = (state,(tsynbOneTick c2) )"
  by (metis (full_types) EvenAutomatonState.exhaust EvenAutomatonSubstate.exhaust evenAutomatonTransition.simps(2) evenAutomatonTransition.simps(4))
        
lemma tran_sum_even[simp]: assumes "Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M>(A m)]) = (State Even (summe + m), createC2Output True)"
  apply (cases ooo)
   apply auto
  using assms by presburger  +

    
lemma tran_sum_odd[simp]: assumes "\<not>Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M>(A m)]) = (State Odd (summe + m), createC2Output False)"
  apply (cases ooo)
   apply auto
  using assms by presburger  +    

lemma EvenAutomatonAutomaton_h: "\<And>s f. dom f = {c1} \<and> ubElemWell f  (*Can not be generated right now*)
          \<Longrightarrow> ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
proof -
  fix s::EvenAutomatonState and f::"channel \<rightharpoonup> EvenAutomaton event"
  assume a1: "dom f = {c1} \<and> ubElemWell f"
  obtain a where f_def: "f = [c1 \<mapsto> a]"
    using a1 dom_eq_singleton_conv by force
  have f1: "f\<rightharpoonup>c1 \<noteq> \<surd> \<Longrightarrow> (\<exists> b. f\<rightharpoonup>c1 = Msg b)"
    using event.exhaust by auto
  have f2: "f\<rightharpoonup>c1 \<noteq> \<surd> \<Longrightarrow> ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}" (*f2 is a problem for sledgehammer*)
  proof - 
    assume a2: "f \<rightharpoonup> c1 \<noteq> \<surd>"
    obtain b where b_def: "Msg b = f \<rightharpoonup> c1"
      using a2 f1 by auto
    hence "b \<in> ctype c1"
      apply (subst ctype_event_iff)
      by (simp add: a1 ubElemWellI)
    hence "\<exists> n. f = [c1 \<mapsto> Msg (A n)]"
      using b_def f_def by auto
    then obtain my_n where my_n_def: "f = [c1 \<mapsto> Msg (A my_n)]"
      by blast
    show "ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
      by (metis EvenAutomaton.getSubState.cases createc2output_dom my_n_def snd_conv tran_sum_even tran_sum_odd)
  qed
  show "ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
    using f2 f_def by fastforce
qed
  
  
lift_definition EvenAutomatonAutomaton :: "(EvenAutomatonState, EvenAutomaton event) automaton" is 
  "(evenAutomatonTransition, State Even 0,(tsynbOneTick c2), {c1}, {c2})"
  by (simp add: EvenAutomatonAutomaton_h) (*Can not be generated right now (see lemma EvenAutomatonAutomaton_h)*)

definition EvenAutomatonSPF :: "EvenAutomaton event SPF" where
"EvenAutomatonSPF = H EvenAutomatonAutomaton"






(* It does not matter if it is input or output, the functions should be general *)
(* see: createC2Output *)
lift_definition createC1Bundle :: "nat \<Rightarrow> EvenAutomaton event SB" is
  "\<lambda>n. [ c1 \<mapsto> \<up>(Msg (A n))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
by simp

lemma createC1output_dom[simp]: "ubDom\<cdot>(createC1Bundle b) = {c1}"  (*Can be generated*)
  by (simp add: ubdom_insert createC1Bundle.rep_eq)  

end