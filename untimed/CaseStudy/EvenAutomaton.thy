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
  sorry
  
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

lemma c1bundle_dom [simp]: "ubDom\<cdot>(createC1Bundle n) = {c1}"
  by (simp add: ubdom_insert createC1Bundle.rep_eq)



lemma evenaut_h_even_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (tsynbOneTick c2)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Even summe) \<rightleftharpoons> sb)"
  oops

lemma evenaut_h_odd_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (tsynbOneTick c2)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Odd summe) \<rightleftharpoons> sb)"
  oops

lemma evenaut_h_even_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton  (State Even (n+summe)) \<rightleftharpoons> sb)"
  oops

lemma evenaut_h_odd_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton (State Even (n+summe)) \<rightleftharpoons> sb)"
  oops



lemma evenaut_H_step: assumes "ubDom\<cdot>sb={c1}"
  shows "H EvenAutomatonAutomaton \<rightleftharpoons> sb =  ubConc (tsynbOneTick c2)\<cdot>(h EvenAutomatonAutomaton (State Even 0) \<rightleftharpoons> sb)"
  oops


end