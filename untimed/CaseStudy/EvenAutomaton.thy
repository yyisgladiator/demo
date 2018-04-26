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

lemma createc2output_dom: "ubDom\<cdot>(createC2Output b) = {c2}"
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

lemma ubElemWellI: assumes "ubElemWell f" and "c \<in> dom f"
  shows "(f \<rightharpoonup> c) \<in> ctype c"
  using assms(1) assms(2) ubElemWell_def by auto

lemma ubElemWellI2: assumes "ubElemWell f" and "c \<in> dom f"
and "(f \<rightharpoonup> c) = a"
shows "a \<in> ctype c"
  using assms(1) assms(2) assms(3) ubElemWellI by auto


lemma EvenAutomatonAutomaton_h: "\<And>s f. dom f = {c1} \<and> ubElemWell f 
          \<Longrightarrow> ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
proof -
  fix s::EvenAutomatonState and f::"channel \<rightharpoonup> EvenAutomaton event"
  assume a1: "dom f = {c1} \<and> ubElemWell f"
  obtain a where f_def: "f = [c1 \<mapsto> a]"
    using a1 dom_eq_singleton_conv by force
  have f1: "f\<rightharpoonup>c1 \<noteq> \<surd> \<Longrightarrow> (\<exists> b. f\<rightharpoonup>c1 = Msg b)"
    using event.exhaust by auto
  have f2: "f\<rightharpoonup>c1 \<noteq> \<surd> \<Longrightarrow> ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
  proof - 
    assume a2: "f \<rightharpoonup> c1 \<noteq> \<surd>"
    obtain b where b_def: "Msg b = f \<rightharpoonup> c1"
      using a2 f1 by auto
    have f0: "ctype c1 = {Tick} \<union> (Msg ` (ctype c1))"
      by (simp add: ctype_event_def)
    have "Msg b \<in> ctype c1"
      by (simp add: a1 b_def ubElemWellI)
    then have "Msg b \<in> (Msg ` (ctype c1))"
      by (simp add: a2 f0)
    hence "Msg b \<in> (Msg ` (range A))"
      by simp
    hence "b \<in> range A"
      by blast
    hence "\<exists> n. f = [c1 \<mapsto> Msg (A n)]"
      using b_def f_def by auto
    then obtain my_n where my_n_def: "f = [c1 \<mapsto> Msg (A my_n)]"
      by blast
    show "ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
      apply (simp add: my_n_def)
      apply (cases s)
      apply (case_tac x1)
      by (simp_all add: createc2output_dom)
  qed
  show "ubDom\<cdot>(snd (evenAutomatonTransition (s, f))) = {c2}"
    apply (cases "(f\<rightharpoonup>c1) = Tick")
     apply (metis (full_types) EvenAutomaton.getSubState.cases EvenAutomatonSubstate.exhaust 
        evenAutomatonTransition.simps(2) evenAutomatonTransition.simps(4) 
        f_def fun_upd_same option.sel snd_conv tsynbonetick_dom)
    by (simp add: f2)
qed

lift_definition EvenAutomatonAutomaton :: "(EvenAutomatonState, EvenAutomaton event) automaton" is 
  "(evenAutomatonTransition, State Even 0,(tsynbOneTick c2), {c1}, {c2})"
  by (simp add: EvenAutomatonAutomaton_h)

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

end