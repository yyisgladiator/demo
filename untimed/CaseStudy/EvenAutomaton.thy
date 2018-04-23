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

lemma c1bundle_ubgetch[simp]: "(createC1Bundle n) . c1 = \<up>(\<M>(A n))"
  by (metis c1bundle_dom createC1Bundle.rep_eq fun_upd_same insertI1 option.inject ubgetchE)

(*Stuff*)
lemma test[simp]:"ubConc (tsynbOneTick c1)\<cdot>sb  .  c1 = \<up>\<surd> \<bullet> (ubUp\<cdot>sb .c1)"
  apply (simp only: ubConc_def)
  apply (simp only:  Abs_cfun_inverse2 ubconc_cont)
  apply (simp add: ubgetch_ubrep_eq)
  by (simp add: usclConc_stream_def)

lemma test2[simp]: "ubConc (createC1Bundle n)\<cdot>sb  .  c1 = \<up>(\<M>(A n)) \<bullet> (ubUp\<cdot>sb. c1)"
  apply (simp only: ubConc_def)
  apply (simp only:  Abs_cfun_inverse2 ubconc_cont)
  apply (simp add: ubgetch_ubrep_eq)
  by (simp add: usclConc_stream_def)
     
lemma sbRt_ubConc_dom[simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "sbRt\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: sbRt_def assms) +
    
lemma sbRt_ubConc_dom2[simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "sbRt\<cdot>(ubConc (createC1Bundle n)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: sbRt_def assms) +
lemma convDiscrUp_inj: "inj convDiscrUp"
  proof (rule injI)
    fix x::"channel \<Rightarrow> 'b option" and y::"channel \<Rightarrow> 'b option"
    assume a1: "convDiscrUp x = convDiscrUp y"
    have f1: "dom x = dom y"
      by (metis a1 convDiscrUp_dom_eq)
    have f2: "\<forall> xa \<in> dom x. (Iup (Discr (x \<rightharpoonup> xa))) = (Iup (Discr (y \<rightharpoonup> xa)))"
      by (metis (full_types) a1 convDiscrUp_def convDiscrUp_dom_eq option.sel)
    show "x = y"     
      apply (subst fun_eq_iff)
      apply rule
      apply (case_tac "xa \<in> dom x") defer
       apply (metis a1 convDiscrUp_dom_eq domIff)
      by (metis discr.inject domD f1 f2 option.sel u.inject)
  qed
lemma [simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "(inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))) = [c1 \<mapsto> \<surd>]"
proof -
  obtain my_p where my_p_def: "my_p = (\<lambda> x::channel \<Rightarrow> 'a event option. (\<lambda>c::channel. (c \<in> dom x)\<leadsto>Iup (Discr x\<rightharpoonup>c)) = sbHdElem\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))"
    by simp
  have f1: "(\<exists> x::channel \<Rightarrow> 'a event option. (\<lambda>c::channel. (c \<in> dom x)\<leadsto>Iup (Discr x\<rightharpoonup>c)) = sbHdElem\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))"
    apply (rule_tac x="[c1 \<mapsto> \<surd>]" in exI)
    apply (subst fun_eq_iff)
    apply rule +
    apply (case_tac "x \<in> dom [c1 \<mapsto> \<surd>]")
     apply simp
    unfolding sbHdElem_def
    apply (simp add: sbHdElem_cont)
    unfolding up_def
     apply simp
    by (simp add: sbHdElem_cont assms)
  have f3: "convDiscrUp (inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))) = 
            convDiscrUp  [c1 \<mapsto> \<surd>]"
    apply (subst convdiscrup_inv_eq)
     apply (metis assms lscons_conv sbHdElem_channel sbHdElem_dom sbRt_ubConc_dom 
        sbrt_sbdom singletonD stream.con_rews(2) test up_defined)
    apply (subst fun_eq_iff)
    apply rule
    apply (case_tac "x = c1")
    unfolding sbHdElem_def
    apply (simp_all add: sbHdElem_cont assms)
    unfolding convDiscrUp_def
     apply simp
     apply (simp add: up_def)
    by simp
  show ?thesis
    by (metis convDiscrUp_inj f3 inv_f_f)
qed
    
lemma [simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "(inv convDiscrUp (sbHdElem\<cdot>(ubConc (createC1Bundle n)\<cdot>sb))) = [c1 \<mapsto> \<M>(A n)]"
proof -
  have f3: "convDiscrUp (inv convDiscrUp (sbHdElem\<cdot>(ubConc (createC1Bundle n)\<cdot>sb))) = 
            convDiscrUp [c1 \<mapsto> \<M>(A n)]"
    apply (subst convdiscrup_inv_eq)
    apply (simp add: assms sbHdElem_channel)
    apply (subst fun_eq_iff)
    apply rule
    apply (case_tac "x = c1")
    unfolding sbHdElem_def
    apply (simp_all add: sbHdElem_cont assms)
    unfolding convDiscrUp_def
     apply simp
     apply (simp add: up_def)
    by simp
  show ?thesis
    by (metis convDiscrUp_inj f3 inv_f_f)
qed

lemma [simp]:"ubDom\<cdot>(createC2Output True) = {c2}"
  by(simp add: ubDom_def createC2Output.rep_eq)
    
(*Transition*)
lemma evenTraTick[simp]:"evenAutomatonTransition (state, [c1 \<mapsto> \<surd>]) = (state,(tsynbOneTick c2) )"
  sorry  
        
lemma tran_sum_even[simp]: assumes "Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M> A m]) = (State Even (summe + m), createC2Output True)"
  sorry
    
lemma tran_sum_odd[simp]: assumes "\<not>Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M> A m]) = (State Odd (summe + m), createC2Output False)"
  sorry   
    
(*step lemmata*)
lemma evenaut_h_even_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (tsynbOneTick c1)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Even summe) \<rightleftharpoons> sb)"
  by(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def)


lemma evenaut_h_odd_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (tsynbOneTick c1)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Odd summe) \<rightleftharpoons> sb)"
  by(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def)

lemma evenaut_h_even_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton  (State Even (n+summe)) \<rightleftharpoons> sb)"
  by(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def add.commute even_iff_mod_2_eq_zero)


lemma evenaut_h_odd_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton (State Even (n+summe)) \<rightleftharpoons> sb)"
  by(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def add.commute even_iff_mod_2_eq_zero)




lemma evenaut_H_step: assumes "ubDom\<cdot>sb={c1}"
  shows "H EvenAutomatonAutomaton \<rightleftharpoons> sb =  ubConc (tsynbOneTick c2)\<cdot>(h EvenAutomatonAutomaton (State Even 0) \<rightleftharpoons> sb)"
  unfolding H_def
  by(simp add: h_out_dom getRan_def getInitialState_def getInitialOutput_def EvenAutomatonAutomaton.rep_eq getDom_def assms)

end