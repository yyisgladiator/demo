theory EvenAutomaton

imports dAutomaton "../../timesyn/tsynBundle" 

begin

(* This are the actual states from MAA *)
datatype EvenAutomatonSubstate = Odd | Even

(* And these have also the variables *)
datatype EvenAutomatonState = State EvenAutomatonSubstate "nat"

fun getSubState :: "EvenAutomatonState \<Rightarrow> EvenAutomatonSubstate" where
    "getSubState (State state_s automaton_sum) = state_s"

fun getSum :: "EvenAutomatonState \<Rightarrow> nat" where
"getSum (State _ automaton_sum) = automaton_sum"
    

datatype EvenAutomaton = A "nat" | B "bool"
instance EvenAutomaton :: countable
apply(intro_classes)
by(countable_datatype)

abbreviation input_c1_c1 :: "channel" ("\<guillemotright>c1") where
"\<guillemotright>c1 \<equiv> c1"

abbreviation output_c2_c2 :: "channel" ("c2\<guillemotright>") where
"c2\<guillemotright> \<equiv> c2"

instantiation EvenAutomaton :: message
begin
fun ctype_EvenAutomaton :: "channel  \<Rightarrow> EvenAutomaton set" where
    "ctype_EvenAutomaton \<guillemotright>c1 = range A" | 
    "ctype_EvenAutomaton c2\<guillemotright> = range B" 
instance
by(intro_classes)
end


(* Some in and out shortcuts *)
definition createC1Bundle :: "nat \<Rightarrow> EvenAutomaton tsyn SB" where
"createC1Bundle n = (createBundle (Msg (A n)) c1)"

lemma MsgA_ctype: "(Msg (A n)) \<in> ctype c1"
  by (simp add: ctype_tsynI)

lemma createC1Bundle_dom[simp]: "ubDom\<cdot>(createC1Bundle n) = {c1}"
  by (simp add: createC1Bundle_def)

definition createC2Bundle :: "bool \<Rightarrow> EvenAutomaton tsyn SB" where
"createC2Bundle b = (createBundle (Msg (B b)) c2)"

lemma MsgB_ctype: "(Msg (B b)) \<in> ctype c2"
  by (simp add: ctype_tsynI)

lemma createC2Bundle_dom[simp]: "ubDom\<cdot>(createC2Bundle b) = {c2}"
  by (simp add: createC2Bundle_def) 

lemma createC2Bundle_ubgetch[simp]: "(createC2Bundle b) . c2 = \<up>(\<M>(B b))"
  apply(simp add: createC2Bundle_def MsgB_ctype)
  by (metis MsgB_ctype createBundle.rep_eq createBundle_apply fun_upd_same option.sel ubgetch_insert)

lemma createC1Bundle_ubgetch[simp]: "(createC1Bundle n) . c1 = \<up>(\<M>(A n))"
  apply(simp add: createC1Bundle_def MsgA_ctype)
  by (metis MsgA_ctype createBundle.rep_eq createBundle_apply fun_upd_same option.sel ubgetch_insert)
  
lemma createC1Bundle_ubconc[simp]:
  assumes "ubDom\<cdot>sb = {c1}" 
    shows "ubConc (createC1Bundle n)\<cdot>sb  .  c1 = \<up>(\<M>(A n)) \<bullet> (sb. c1)"
  by(simp add: assms ubConc_usclConc_eq usclConc_stream_def)
    
lemma createC1Bundle_ubconc_sbrt[simp]:assumes "ubDom\<cdot>sb = {c1}" 
                               shows "sbRt\<cdot>(ubConc (createC1Bundle n)\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: sbRt_def assms) +
  by (simp add: usclConc_stream_def) 




(* tsynbNull is defined in: timesyn/tsynBundle *)
fun evenAutomatonTransitionH :: "(EvenAutomatonState \<times> (EvenAutomaton tsyn)) \<Rightarrow> (EvenAutomatonState \<times> EvenAutomaton tsyn SB)" where
    "evenAutomatonTransitionH (State Even automaton_sum, (Msg (A a))) = 
       (if((a+automaton_sum) mod 2 = 1) then ((State Odd (a+automaton_sum),(createC2Bundle (False))))
        else if((a+automaton_sum) mod 2 = 0) then ((State Even (a+automaton_sum),(createC2Bundle (True))))
        else  undefined)"  |

    "evenAutomatonTransitionH (State Even automaton_sum, (null)) = 
       (State Even automaton_sum,(tsynbNull c2\<guillemotright>))"  |

    "evenAutomatonTransitionH (State Odd automaton_sum, (Msg (A a))) = 
       (if((a+automaton_sum) mod 2 = 1) then ((State Odd (a+automaton_sum),(createC2Bundle (False))))
       else if((a+automaton_sum) mod 2 = 0) then ((State Even (a+automaton_sum),(createC2Bundle (True))))
       else undefined)"  |

    "evenAutomatonTransitionH (State Odd automaton_sum, (null)) = 
       (State Odd automaton_sum,(tsynbNull c2\<guillemotright>))"  

fun evenAutomatonTransition :: "(EvenAutomatonState \<times> (channel \<rightharpoonup> EvenAutomaton tsyn)) \<Rightarrow> (EvenAutomatonState \<times> EvenAutomaton tsyn SB)" where
"evenAutomatonTransition (s,f) = (if dom(f) = {\<guillemotright>c1} then evenAutomatonTransitionH (s,(f\<rightharpoonup>\<guillemotright>c1)) else undefined)"
 
(*Transition can be generated*)
lemma evenTraTick[simp]:"evenAutomatonTransition (state, [c1 \<mapsto> null]) = (state,(tsynbNull c2) )"
proof -
  have "evenAutomatonTransitionH (state, null) = (state, tsynbNull c2\<guillemotright>)"
    by (metis (full_types) EvenAutomatonState.exhaust EvenAutomatonSubstate.exhaust evenAutomatonTransitionH.simps(2) evenAutomatonTransitionH.simps(4))
  then show ?thesis
    by simp
qed
        
lemma tran_sum_even[simp]: assumes "Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M>(A m)]) = (State Even (summe + m), createC2Bundle True)"
  apply (cases ooo)
   apply auto
  using assms by presburger  +


    
lemma tran_sum_odd[simp]: assumes "\<not>Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M>(A m)]) = (State Odd (summe + m), createC2Bundle False)"
  apply (cases ooo)
   apply auto
  using assms by presburger  +      
  
lift_definition EvenAutomatonAutomaton :: "(EvenAutomatonState, EvenAutomaton tsyn) dAutomaton" is 
  "(evenAutomatonTransition, State Even 0,(tsynbNull c2), {c1}, {c2})"
  by simp

definition EvenAutomatonSPF :: "EvenAutomaton tsyn SPF" where
"EvenAutomatonSPF = da_H EvenAutomatonAutomaton"


end