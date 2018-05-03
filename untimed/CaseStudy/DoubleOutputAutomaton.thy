theory DoubleOutputAutomaton

imports Automaton  "../../timesyn/tsynStream" "../../timesyn/tsynBundle"

begin

(* This are the actual states from MAA *)
datatype DoubleOutputSubstate = Down | Up
                                        
(* And these have also the variables *)
datatype DoubleOutputState = State DoubleOutputSubstate 

fun getSubState :: "DoubleOutputState \<Rightarrow> DoubleOutputSubstate" where
"getSubState (State state_s ) = state_s"


datatype DoubleOutput = A  nat  | B (* additional terminal generated to prevent errors *)
instance DoubleOutput :: countable
apply(intro_classes)
by(countable_datatype)

instantiation DoubleOutput :: message
begin
    fun ctype_DoubleOutput :: "channel  \<Rightarrow> DoubleOutput set" where
        "ctype_DoubleOutput c1 = range A" | 
        "ctype_DoubleOutput c2 = range A" | 
        "ctype_DoubleOutput c3 = range A" | 
        "ctype_DoubleOutput c4 = range A" 
instance
by(intro_classes)
end

lift_definition createC3Output :: "nat \<Rightarrow> DoubleOutput event SB" is
    "\<lambda>b. [ c3 \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
by simp

lift_definition createC4Output :: "nat \<Rightarrow> DoubleOutput event SB" is
    "\<lambda>b. [ c4 \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
by simp


function doubleOutputTransition :: "(DoubleOutputState \<times> (channel \<rightharpoonup> DoubleOutput event)) \<Rightarrow> (DoubleOutputState \<times> DoubleOutput event SB)" where

    "doubleOutputTransition (State Down , [c1 \<mapsto> Msg a, c2 \<mapsto> Msg b]) = (case a of A c \<Rightarrow> (case b of A d \<Rightarrow> 
        (if(True) then ((State Down ,(createC3Output (d)) \<uplus> (createC4Output (c))))
        else undefined)
     | _ \<Rightarrow> undefined)| _ \<Rightarrow> undefined) "  |

    "doubleOutputTransition (State Down , [c1 \<mapsto> Tick, c2 \<mapsto> Msg a]) = (case a of A d \<Rightarrow> 
        (if(True) then ((State Up ,(createC3Output (d)) \<uplus> (tsynbOneTick c4)))
        else undefined)
     | _ \<Rightarrow> undefined) "  |

    "doubleOutputTransition (State Down , [c1 \<mapsto> Msg a, c2 \<mapsto> Tick]) = (case a of A c \<Rightarrow> 
        (if(True) then ((State Up ,(tsynbOneTick c3) \<uplus> (createC4Output (c))))
        else undefined)
     | _ \<Rightarrow> undefined) "  |

    "doubleOutputTransition (State Down , [c1 \<mapsto> Tick, c2 \<mapsto> Tick]) = 
        (if(True) then ((State Up ,(tsynbOneTick c3) \<uplus> (tsynbOneTick c4)))
        else undefined) "  |

    "doubleOutputTransition (State Up , [c1 \<mapsto> Msg a, c2 \<mapsto> Msg b]) = (case a of A c \<Rightarrow> (case b of A d \<Rightarrow> 
        (if(True) then ((State Up ,(createC3Output (c)) \<uplus> (createC4Output (d))))
        else undefined)
     | _ \<Rightarrow> undefined)| _ \<Rightarrow> undefined) "  |

    "doubleOutputTransition (State Up , [c1 \<mapsto> Msg a, c2 \<mapsto> Tick]) = (case a of A c \<Rightarrow> 
        (if(True) then ((State Down ,(createC3Output (c)) \<uplus> (tsynbOneTick c4)))
        else undefined)
     | _ \<Rightarrow> undefined) "  |

    "doubleOutputTransition (State Up , [c1 \<mapsto> Tick, c2 \<mapsto> Msg a]) = (case a of A d \<Rightarrow> 
        (if(True) then ((State Down ,(tsynbOneTick c3) \<uplus> (createC4Output (d))))
        else undefined)
     | _ \<Rightarrow> undefined) "  |

    "doubleOutputTransition (State Up , [c1 \<mapsto> Tick, c2 \<mapsto> Tick]) = 
        (if(True) then ((State Down ,(tsynbOneTick c3) \<uplus> (tsynbOneTick c4)))
        else undefined) "  |

   "dom f\<noteq> {c1, c2} \<Longrightarrow>  doubleOutputTransition (_,f) = undefined"
apply auto
apply (smt DoubleOutputAutomaton.getSubState.elims DoubleOutputSubstate.exhaust domEventExhaust)
apply (smt channel.distinct(1) event.inject fun_upd_same fun_upd_twist option.sel)
apply (metis (no_types, lifting) channel.distinct(1) event.distinct(1) fun_upd_eqD fun_upd_twist option.inject)
apply (meson event.distinct(1) map_upd_eqD1)
apply (meson event.distinct(1) map_upd_eqD1)
apply (metis fun_upd_apply option.simps(3))
using map_upd_eqD1 apply force
apply (meson event.distinct(1) map_upd_eqD1)
apply (meson event.distinct(1) map_upd_eqD1)
apply (metis fun_upd_apply option.distinct(1))
apply (metis (no_types, lifting) channel.distinct(1) event.inject fun_upd_twist map_upd_eqD1)
apply (metis channel.distinct(1) event.distinct(1) fun_upd_eqD fun_upd_twist option.inject)
apply (metis fun_upd_apply option.distinct(1))
apply (metis fun_upd_apply option.distinct(1))
apply (smt channel.distinct(1) event.inject fun_upd_same fun_upd_twist option.sel)
apply (meson event.distinct(1) map_upd_eqD1)
apply (metis channel.distinct(1) event.distinct(1) fun_upd_eqD fun_upd_twist option.inject)
apply (meson event.distinct(1) map_upd_eqD1)
apply (metis fun_upd_apply option.distinct(1))
apply (metis (no_types, lifting) channel.distinct(1) event.inject fun_upd_twist map_upd_eqD1)
using map_upd_eqD1 apply force
apply (metis channel.distinct(1) event.distinct(1) fun_upd_eqD fun_upd_twist option.inject)
apply (metis fun_upd_apply option.distinct(1))
using map_upd_eqD1 apply fastforce
apply (meson event.distinct(1) map_upd_eqD1)
apply (metis fun_upd_apply option.distinct(1))
by (metis fun_upd_apply option.distinct(1))
termination by lexicographic_order
    
    
    (*Transition can be generated*)
    
(*State Up*)
lemma doubleOutputTick_Up[simp]:"doubleOutputTransition (State Up, [c1 \<mapsto> \<surd>, c2 \<mapsto> \<surd>]) = (State Down,(tsynbOneTick c3  \<uplus> tsynbOneTick c4) )"
  by simp
    
lemma doubleOutputMsg_Up[simp]:"doubleOutputTransition (State Up, [c1 \<mapsto> \<M>(A a), c2 \<mapsto> \<M>(A b)]) = (State Up,(createC3Output (a)) \<uplus> (createC4Output (b)) )"
  by simp
    
lemma doubleOutputMsgTick_Up[simp]:"doubleOutputTransition (State Up, [c1 \<mapsto> \<M>(A a), c2 \<mapsto> \<surd>]) = (State Down,(createC3Output (a)) \<uplus> (tsynbOneTick c4) )"
  by simp

lemma doubleOutputTickMsg_Up[simp]:"doubleOutputTransition (State Up, [c1 \<mapsto> \<surd>, c2 \<mapsto> \<M>(A b)]) = (State Down,(tsynbOneTick c3) \<uplus> (createC4Output (b)) )"
  by simp
    
(* State down*)
lemma doubleOutputTick_Down[simp]:"doubleOutputTransition (State Down, [c1 \<mapsto> \<surd>, c2 \<mapsto> \<surd>]) = (State Up,(tsynbOneTick c3  \<uplus> tsynbOneTick c4) )"
  by simp

lemma doubleOutputMsg_Down[simp]:"doubleOutputTransition (State Down, [c1 \<mapsto> \<M>(A a), c2 \<mapsto> \<M>(A b)]) = (State Down,(createC3Output (b)) \<uplus> (createC4Output (a)) )"
  by simp    
    
lemma doubleOutputMsgTick_Down[simp]:"doubleOutputTransition (State Down, [c1 \<mapsto> \<M>(A a), c2 \<mapsto> \<surd>]) = (State Up,((tsynbOneTick c3)  \<uplus> createC4Output (a)) )"
  by simp

lemma doubleOutputTickMsg_Down[simp]:"doubleOutputTransition (State Down, [c1 \<mapsto> \<surd>, c2 \<mapsto> \<M>(A b)]) = (State Up,( (createC3Output (b))\<uplus> tsynbOneTick c4)  )"
  by simp      

lift_definition DoubleOutputAutomaton :: "(DoubleOutputState, DoubleOutput event) automaton" is "(doubleOutputTransition, State Up , (tsynbOneTick c3) \<uplus> (tsynbOneTick c4), {c1,c2}, {c3,c4})"
sorry

definition DoubleOutputSPF :: "DoubleOutput event SPF" where
"DoubleOutputSPF = H DoubleOutputAutomaton"

lift_definition createC1Output :: "nat \<Rightarrow> DoubleOutput event SB" is
    "\<lambda>b. [ c1 \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
  by simp
    
lift_definition createC2Output :: "nat \<Rightarrow> DoubleOutput event SB" is
    "\<lambda>b. [ c2 \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
by simp

(*step lemmata*)
lemma doubleOutput_h_Up_tick_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton" and "x\<noteq> y"
  shows "h DoubleOutputAutomaton (State x) \<rightleftharpoons> (ubConc (tsynbOneTick c1  \<uplus> tsynbOneTick c2)\<cdot>sb) 
          = ubConc (tsynbOneTick c3 \<uplus> tsynbOneTick c4)\<cdot> (h DoubleOutputAutomaton  (State y) \<rightleftharpoons> sb)"
    sorry

lemma doubleOutput_h_Up_MsgTick_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Up) \<rightleftharpoons> (ubConc (createC1Output a  \<uplus> tsynbOneTick c2)\<cdot>sb) 
          = ubConc (createC3Output a  \<uplus> tsynbOneTick c2)\<cdot> (h DoubleOutputAutomaton  (State Down) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Up_TickMsg_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Up) \<rightleftharpoons> (ubConc ( tsynbOneTick c1  \<uplus> createC2Output a )\<cdot>sb) 
          = ubConc ( tsynbOneTick c3  \<uplus> createC4Output a )\<cdot> (h DoubleOutputAutomaton  (State Down) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Up_Msg_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Up) \<rightleftharpoons> (ubConc ( createC1Output a  \<uplus> createC2Output b )\<cdot>sb) 
          = ubConc ( createC3Output a  \<uplus> createC4Output b )\<cdot> (h DoubleOutputAutomaton  (State Up) \<rightleftharpoons> sb)"
  sorry

lemma doubleOutput_h_Down_MsgTick_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Down) \<rightleftharpoons> (ubConc (createC1Output a  \<uplus> tsynbOneTick c2)\<cdot>sb) 
          = ubConc ( tsynbOneTick c3 \<uplus> createC4Output a )\<cdot> (h DoubleOutputAutomaton  (State Up) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Down_TickMsg_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Down) \<rightleftharpoons> (ubConc ( tsynbOneTick c1  \<uplus> createC2Output a )\<cdot>sb) 
          = ubConc (createC3Output a  \<uplus>  tsynbOneTick c4 )\<cdot> (h DoubleOutputAutomaton  (State Up) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Down_Msg_step: assumes "ubDom\<cdot>sb = getDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Down) \<rightleftharpoons> (ubConc ( createC1Output a  \<uplus> createC2Output b )\<cdot>sb) 
          = ubConc ( createC3Output b  \<uplus> createC4Output a )\<cdot> (h DoubleOutputAutomaton  (State Down) \<rightleftharpoons> sb)"
  sorry

lemma doubleOutput_H_step: assumes "ubDom\<cdot>sb=getDom DoubleOutputAutomaton"
  shows "H DoubleOutputAutomaton \<rightleftharpoons> sb =  ubConc (tsynbOneTick c3  \<uplus> tsynbOneTick c4)\<cdot>(h DoubleOutputAutomaton (State Up) \<rightleftharpoons> sb)"
  sorry
  
lemma DoubleOutputSPF_final1: assumes "ubDom\<cdot>sb = {c1,c2}" and "Fin n < ubLen sb" shows "\<exists>outsb. DoubleOutputSPF \<rightleftharpoons> sb = outsb \<and> (*Very ugly and not a complete verification*)
  (ubMapStream (\<lambda>s. \<up>(snth n s)) outsb = ubMapStream (\<lambda>s. \<up>(snth n s)) sb \<or> 
   ubMapStream (\<lambda>s. \<up>(snth n s)) outsb = ubMapStream (\<lambda>s. \<up>(snth n s)) ((ubSetCh\<cdot>((ubSetCh \<cdot>sb) c1 (sb .c2))) c2 (sb . c1)))"
  sorry

end