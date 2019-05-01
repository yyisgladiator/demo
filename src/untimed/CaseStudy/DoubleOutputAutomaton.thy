theory DoubleOutputAutomaton

imports dAutomaton  "../../timesyn/tsynBundle" 

begin

(* This are the actual states from MAA *)
datatype DoubleOutputSubstate = Down | Up
setup_lifting datatype_definition_DoubleOutputSubstate

(* And these have also the variables *)
datatype DoubleOutputState = State DoubleOutputSubstate 
setup_lifting datatype_definition_DoubleOutputState

fun getSubState :: "DoubleOutputState \<Rightarrow> DoubleOutputSubstate" where
    "getSubState (State state_s ) = state_s"


datatype DoubleOutput = A "nat"
instance DoubleOutput :: countable
apply(intro_classes)
by(countable_datatype)
setup_lifting datatype_definition_DoubleOutput

abbreviation input_i1_c1 :: "channel" ("\<guillemotright>i1") where
"\<guillemotright>i1 \<equiv> c1"

abbreviation input_i2_c2 :: "channel" ("\<guillemotright>i2") where
"\<guillemotright>i2 \<equiv> c2"

abbreviation output_o1_c3 :: "channel" ("o1\<guillemotright>") where
"o1\<guillemotright> \<equiv> c3"

abbreviation output_o2_c4 :: "channel" ("o2\<guillemotright>") where
"o2\<guillemotright> \<equiv> c4"

instantiation DoubleOutput :: message
begin
fun ctype_DoubleOutput :: "channel  \<Rightarrow> DoubleOutput set" where
    "ctype_DoubleOutput \<guillemotright>i1 = range A" | 
    "ctype_DoubleOutput \<guillemotright>i2 = range A" | 
    "ctype_DoubleOutput o1\<guillemotright> = range A" | 
    "ctype_DoubleOutput o2\<guillemotright> = range A" 
instance
by(intro_classes)
end

lift_definition createO1Output :: "nat \<Rightarrow> DoubleOutput tsyn SB" is
    "\<lambda>b. [ o1\<guillemotright> \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

lift_definition createO2Output :: "nat \<Rightarrow> DoubleOutput tsyn SB" is
    "\<lambda>b. [ o2\<guillemotright> \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp


fun doubleOutputTransitionH :: "(DoubleOutputState \<times> (DoubleOutput tsyn \<times> DoubleOutput tsyn)) \<Rightarrow> (DoubleOutputState \<times> DoubleOutput tsyn SB)" where
    "doubleOutputTransitionH (State Down , (Msg (A a), Msg (A b))) = 
       (State Down ,(createO1Output (b)) \<uplus> (createO2Output (a)))"  |

    "doubleOutputTransitionH (State Down , (null, Msg (A b))) = 
       (State Up ,(createO1Output (b)) \<uplus> (tsynbNull o2\<guillemotright>))"  |

    "doubleOutputTransitionH (State Down , (Msg (A a), null)) = 
       (State Up ,(tsynbNull o1\<guillemotright>) \<uplus> (createO2Output (a)))"  |

    "doubleOutputTransitionH (State Down , (null, null)) = 
       (State Up ,(tsynbNull o1\<guillemotright>) \<uplus> (tsynbNull o2\<guillemotright>))"  |

    "doubleOutputTransitionH (State Up , (Msg (A a), Msg (A b))) = 
       (State Up ,(createO1Output (a)) \<uplus> (createO2Output (b)))"  |

    "doubleOutputTransitionH (State Up , (Msg (A a), null)) = 
       (State Down ,(createO1Output (a)) \<uplus> (tsynbNull o2\<guillemotright>))"  |

    "doubleOutputTransitionH (State Up , (null, Msg (A b))) = 
       (State Down ,(tsynbNull o1\<guillemotright>) \<uplus> (createO2Output (b)))"  |

    "doubleOutputTransitionH (State Up , (null, null)) = 
       (State Down ,(tsynbNull o1\<guillemotright>) \<uplus> (tsynbNull o2\<guillemotright>))"  

fun doubleOutputTransition :: "(DoubleOutputState \<times> (channel \<rightharpoonup> DoubleOutput tsyn)) \<Rightarrow> (DoubleOutputState \<times> DoubleOutput tsyn SB)" where
"doubleOutputTransition (s,f) = (if dom(f) = {\<guillemotright>i1,\<guillemotright>i2} then doubleOutputTransitionH (s,(f\<rightharpoonup>\<guillemotright>i1,f\<rightharpoonup>\<guillemotright>i2)) else undefined)"
    
    (*Transition can be generated*)

(*State Up*)
lemma doubleOutputTick_Up[simp]:"doubleOutputTransition (State Up, [\<guillemotright>i1 \<mapsto> null, \<guillemotright>i2 \<mapsto> null]) = (State Down,(tsynbNull o1\<guillemotright>  \<uplus> tsynbNull o2\<guillemotright>) )"
  by auto
    
lemma doubleOutputMsg_Up[simp]:"doubleOutputTransition (State Up, [\<guillemotright>i1 \<mapsto> \<M>(A a), \<guillemotright>i2 \<mapsto> \<M>(A b)]) = (State Up,(createO1Output (a)) \<uplus> (createO2Output (b)) )"
 by auto
    
lemma doubleOutputMsgTick_Up[simp]:"doubleOutputTransition (State Up, [\<guillemotright>i1 \<mapsto> \<M>(A a), \<guillemotright>i2 \<mapsto> null]) = (State Down,(createO1Output (a)) \<uplus> (tsynbNull o2\<guillemotright>) )"
 by auto

lemma doubleOutputTickMsg_Up[simp]:"doubleOutputTransition (State Up, [\<guillemotright>i1 \<mapsto> null, \<guillemotright>i2 \<mapsto> \<M>(A b)]) = (State Down,(tsynbNull o1\<guillemotright>) \<uplus> (createO2Output (b)) )"
 by auto
    
(* State down*)
lemma doubleOutputTick_Down[simp]:"doubleOutputTransition (State Down, [\<guillemotright>i1 \<mapsto> null, \<guillemotright>i2 \<mapsto> null]) = (State Up,(tsynbNull o1\<guillemotright>  \<uplus> tsynbNull o2\<guillemotright>) )"
 by auto

lemma doubleOutputMsg_Down[simp]:"doubleOutputTransition (State Down, [\<guillemotright>i1 \<mapsto> \<M>(A a), \<guillemotright>i2 \<mapsto> \<M>(A b)]) = (State Down,(createO1Output (b)) \<uplus> (createO2Output (a)) )"
 by auto
    
lemma doubleOutputMsgTick_Down[simp]:"doubleOutputTransition (State Down, [\<guillemotright>i1 \<mapsto> \<M>(A a), \<guillemotright>i2 \<mapsto> null]) = (State Up,((tsynbNull o1\<guillemotright>)  \<uplus> createO2Output (a)) )"
 by auto

lemma doubleOutputTickMsg_Down[simp]:"doubleOutputTransition (State Down, [\<guillemotright>i1 \<mapsto> null, \<guillemotright>i2 \<mapsto> \<M>(A b)]) = (State Up,( (createO1Output (b))\<uplus> tsynbNull o2\<guillemotright>)  )"
 by auto

lift_definition DoubleOutputAutomaton :: "(DoubleOutputState, DoubleOutput tsyn) dAutomaton" is "(doubleOutputTransition, State Up , (tsynbNull o1\<guillemotright>) \<uplus> (tsynbNull o2\<guillemotright>), {\<guillemotright>i1,\<guillemotright>i2}, {o1\<guillemotright>,o2\<guillemotright>})"
sorry

definition DoubleOutputSPF :: "DoubleOutput tsyn SPF" where
"DoubleOutputSPF = da_H DoubleOutputAutomaton"

lift_definition createC1Output :: "nat \<Rightarrow> DoubleOutput tsyn SB" is
    "\<lambda>b. [ \<guillemotright>i1 \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
  by simp
    
lift_definition createC2Output :: "nat \<Rightarrow> DoubleOutput tsyn SB" is
    "\<lambda>b. [ \<guillemotright>i2 \<mapsto> \<up>(Msg (A b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp

(*step lemmata*)
lemma doubleOutput_h_Up_tick_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton" and "x\<noteq> y"
  shows "h DoubleOutputAutomaton (State x) \<rightleftharpoons> (ubConc (tsynbNull \<guillemotright>i1  \<uplus> tsynbNull \<guillemotright>i2)\<cdot>sb) 
          = ubConc (tsynbNull o1\<guillemotright> \<uplus> tsynbNull o2\<guillemotright>)\<cdot> (h DoubleOutputAutomaton  (State y) \<rightleftharpoons> sb)"
    sorry

lemma doubleOutput_h_Up_MsgTick_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Up) \<rightleftharpoons> (ubConc (createC1Output a  \<uplus> tsynbNull \<guillemotright>i2)\<cdot>sb) 
          = ubConc (createO1Output a  \<uplus> tsynbNull \<guillemotright>i2)\<cdot> (h DoubleOutputAutomaton  (State Down) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Up_TickMsg_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Up) \<rightleftharpoons> (ubConc ( tsynbNull \<guillemotright>i1  \<uplus> createC2Output a )\<cdot>sb) 
          = ubConc ( tsynbNull o1\<guillemotright>  \<uplus> createO2Output a )\<cdot> (h DoubleOutputAutomaton  (State Down) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Up_Msg_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Up) \<rightleftharpoons> (ubConc ( createC1Output a  \<uplus> createC2Output b )\<cdot>sb) 
          = ubConc ( createO1Output a  \<uplus> createO2Output b )\<cdot> (h DoubleOutputAutomaton  (State Up) \<rightleftharpoons> sb)"
  sorry

lemma doubleOutput_h_Down_MsgTick_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Down) \<rightleftharpoons> (ubConc (createC1Output a  \<uplus> tsynbNull \<guillemotright>i2)\<cdot>sb) 
          = ubConc ( tsynbNull o1\<guillemotright> \<uplus> createO2Output a )\<cdot> (h DoubleOutputAutomaton  (State Up) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Down_TickMsg_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Down) \<rightleftharpoons> (ubConc ( tsynbNull \<guillemotright>i1  \<uplus> createC2Output a )\<cdot>sb) 
          = ubConc (createO1Output a  \<uplus>  tsynbNull o2\<guillemotright> )\<cdot> (h DoubleOutputAutomaton  (State Up) \<rightleftharpoons> sb)"
  sorry
    
lemma doubleOutput_h_Down_Msg_step: assumes "ubDom\<cdot>sb = daDom DoubleOutputAutomaton"
  shows "h DoubleOutputAutomaton (State Down) \<rightleftharpoons> (ubConc ( createC1Output a  \<uplus> createC2Output b )\<cdot>sb) 
          = ubConc ( createO1Output b  \<uplus> createO2Output a )\<cdot> (h DoubleOutputAutomaton  (State Down) \<rightleftharpoons> sb)"
  sorry

lemma doubleOutput_H_step: assumes "ubDom\<cdot>sb=daDom DoubleOutputAutomaton"
  shows "H DoubleOutputAutomaton \<rightleftharpoons> sb =  ubConc (tsynbNull o1\<guillemotright>  \<uplus> tsynbNull o2\<guillemotright>)\<cdot>(h DoubleOutputAutomaton (State Up) \<rightleftharpoons> sb)"
  sorry
  
lemma DoubleOutputSPF_final1: assumes "ubDom\<cdot>sb = {\<guillemotright>i1,\<guillemotright>i2}" and "Fin n < ubLen sb" shows "\<exists>outsb. DoubleOutputSPF \<rightleftharpoons> sb = outsb \<and> (*Very ugly and not a complete verification*)
  (ubMapStream (\<lambda>s. \<up>(snth n s)) outsb = ubMapStream (\<lambda>s. \<up>(snth n s)) sb \<or> 
   ubMapStream (\<lambda>s. \<up>(snth n s)) outsb = ubMapStream (\<lambda>s. \<up>(snth n s)) ((ubSetCh\<cdot>((ubSetCh \<cdot>sb) \<guillemotright>i1 (sb .\<guillemotright>i2))) \<guillemotright>i2 (sb . \<guillemotright>i1)))"
  sorry

end