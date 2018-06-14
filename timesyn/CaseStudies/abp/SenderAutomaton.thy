

theory SenderAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype SenderState = State SenderSubstate "nat list"

fun getSubState :: "SenderState \<Rightarrow> SenderSubstate" where
    "getSubState (State state_s automaton_buffer) = state_s"

fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (State _ automaton_buffer) = automaton_buffer"
    


abbreviation input_i_c6 :: "channel" ("\<guillemotright>i") where
"\<guillemotright>i \<equiv> c6"

abbreviation input_as_c1 :: "channel" ("\<guillemotright>as") where
"\<guillemotright>as \<equiv> c1"

abbreviation output_ds_c3 :: "channel" ("ds\<guillemotright>") where
"ds\<guillemotright> \<equiv> c3"


lift_definition createDsOutput :: "(nat\<times>bool) \<Rightarrow> Message tsyn SB" is
    "\<lambda>b. [ ds\<guillemotright> \<mapsto> \<up>(Msg (Pair_nat_bool b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp


fun senderTransitionH :: "(SenderState \<times> (Message tsyn \<times> Message tsyn)) \<Rightarrow> (SenderState \<times> Message tsyn SB)" where
    "senderTransitionH (State Sf automaton_buffer, (Msg (nat a), Msg (bool b))) = 
       (if((size automaton_buffer)>1 \<and> b=False) then ((State St ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)=0) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair a False ))))
       else if((size automaton_buffer)>0 \<and> b=True) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=1 \<and> b=False) then ((State St ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair a True ))))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_buffer, (Msg (nat a), null)) = 
       (if((size automaton_buffer)>0) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair a False ))))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_buffer, (null, Msg (bool b))) = 
       (if((size automaton_buffer)>0 \<and> b=True) then ((State Sf automaton_buffer,(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>1 \<and> b=False) then ((State St ((butlast automaton_buffer)),(createDsOutput (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)=0) then ((State Sf automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)=1 \<and> b=False) then ((State St ((butlast automaton_buffer)),(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_buffer, (null, null)) = 
       (if((size automaton_buffer)>0) then ((State Sf automaton_buffer,(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (Msg (nat a), Msg (bool b))) = 
       (if((size automaton_buffer)=0) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair a True ))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((State Sf ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair a False ))))
       else if((size automaton_buffer)>1 \<and> b=True) then ((State Sf ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)>0 \<and> b=False) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) True ))))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (null, Msg (bool b))) = 
       (if((size automaton_buffer)=0) then ((State St automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>0 \<and> b=False) then ((State St automaton_buffer,(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((State Sf ((butlast automaton_buffer)),(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>1 \<and> b=True) then ((State Sf ((butlast automaton_buffer)),(createDsOutput (Pair (last (butlast automaton_buffer)) False ))))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (Msg (nat a), null)) = 
       (if((size automaton_buffer)=0) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair a True ))))
       else if((size automaton_buffer)>0) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) True ))))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (null, null)) = 
       (if((size automaton_buffer)>0) then ((State St automaton_buffer,(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((State St automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  

fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> Message tsyn)) \<Rightarrow> (SenderState \<times> Message tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<guillemotright>i,\<guillemotright>as} then senderTransitionH (s,(f\<rightharpoonup>\<guillemotright>i,f\<rightharpoonup>\<guillemotright>as)) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, Message tsyn) automaton" is "(senderTransition, State Sf [], (tsynbNull ds\<guillemotright>), {c6,c1}, {c3})"
sorry

definition SenderSPF :: "Message tsyn SPF" where
"SenderSPF = H SenderAutomaton"

end