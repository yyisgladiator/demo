theory SenderAutomaton

imports "../../../untimed/CaseStudy/Automaton" "../../tsynStream" "../../tsynBundle" 

begin

fun prepend:: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"prepend xs x= x#xs"

(* This are the actual states from MAA *)
datatype SenderSubstate = St | Sf

(* And these have also the variables *)
datatype SenderState = State SenderSubstate "nat" "nat list"

fun getSubState :: "SenderState \<Rightarrow> SenderSubstate" where
    "getSubState (State state_s automaton_c automaton_buffer) = state_s"

fun getC :: "SenderState \<Rightarrow> nat" where
"getC (State _ automaton_c automaton_buffer) = automaton_c"
     
fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (State _ automaton_c automaton_buffer) = automaton_buffer"
    

datatype Sender = B "nat" | A "bool" | C "(nat\<times>bool)"
instance Sender :: countable
apply(intro_classes)
by(countable_datatype)

abbreviation input_as_c1 :: "channel" ("\<guillemotright>as") where
"\<guillemotright>as \<equiv> c1"

abbreviation input_i_c2 :: "channel" ("\<guillemotright>i") where
"\<guillemotright>i \<equiv> c2"

abbreviation output_ds_c3 :: "channel" ("ds\<guillemotright>") where
"ds\<guillemotright> \<equiv> c3"

instantiation Sender :: message
begin
fun ctype_Sender :: "channel  \<Rightarrow> Sender set" where
    "ctype_Sender \<guillemotright>as = range A" | 
    "ctype_Sender \<guillemotright>i = range B" | 
    "ctype_Sender ds\<guillemotright> = range C" 
instance
by(intro_classes)
end

lift_definition createDsOutput :: "(nat\<times>bool) \<Rightarrow> Sender tsyn SB" is
    "\<lambda>b. [ ds\<guillemotright> \<mapsto> \<up>(Msg (C b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_tsyn_def
by simp


fun senderTransitionH :: "(SenderState \<times> (Sender tsyn \<times> Sender tsyn)) \<Rightarrow> (SenderState \<times> Sender tsyn SB)" where
    "senderTransitionH (State Sf automaton_c automaton_buffer, (Msg (A a), Msg (B b))) = 
       (if((size automaton_buffer)=1 \<and> a=False) then ((State St (2) ((prepend (butlast automaton_buffer))b),(createDsOutput (Pair b True ))))
       else if((size automaton_buffer)>1 \<and> a=False) then ((State St (2) ((prepend (butlast automaton_buffer))b),(createDsOutput (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True) then ((State Sf (automaton_c-1) ((prepend automaton_buffer)b),(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True) then ((State Sf (2) ((prepend automaton_buffer)b),(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf (2) ((prepend automaton_buffer)b),(createDsOutput (Pair b False ))))
       else  (State Sf automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_c automaton_buffer, (null, Msg (B b))) = 
       (if((size automaton_buffer)>0 \<and> automaton_c=0) then ((State Sf (2) ((prepend automaton_buffer)b),(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf (2) ((prepend automaton_buffer)b),(createDsOutput (Pair b False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((State Sf (automaton_c-1) ((prepend automaton_buffer)b),(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_c automaton_buffer, (Msg (A a), null)) = 
       (if((size automaton_buffer)=0) then ((State Sf automaton_c automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)=1 \<and> a=False) then ((State St automaton_c ((butlast automaton_buffer)),(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>1 \<and> a=False) then ((State St (2) ((butlast automaton_buffer)),(createDsOutput (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True) then ((State Sf (2) automaton_buffer,(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True) then ((State Sf (automaton_c-1) automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_c automaton_buffer, (null, null)) = 
       (if((size automaton_buffer)>0 \<and> automaton_c=0) then ((State Sf (2) automaton_buffer,(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf automaton_c automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((State Sf (automaton_c-1) automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_c automaton_buffer, (Msg (A a), Msg (B b))) = 
       (if((size automaton_buffer)=1 \<and> a=True) then ((State Sf (2) ((prepend (butlast automaton_buffer))b),(createDsOutput (Pair b False ))))
       else if((size automaton_buffer)=0) then ((State St (2) ((prepend automaton_buffer)b),(createDsOutput (Pair b True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False) then ((State St (2) ((prepend automaton_buffer)b),(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False) then ((State St (automaton_c-1) ((prepend automaton_buffer)b),(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>1 \<and> a=True) then ((State Sf (2) ((prepend (butlast automaton_buffer))b),(createDsOutput (Pair (last (butlast automaton_buffer)) False ))))
       else  (State St automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_c automaton_buffer, (null, Msg (B b))) = 
       (if((size automaton_buffer)=0) then ((State St (2) ((prepend automaton_buffer)b),(createDsOutput (Pair b True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((State St (2) ((prepend automaton_buffer)b),(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((State St (automaton_c-1) ((prepend automaton_buffer)b),(tsynbNull ds\<guillemotright>)))
       else  (State St automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_c automaton_buffer, (Msg (A a), null)) = 
       (if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False) then ((State St (automaton_c-1) automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)=0) then ((State St automaton_c automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)=1 \<and> a=True) then ((State Sf automaton_c ((butlast automaton_buffer)),(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>1 \<and> a=True) then ((State Sf (2) ((butlast automaton_buffer)),(createDsOutput (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False) then ((State St (2) automaton_buffer,(createDsOutput (Pair (last automaton_buffer) True ))))
       else  (State St automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_c automaton_buffer, (null, null)) = 
       (if((size automaton_buffer)>0 \<and> automaton_c>0) then ((State St (automaton_c-1) automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((State St (2) automaton_buffer,(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((State St automaton_c automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State St automaton_c automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  

fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> Sender tsyn)) \<Rightarrow> (SenderState \<times> Sender tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<guillemotright>as,\<guillemotright>i} then senderTransitionH (s,(f\<rightharpoonup>\<guillemotright>as,f\<rightharpoonup>\<guillemotright>i)) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, Sender tsyn) automaton" is "(senderTransition, State Sf 0 [], (tsynbNull ds\<guillemotright>), {c1,c2}, {c3})"
sorry

definition SenderSPF :: "Sender tsyn SPF" where
"SenderSPF = H SenderAutomaton"

end