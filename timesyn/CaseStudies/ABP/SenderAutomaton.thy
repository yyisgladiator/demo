theory SenderAutomaton

imports "../../../untimed/CaseStudy/Automaton" "../../tsynStream" "../../tsynBundle" 

begin

fun prepend:: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"prepend xs x= x#xs"

(* This are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype SenderState = State SenderSubstate "nat list"

fun getSubState :: "SenderState \<Rightarrow> SenderSubstate" where
    "getSubState (State state_s automaton_buffer) = state_s"

fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (State _ automaton_buffer) = automaton_buffer"
    

datatype Sender = A "nat" | B "bool" | C "(nat\<times>bool)"
instance Sender :: countable
apply(intro_classes)
by(countable_datatype)

abbreviation input_i_c1 :: "channel" ("\<guillemotright>i") where
"\<guillemotright>i \<equiv> c1"

abbreviation input_as_c2 :: "channel" ("\<guillemotright>as") where
"\<guillemotright>as \<equiv> c2"

abbreviation output_ds_c3 :: "channel" ("ds\<guillemotright>") where
"ds\<guillemotright> \<equiv> c3"

instantiation Sender :: message
begin
fun ctype_Sender :: "channel  \<Rightarrow> Sender set" where
    "ctype_Sender \<guillemotright>i = range A" | 
    "ctype_Sender \<guillemotright>as = range B" | 
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
    "senderTransitionH (State Sf automaton_buffer, (Msg (A a), Msg (B b))) = 
       (if((size automaton_buffer)>0 \<and> b=True) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>1 \<and> b=False) then ((State St ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)=1 \<and> b=False) then ((State St ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair a True ))))
       else if((size automaton_buffer)=0) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair a False ))))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_buffer, (null, Msg (B b))) = 
       (if((size automaton_buffer)>0 \<and> b=True) then ((State Sf automaton_buffer,(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>1 \<and> b=False) then ((State St ((butlast automaton_buffer)),(createDsOutput (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)=0) then ((State Sf automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)=1 \<and> b=False) then ((State St ((butlast automaton_buffer)),(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_buffer, (Msg (A a), null)) = 
       (if((size automaton_buffer)=0) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair a False ))))
       else if((size automaton_buffer)>0) then ((State Sf ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) False ))))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State Sf automaton_buffer, (null, null)) = 
       (if((size automaton_buffer)>0) then ((State Sf automaton_buffer,(createDsOutput (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State Sf automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (Msg (A a), Msg (B b))) = 
       (if((size automaton_buffer)>0 \<and> b=False) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((State Sf ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair a False ))))
       else if((size automaton_buffer)=0) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair a True ))))
       else if((size automaton_buffer)>1 \<and> b=True) then ((State Sf ((prepend (butlast automaton_buffer))a),(createDsOutput (Pair (last (butlast automaton_buffer)) False ))))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (null, Msg (B b))) = 
       (if((size automaton_buffer)=0) then ((State St automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>1 \<and> b=True) then ((State Sf ((butlast automaton_buffer)),(createDsOutput (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((State Sf ((butlast automaton_buffer)),(tsynbNull ds\<guillemotright>)))
       else if((size automaton_buffer)>0 \<and> b=False) then ((State St automaton_buffer,(createDsOutput (Pair (last automaton_buffer) True ))))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (Msg (A a), null)) = 
       (if((size automaton_buffer)>0) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((State St ((prepend automaton_buffer)a),(createDsOutput (Pair a True ))))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  |

    "senderTransitionH (State St automaton_buffer, (null, null)) = 
       (if((size automaton_buffer)>0) then ((State St automaton_buffer,(createDsOutput (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((State St automaton_buffer,(tsynbNull ds\<guillemotright>)))
       else  (State St automaton_buffer, ((tsynbNull ds\<guillemotright>))))"  

fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> Sender tsyn)) \<Rightarrow> (SenderState \<times> Sender tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<guillemotright>i,\<guillemotright>as} then senderTransitionH (s,(f\<rightharpoonup>\<guillemotright>i,f\<rightharpoonup>\<guillemotright>as)) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, Sender tsyn) automaton" is "(senderTransition, State Sf [], (tsynbNull ds\<guillemotright>), {c1,c2}, {c3})"
sorry

definition SenderSPF :: "Sender tsyn SPF" where
"SenderSPF = H SenderAutomaton"


(* ----------------------------------------------------------------------- *)
section {* Some Sender tsyn stream ubundle for testing the sender function.
           Move this section to Components.thy as soon as it imports SenderAutomaton.thy*}
(* ----------------------------------------------------------------------- *)

(* Everything works fine: Sending two messages while receiving the correct acknowledgement bits  *)
definition snd_testinput_msg_1 :: "nat tsyn stream" where 
"snd_testinput_msg_1 \<equiv> list2s [Msg 1, Msg 2, null]"

definition snd_testinput_acks_1 :: "bool tsyn stream" where 
"snd_testinput_acks_1 \<equiv> list2s [null, Msg True, Msg False]"

lift_definition snd_testubundle_1 :: "Sender tsyn SB" is
"[\<guillemotright>i \<mapsto> tsynMap A\<cdot>snd_testinput_msg_1, \<guillemotright>as \<mapsto> tsynMap B\<cdot>snd_testinput_acks_1]" 
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  apply(simp add: snd_testinput_msg_1_def)
  apply(simp add: snd_testinput_acks_1_def)
  apply(simp add: tsynMap_def)
  by (simp add: rangeI)



(*Medium 1 or Medium 2 loses the first message *)
definition snd_testinput_msg_2 :: "nat tsyn stream" where 
"snd_testinput_msg_2 \<equiv> list2s [Msg 1, null, Msg 2]"

definition snd_testinput_acks_2 :: "bool tsyn stream" where 
"snd_testinput_acks_2 \<equiv> list2s [null, null, Msg True, Msg False]"

lift_definition snd_testubundle_2 :: "Sender tsyn SB" is
"[\<guillemotright>i \<mapsto> tsynMap A\<cdot>snd_testinput_msg_2, \<guillemotright>as \<mapsto> tsynMap B\<cdot>snd_testinput_acks_2]" 
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  apply(simp add: snd_testinput_msg_2_def)
  apply(simp add: snd_testinput_acks_2_def)
  apply(simp add: tsynMap_def)
  by (simp add: rangeI)


(*There are two messages to send and both mediums lose either the ack or the message two times in a row *)
definition snd_testinput_msg_3 :: "nat tsyn stream" where 
"snd_testinput_msg_3 \<equiv> list2s [Msg 1, Msg 2, null, null, null]"

definition snd_testinput_acks_3 :: "bool tsyn stream" where 
"snd_testinput_acks_3 \<equiv> list2s [null, null, null, Msg True, Msg False]"

lift_definition snd_testubundle_3 :: "Sender tsyn SB" is
"[\<guillemotright>i \<mapsto> tsynMap A\<cdot>snd_testinput_msg_3, \<guillemotright>as \<mapsto> tsynMap B\<cdot>snd_testinput_acks_3]" 
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  apply(simp add: snd_testinput_msg_3_def)
  apply(simp add: snd_testinput_acks_3_def)
  apply(simp add: tsynMap_def)
  by (simp add: rangeI)














end