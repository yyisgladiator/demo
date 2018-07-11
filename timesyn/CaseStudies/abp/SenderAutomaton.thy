(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Jul 3, 2018 6:22:45 PM by transformer 1.0.0
 *)
theory SenderAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype SenderState = State SenderSubstate (* buffer = *) "nat list"

fun getSubState :: "SenderState \<Rightarrow> SenderSubstate" where
"getSubState (State state_s automaton_buffer) = state_s"

fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (State _ automaton_buffer) = automaton_buffer"
    


fun senderTransitionH :: "(SenderState \<times> (abpMessage tsyn \<times> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
    "senderTransitionH (State Sf automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)>1 \<and> b=False) then ((State St ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)=0) then ((State Sf ((prepend automaton_buffer)a),(createDsBundle (Pair a False ))))
       else if((size automaton_buffer)=1 \<and> b=False) then ((State St ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair a True ))))
       else if((size automaton_buffer)>0 \<and> b=True) then ((State Sf ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) False ))))
       else  (State Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State Sf automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)=0) then ((State Sf ((prepend automaton_buffer)a),(createDsBundle (Pair a False ))))
       else if((size automaton_buffer)>0) then ((State Sf ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) False ))))
       else  (State Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State Sf automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)=0) then ((State Sf automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)=1 \<and> b=False) then ((State St ((butlast automaton_buffer)),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> b=True) then ((State Sf automaton_buffer,(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>1 \<and> b=False) then ((State St ((butlast automaton_buffer)),(createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
       else  (State Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State Sf automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0) then ((State Sf automaton_buffer,(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((State Sf automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else  (State Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State St automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)>1 \<and> b=True) then ((State Sf ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)>0 \<and> b=False) then ((State St ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((State Sf ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair a False ))))
       else if((size automaton_buffer)=0) then ((State St ((prepend automaton_buffer)a),(createDsBundle (Pair a True ))))
       else  (State St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State St automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)>1 \<and> b=True) then ((State Sf ((butlast automaton_buffer)),(createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)=0) then ((State St automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((State Sf ((butlast automaton_buffer)),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> b=False) then ((State St automaton_buffer,(createDsBundle (Pair (last automaton_buffer) True ))))
       else  (State St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State St automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0) then ((State St ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((State St ((prepend automaton_buffer)a),(createDsBundle (Pair a True ))))
       else  (State St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (State St automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0) then ((State St automaton_buffer,(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((State St automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else  (State St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  

fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<C> ''i'',\<C> ''as''} then senderTransitionH (s,(f\<rightharpoonup>\<C> ''i'',f\<rightharpoonup>\<C> ''as'')) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, abpMessage tsyn) dAutomaton" is "(senderTransition, State St [], (tsynbNull (\<C> ''ds'')), {\<C> ''i'', \<C> ''as''}, {\<C> ''ds''})"
  by simp

definition SenderSPF :: "abpMessage tsyn SPF" where
"SenderSPF = da_H SenderAutomaton"

end