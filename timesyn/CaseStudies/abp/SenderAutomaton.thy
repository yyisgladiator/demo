(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Jul 9, 2018 2:08:06 PM by transformer 1.0.0
 *)
theory SenderAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype SenderSubstate = St | Sf

(* And these have also the variables *)
datatype SenderState = SenderState SenderSubstate (* buffer = *) "nat list"

fun getSenderSubState :: "SenderState \<Rightarrow> SenderSubstate" where
"getSenderSubState (SenderState state_s automaton_buffer) = state_s"

fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (SenderState _ automaton_buffer) = automaton_buffer"
    


fun senderTransitionH :: "(SenderState \<times> (abpMessage tsyn \<times> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
    "senderTransitionH (SenderState Sf automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)>1 \<and> b=False) then ((SenderState St ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)>0 \<and> b=True) then ((SenderState Sf ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=1 \<and> b=False) then ((SenderState St ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair a True ))))
       else if((size automaton_buffer)=0) then ((SenderState Sf ((prepend automaton_buffer)a),(createDsBundle (Pair a False ))))
       else  (SenderState Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState Sf automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)=1 \<and> b=False) then ((SenderState St ((butlast automaton_buffer)),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)=0) then ((SenderState Sf automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>1 \<and> b=False) then ((SenderState St ((butlast automaton_buffer)),(createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)>0 \<and> b=True) then ((SenderState Sf automaton_buffer,(createDsBundle (Pair (last automaton_buffer) False ))))
       else  (SenderState Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState Sf automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0) then ((SenderState Sf ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((SenderState Sf ((prepend automaton_buffer)a),(createDsBundle (Pair a False ))))
       else  (SenderState Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState Sf automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)=0) then ((SenderState Sf automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0) then ((SenderState Sf automaton_buffer,(createDsBundle (Pair (last automaton_buffer) False ))))
       else  (SenderState Sf automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)>1 \<and> b=True) then ((SenderState Sf ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)=1 \<and> b=True) then ((SenderState Sf ((prepend (butlast automaton_buffer))a),(createDsBundle (Pair a False ))))
       else if((size automaton_buffer)>0 \<and> b=False) then ((SenderState St ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((SenderState St ((prepend automaton_buffer)a),(createDsBundle (Pair a True ))))
       else  (SenderState St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)Msg (Bool b))) = 
       (if((size automaton_buffer)=1 \<and> b=True) then ((SenderState Sf ((butlast automaton_buffer)),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> b=False) then ((SenderState St automaton_buffer,(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((SenderState St automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>1 \<and> b=True) then ((SenderState Sf ((butlast automaton_buffer)),(createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
       else  (SenderState St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer, ((*i\<mapsto>*)Msg (Nat a), (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0) then ((SenderState St ((prepend automaton_buffer)a),(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((SenderState St ((prepend automaton_buffer)a),(createDsBundle (Pair a True ))))
       else  (SenderState St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer, ((*i\<mapsto>*)null, (*as\<mapsto>*)null)) = 
       (if((size automaton_buffer)=0) then ((SenderState St automaton_buffer,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0) then ((SenderState St automaton_buffer,(createDsBundle (Pair (last automaton_buffer) True ))))
       else  (SenderState St automaton_buffer, ((tsynbNull (\<C> ''ds'')))))"  

fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<C> ''i'',\<C> ''as''} then senderTransitionH (s,(f\<rightharpoonup>\<C> ''i'',f\<rightharpoonup>\<C> ''as'')) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, abpMessage tsyn) dAutomaton" is "(senderTransition, SenderState Sf [], (tsynbNull (\<C> ''ds'')), {\<C> ''i'', \<C> ''as''}, {\<C> ''ds''})"
  by simp

definition SenderSPF :: "abpMessage tsyn SPF" where
"SenderSPF = da_H SenderAutomaton"

end