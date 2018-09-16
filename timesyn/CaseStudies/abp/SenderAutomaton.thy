(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Aug 8, 2018 9:44:47 PM by isartransformer 1.0.0
 *)
theory SenderAutomaton

imports "../AutomatonPrelude"

begin

(* This are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype SenderState = SenderState SenderSubstate (* buffer = *) "nat list" (* c = *) "nat"

fun getSenderSubState :: "SenderState \<Rightarrow> SenderSubstate" where
"getSenderSubState (SenderState state_s automaton_buffer automaton_c) = state_s"

fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (SenderState _ automaton_buffer automaton_c) = automaton_buffer"
     
fun getC :: "SenderState \<Rightarrow> nat" where
"getC (SenderState _ automaton_buffer automaton_c) = automaton_c"
    


fun senderTransitionH :: "(SenderState \<times> (abpMessage tsyn \<times> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
    "senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (Bool a), (*i\<mapsto>*)Msg (Nat b))) = 
       (if((size automaton_buffer)=0) then ((SenderState Sf ((prepend automaton_buffer)b) (3),(createDsBundle (Pair b False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True) then ((SenderState Sf ((prepend automaton_buffer)b) (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)=1 \<and> a=False) then ((SenderState St ((prepend (butlast automaton_buffer))b) (3),(createDsBundle (Pair b True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True) then ((SenderState Sf ((prepend automaton_buffer)b) (3),(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>1 \<and> a=False) then ((SenderState St ((prepend (butlast automaton_buffer))b) (3),(createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
       else  (SenderState Sf automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)Msg (Nat b))) = 
       (if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState Sf ((prepend automaton_buffer)b) (3),(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState Sf ((prepend automaton_buffer)b) (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)=0) then ((SenderState Sf ((prepend automaton_buffer)b) (3),(createDsBundle (Pair b False ))))
       else  (SenderState Sf automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (Bool a), (*i\<mapsto>*)null)) = 
       (if((size automaton_buffer)=0) then ((SenderState Sf automaton_buffer automaton_c,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True) then ((SenderState Sf automaton_buffer (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>1 \<and> a=False) then ((SenderState St ((butlast automaton_buffer)) (3),(createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True) then ((SenderState Sf automaton_buffer (3),(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=1 \<and> a=False) then ((SenderState St ((butlast automaton_buffer)) automaton_c,(tsynbNull (\<C> ''ds''))))
       else  (SenderState Sf automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState Sf automaton_buffer (3),(createDsBundle (Pair (last automaton_buffer) False ))))
       else if((size automaton_buffer)=0) then ((SenderState Sf automaton_buffer automaton_c,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState Sf automaton_buffer (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else  (SenderState Sf automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (Bool a), (*i\<mapsto>*)Msg (Nat b))) = 
       (if((size automaton_buffer)=0) then ((SenderState St ((prepend automaton_buffer)b) (3),(createDsBundle (Pair b True ))))
       else if((size automaton_buffer)>1 \<and> a=True) then ((SenderState Sf ((prepend (butlast automaton_buffer))b) (3),(createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False) then ((SenderState St ((prepend automaton_buffer)b) (3),(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=1 \<and> a=True) then ((SenderState Sf ((prepend (butlast automaton_buffer))b) (3),(createDsBundle (Pair b False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False) then ((SenderState St ((prepend automaton_buffer)b) (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else  (SenderState St automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)Msg (Nat b))) = 
       (if((size automaton_buffer)=0) then ((SenderState St ((prepend automaton_buffer)b) (3),(createDsBundle (Pair b True ))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState St ((prepend automaton_buffer)b) (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState St ((prepend automaton_buffer)b) (3),(createDsBundle (Pair (last automaton_buffer) True ))))
       else  (SenderState St automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (Bool a), (*i\<mapsto>*)null)) = 
       (if((size automaton_buffer)=0) then ((SenderState St automaton_buffer automaton_c,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)=1 \<and> a=True) then ((SenderState Sf ((butlast automaton_buffer)) automaton_c,(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False) then ((SenderState St automaton_buffer (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>1 \<and> a=True) then ((SenderState Sf ((butlast automaton_buffer)) (3),(createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False) then ((SenderState St automaton_buffer (3),(createDsBundle (Pair (last automaton_buffer) True ))))
       else  (SenderState St automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  |

    "senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)null)) = 
       (if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState St automaton_buffer (automaton_c-1),(tsynbNull (\<C> ''ds''))))
       else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState St automaton_buffer (3),(createDsBundle (Pair (last automaton_buffer) True ))))
       else if((size automaton_buffer)=0) then ((SenderState St automaton_buffer automaton_c,(tsynbNull (\<C> ''ds''))))
       else  (SenderState St automaton_buffer automaton_c, ((tsynbNull (\<C> ''ds'')))))"  

fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<C> ''as'',\<C> ''i''} then senderTransitionH (s,(f\<rightharpoonup>\<C> ''as'',f\<rightharpoonup>\<C> ''i'')) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, abpMessage tsyn) dAutomaton" is "(senderTransition, SenderState St [] 0, (tsynbNull (\<C> ''ds'')), {\<C> ''as'', \<C> ''i''}, {\<C> ''ds''})"
  by simp

definition SenderSPF :: "abpMessage tsyn SPF" where
"SenderSPF = da_H SenderAutomaton"

end