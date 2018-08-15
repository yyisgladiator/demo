(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Aug 15, 2018 3:13:08 PM by isartransformer 1.0.0
 *)
theory SenderAutomaton

imports "../AutomatonPrelude"

begin

(* These are the actual states from MAA *)
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
"senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (ABPBool a), (*i\<mapsto>*)Msg (ABPNat b))) =
  (if((size automaton_buffer)>1 \<and> a=False) then ((SenderState St ((prepend (butlast automaton_buffer))b) (3), (createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
   else if((size automaton_buffer)=1 \<and> a=False) then ((SenderState St ((prepend (butlast automaton_buffer))b) (3), (createDsBundle (Pair b True ))))
   else if((size automaton_buffer)=0) then ((SenderState Sf ((prepend automaton_buffer)b) (3), (createDsBundle (Pair b False ))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True) then ((SenderState Sf ((prepend automaton_buffer)b) (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True) then ((SenderState Sf ((prepend automaton_buffer)b) (3), (createDsBundle (Pair (last automaton_buffer) False ))))
   else (SenderState Sf automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (ABPBool a), (*i\<mapsto>*)null)) =
  (if((size automaton_buffer)>1 \<and> a=False) then ((SenderState St ((butlast automaton_buffer)) (3), (createDsBundle (Pair (last (butlast automaton_buffer)) True ))))
   else if((size automaton_buffer)=1 \<and> a=False) then ((SenderState St ((butlast automaton_buffer)) automaton_c, (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)=0) then ((SenderState Sf automaton_buffer automaton_c, (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True) then ((SenderState Sf automaton_buffer (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True) then ((SenderState Sf automaton_buffer (3), (createDsBundle (Pair (last automaton_buffer) False ))))
   else (SenderState Sf automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)Msg (ABPNat b))) =
  (if((size automaton_buffer)=0) then ((SenderState Sf ((prepend automaton_buffer)b) (3), (createDsBundle (Pair b False ))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState Sf ((prepend automaton_buffer)b) (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState Sf ((prepend automaton_buffer)b) (3), (createDsBundle (Pair (last automaton_buffer) False ))))
   else (SenderState Sf automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState Sf automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)null)) =
  (if((size automaton_buffer)=0) then ((SenderState Sf automaton_buffer automaton_c, (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState Sf automaton_buffer (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState Sf automaton_buffer (3), (createDsBundle (Pair (last automaton_buffer) False ))))
   else (SenderState Sf automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (ABPBool a), (*i\<mapsto>*)Msg (ABPNat b))) =
  (if((size automaton_buffer)=0) then ((SenderState St ((prepend automaton_buffer)b) (3), (createDsBundle (Pair b True ))))
   else if((size automaton_buffer)>1 \<and> a=True) then ((SenderState Sf ((prepend (butlast automaton_buffer))b) (3), (createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False) then ((SenderState St ((prepend automaton_buffer)b) (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False) then ((SenderState St ((prepend automaton_buffer)b) (3), (createDsBundle (Pair (last automaton_buffer) True ))))
   else if((size automaton_buffer)=1 \<and> a=True) then ((SenderState Sf ((prepend (butlast automaton_buffer))b) (3), (createDsBundle (Pair b False ))))
   else (SenderState St automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)Msg (ABPNat b))) =
  (if((size automaton_buffer)=0) then ((SenderState St ((prepend automaton_buffer)b) (3), (createDsBundle (Pair b True ))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState St ((prepend automaton_buffer)b) (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState St ((prepend automaton_buffer)b) (3), (createDsBundle (Pair (last automaton_buffer) True ))))
   else (SenderState St automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)Msg (ABPBool a), (*i\<mapsto>*)null)) =
  (if((size automaton_buffer)=0) then ((SenderState St automaton_buffer automaton_c, (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>1 \<and> a=True) then ((SenderState Sf ((butlast automaton_buffer)) (3), (createDsBundle (Pair (last (butlast automaton_buffer)) False ))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False) then ((SenderState St automaton_buffer (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False) then ((SenderState St automaton_buffer (3), (createDsBundle (Pair (last automaton_buffer) True ))))
   else if((size automaton_buffer)=1 \<and> a=True) then ((SenderState Sf ((butlast automaton_buffer)) automaton_c, (tsynbNull (\<C> ''ds''))))
   else (SenderState St automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))" |

"senderTransitionH (SenderState St automaton_buffer automaton_c, ((*as\<mapsto>*)null, (*i\<mapsto>*)null)) =
  (if((size automaton_buffer)=0) then ((SenderState St automaton_buffer automaton_c, (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c>0) then ((SenderState St automaton_buffer (automaton_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size automaton_buffer)>0 \<and> automaton_c=0) then ((SenderState St automaton_buffer (3), (createDsBundle (Pair (last automaton_buffer) True ))))
   else (SenderState St automaton_buffer automaton_c, tsynbNull (\<C> ''ds'')))"
        
fun senderTransition :: "(SenderState \<times> (channel \<rightharpoonup> abpMessage tsyn)) \<Rightarrow> (SenderState \<times> abpMessage tsyn SB)" where
"senderTransition (s,f) = (if dom(f) = {\<C> ''as'',\<C> ''i''} then senderTransitionH (s,(f\<rightharpoonup>\<C> ''as'',f\<rightharpoonup>\<C> ''i'')) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, abpMessage tsyn) dAutomaton" is "(senderTransition, SenderState St [] 0, (tsynbNull (\<C> ''ds'')), {\<C> ''as'', \<C> ''i''}, {\<C> ''ds''})"
  by simp

definition SenderSPF :: "abpMessage tsyn SPF" where
"SenderSPF = da_H SenderAutomaton"

(* Line 34 in the MAA model *)
lemma tbd_0_0:
  assumes "(size automaton_buffer)>1 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last (butlast automaton_buffer)) True ))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend (butlast automaton_buffer))b) (3)))"
  oops

(* Line 36 in the MAA model *)
lemma tbd_0_1:
  assumes "(size automaton_buffer)=1 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair b True ))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend (butlast automaton_buffer))b) (3)))"
  oops

(* Line 44 in the MAA model *)
lemma tbd_0_2:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair b False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 46 in the MAA model *)
lemma tbd_0_3:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend automaton_buffer)b) (automaton_c-1)))"
  oops

(* Line 48 in the MAA model *)
lemma tbd_0_4:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 35 in the MAA model *)
lemma tbd_1_0:
  assumes "(size automaton_buffer)>1 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last (butlast automaton_buffer)) True ))\<cdot>(da_h SenderAutomaton (SenderState St ((butlast automaton_buffer)) (3)))"
  oops

(* Line 37 in the MAA model *)
lemma tbd_1_1:
  assumes "(size automaton_buffer)=1 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St ((butlast automaton_buffer)) automaton_c))"
  oops

(* Line 39 in the MAA model *)
lemma tbd_1_2:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))"
  oops

(* Line 41 in the MAA model *)
lemma tbd_1_3:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer (automaton_c-1)))"
  oops

(* Line 42 in the MAA model *)
lemma tbd_1_4:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) False ))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer (3)))"
  oops

(* Line 45 in the MAA model *)
lemma tbd_2_0:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair b False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 47 in the MAA model *)
lemma tbd_2_1:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend automaton_buffer)b) (automaton_c-1)))"
  oops

(* Line 49 in the MAA model *)
lemma tbd_2_2:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 38 in the MAA model *)
lemma tbd_3_0:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))"
  oops

(* Line 40 in the MAA model *)
lemma tbd_3_1:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer (automaton_c-1)))"
  oops

(* Line 43 in the MAA model *)
lemma tbd_3_2:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) False ))\<cdot>(da_h SenderAutomaton (SenderState Sf automaton_buffer (3)))"
  oops

(* Line 26 in the MAA model *)
lemma tbd_4_0:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair b True ))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 28 in the MAA model *)
lemma tbd_4_1:
  assumes "(size automaton_buffer)>1 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last (butlast automaton_buffer)) False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend (butlast automaton_buffer))b) (3)))"
  oops

(* Line 29 in the MAA model *)
lemma tbd_4_2:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend automaton_buffer)b) (automaton_c-1)))"
  oops

(* Line 31 in the MAA model *)
lemma tbd_4_3:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) True ))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 33 in the MAA model *)
lemma tbd_4_4:
  assumes "(size automaton_buffer)=1 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair b False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((prepend (butlast automaton_buffer))b) (3)))"
  oops

(* Line 27 in the MAA model *)
lemma tbd_5_0:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair b True ))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 30 in the MAA model *)
lemma tbd_5_1:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend automaton_buffer)b) (automaton_c-1)))"
  oops

(* Line 32 in the MAA model *)
lemma tbd_5_2:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle b)\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) True ))\<cdot>(da_h SenderAutomaton (SenderState St ((prepend automaton_buffer)b) (3)))"
  oops

(* Line 18 in the MAA model *)
lemma tbd_6_0:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))"
  oops

(* Line 19 in the MAA model *)
lemma tbd_6_1:
  assumes "(size automaton_buffer)>1 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last (butlast automaton_buffer)) False ))\<cdot>(da_h SenderAutomaton (SenderState Sf ((butlast automaton_buffer)) (3)))"
  oops

(* Line 21 in the MAA model *)
lemma tbd_6_2:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer (automaton_c-1)))"
  oops

(* Line 23 in the MAA model *)
lemma tbd_6_3:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0 \<and> a=False"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) True ))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer (3)))"
  oops

(* Line 25 in the MAA model *)
lemma tbd_6_4:
  assumes "(size automaton_buffer)=1 \<and> a=True"
    shows "spfConcIn  (createAsBundle a \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf ((butlast automaton_buffer)) automaton_c))"
  oops

(* Line 20 in the MAA model *)
lemma tbd_7_0:
  assumes "(size automaton_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))"
  oops

(* Line 22 in the MAA model *)
lemma tbd_7_1:
  assumes "(size automaton_buffer)>0 \<and> automaton_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer (automaton_c-1)))"
  oops

(* Line 24 in the MAA model *)
lemma tbd_7_2:
  assumes "(size automaton_buffer)>0 \<and> automaton_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer automaton_c))
         = spfConcOut (createDsBundle (Pair (last automaton_buffer) True ))\<cdot>(da_h SenderAutomaton (SenderState St automaton_buffer (3)))"
  oops


end