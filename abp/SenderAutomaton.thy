(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 21, 2018 4:47:19 PM by isartransformer 1.0.0
 *)
theory SenderAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"

section \<open>Datatype definition\<close>

datatype senderMessage = SenderBool "bool" | SenderNat "nat" | SenderPair_SenderNat_SenderBool "(nat\<times>bool)"
instance senderMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation senderMessage :: message
begin
  fun ctype_senderMessage :: "channel  \<Rightarrow> senderMessage set" where
  "ctype_senderMessage c = (
    if c = \<C> ''as'' then range SenderBool else
    if c = \<C> ''i'' then range SenderNat else
    if c = \<C> ''ds'' then range SenderPair_SenderNat_SenderBool else
    {})"
    instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition senderElem_raw_As :: "bool \<Rightarrow> senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''as'' \<mapsto> Msg (SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition senderElem_raw_I :: "nat \<Rightarrow> senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''i'' \<mapsto> Msg (SenderNat x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition senderElem_raw_Ds :: "(nat\<times>bool) \<Rightarrow> senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ds'' \<mapsto> Msg (SenderPair_SenderNat_SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun senderElem_As :: "bool tsyn \<Rightarrow> senderMessage tsyn sbElem" where
"senderElem_As (Msg port_as) = senderElem_raw_As port_as" |
"senderElem_As null = sbeNull {\<C> ''as''}"

definition sender_As :: "bool tsyn \<Rightarrow> senderMessage tsyn SB" where
"sender_As port_as = sbe2SB (senderElem_As port_as)"

fun senderElem_I :: "nat tsyn \<Rightarrow> senderMessage tsyn sbElem" where
"senderElem_I (Msg port_i) = senderElem_raw_I port_i" |
"senderElem_I null = sbeNull {\<C> ''i''}"

definition sender_I :: "nat tsyn \<Rightarrow> senderMessage tsyn SB" where
"sender_I port_i = sbe2SB (senderElem_I port_i)"

fun senderElem_Ds :: "(nat\<times>bool) tsyn \<Rightarrow> senderMessage tsyn sbElem" where
"senderElem_Ds (Msg port_ds) = senderElem_raw_Ds port_ds" |
"senderElem_Ds null = sbeNull {\<C> ''ds''}"

definition sender_Ds :: "(nat\<times>bool) tsyn \<Rightarrow> senderMessage tsyn SB" where
"sender_Ds port_ds = sbe2SB (senderElem_Ds port_ds)"

(* Create one sbElem for all input channels *)
fun senderElemIn_As_I :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> senderMessage tsyn sbElem" where
"senderElemIn_As_I port_as port_i = (senderElem_As port_as) \<plusminus> (senderElem_I port_i)"

(* Create one sbElem for all output channels *)
fun senderElemOut_Ds :: "(nat\<times>bool) tsyn \<Rightarrow> senderMessage tsyn sbElem" where
"senderElemOut_Ds port_ds = (senderElem_Ds port_ds)"

(* Create one SB for all input channels *)
fun senderIn_As_I :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> senderMessage tsyn SB" where
"senderIn_As_I port_as port_i = (sbe2SB (senderElemIn_As_I port_as port_i))"

(* Create one SB for all output channels *)
fun senderOut_Ds :: "(nat\<times>bool) tsyn \<Rightarrow> senderMessage tsyn SB" where
"senderOut_Ds port_ds = (sbe2SB (senderElemOut_Ds port_ds))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun sender_list_As :: "(bool tsyn) list \<Rightarrow> senderMessage tsyn SB" where
"sender_list_As (x#xs) = ubConcEq (sender_As x)\<cdot>(sender_list_As xs)" |
"sender_list_As []     = ubLeast {\<C> ''as''}"

fun sender_list_I :: "(nat tsyn) list \<Rightarrow> senderMessage tsyn SB" where
"sender_list_I (x#xs) = ubConcEq (sender_I x)\<cdot>(sender_list_I xs)" |
"sender_list_I []     = ubLeast {\<C> ''i''}"

fun sender_list_Ds :: "((nat\<times>bool) tsyn) list \<Rightarrow> senderMessage tsyn SB" where
"sender_list_Ds (x#xs) = ubConcEq (sender_Ds x)\<cdot>(sender_list_Ds xs)" |
"sender_list_Ds []     = ubLeast {\<C> ''ds''}"

(* Create one SB for all input channels *)
fun senderIn_list_As_I :: "bool tsyn list \<Rightarrow> nat tsyn list \<Rightarrow> senderMessage tsyn SB" where
"senderIn_list_As_I port_as port_i = (sender_list_As port_as) \<uplus> (sender_list_I port_i)"

(* Create one SB for all output channels *)
fun senderOut_list_Ds :: "(nat\<times>bool) tsyn list \<Rightarrow> senderMessage tsyn SB" where
"senderOut_list_Ds port_ds = (sender_list_Ds port_ds)"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

definition sender_stream_As :: "(bool) tsyn stream \<Rightarrow> senderMessage tsyn SB" where
"sender_stream_As = undefined"

definition sender_stream_I :: "(nat) tsyn stream \<Rightarrow> senderMessage tsyn SB" where
"sender_stream_I = undefined"

definition sender_stream_Ds :: "((nat\<times>bool)) tsyn stream \<Rightarrow> senderMessage tsyn SB" where
"sender_stream_Ds = undefined"

(* Create one SB for all input channels *)
fun senderIn_stream_As_I :: "bool tsyn stream \<Rightarrow> nat tsyn stream \<Rightarrow> senderMessage tsyn SB" where
"senderIn_stream_As_I port_as port_i = (sender_stream_As port_as) \<uplus> (sender_stream_I port_i)"

(* Create one SB for all output channels *)
fun senderOut_stream_Ds :: "(nat\<times>bool) tsyn stream \<Rightarrow> senderMessage tsyn SB" where
"senderOut_stream_Ds port_ds = (sender_stream_Ds port_ds)"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun senderElem_get_As :: "senderMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"senderElem_get_As sbe = undefined"

fun senderElem_get_stream_As :: "senderMessage tsyn SB \<Rightarrow> (bool) tsyn stream" where
"senderElem_get_stream_As sb = undefined"

fun senderElem_get_I :: "senderMessage tsyn sbElem \<Rightarrow> (nat) tsyn" where
"senderElem_get_I sbe = undefined"

fun senderElem_get_stream_I :: "senderMessage tsyn SB \<Rightarrow> (nat) tsyn stream" where
"senderElem_get_stream_I sb = undefined"

fun senderElem_get_Ds :: "senderMessage tsyn sbElem \<Rightarrow> ((nat\<times>bool)) tsyn" where
"senderElem_get_Ds sbe = undefined"

fun senderElem_get_stream_Ds :: "senderMessage tsyn SB \<Rightarrow> ((nat\<times>bool)) tsyn stream" where
"senderElem_get_stream_Ds sb = undefined"




section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype SenderState = SenderState SenderSubstate (* buffer = *) "nat list" (* c = *) "nat"

(* Function to get the substate *)
fun getSenderSubState :: "SenderState \<Rightarrow> SenderSubstate" where
"getSenderSubState (SenderState s _ _) = s"

(* Functions to get the variables *)
fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (SenderState _ var_buffer var_c) = var_buffer"

fun getC :: "SenderState \<Rightarrow> nat" where
"getC (SenderState _ var_buffer var_c) = var_c"


(* Helper that allows us to utilize pattern matching *)
fun senderTransitionH :: "(SenderState \<times> (bool tsyn \<times> nat tsyn)) \<Rightarrow> (SenderState \<times> senderMessage tsyn SB)" where
"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair port_i True)))))
   else if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) var_c, (senderOut_Ds null)))
   else if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf var_buffer (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf var_buffer var_c, (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i True)))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair port_i False)))))
   else (SenderState St var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (senderOut_Ds null)))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St var_buffer (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) var_c, (senderOut_Ds null)))
   else (SenderState St var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i True)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (senderOut_Ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St var_buffer (var_c-1), (senderOut_Ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (senderOut_Ds null)))"

(* Domain *)
definition senderDom :: "channel set" where
"senderDom = {\<C> ''as'', \<C> ''i''}"

(* Range *)
definition senderRan :: "channel set" where
"senderRan = {\<C> ''ds''}"

(* Transition function *)
fun senderTransition :: "(SenderState \<times> senderMessage tsyn sbElem) \<Rightarrow> (SenderState \<times> senderMessage tsyn SB)" where
"senderTransition (s,b) = (if (sbeDom b) = senderDom then senderTransitionH (s, (senderElem_get_As b, senderElem_get_I b)) else undefined)"

(* The final automaton *)
lift_definition SenderAutomaton :: "(SenderState, senderMessage tsyn) dAutomaton" is
"(senderTransition, SenderState St []  0, (senderOut_Ds null), senderDom, senderRan)"
  by (simp add: senderDom_def senderRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition SenderStep :: "(SenderState \<Rightarrow> (senderMessage tsyn, senderMessage tsyn) SPF)" where
"SenderStep = da_h SenderAutomaton"

(* The final SPF *)
definition SenderSPF :: "(senderMessage tsyn, senderMessage tsyn) SPF" where
"SenderSPF = da_H SenderAutomaton"


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma transition_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) True))))"
  oops

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma transition_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair port_i True))))"
  oops

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma transition_0_2:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i False))))"
  oops

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null))"
  oops

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) False))))"
  oops

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma transition_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState St (butlast var_buffer) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) True))))"
  oops

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma transition_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState St (butlast var_buffer) var_c, (senderOut_Ds null))"
  oops

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma transition_1_2:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState Sf var_buffer var_c, (senderOut_Ds null))"
  oops

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma transition_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState Sf var_buffer (var_c-1), (senderOut_Ds null))"
  oops

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState Sf var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) False))))"
  oops

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma transition_2_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i False))))"
  oops

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null))"
  oops

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) False))))"
  oops

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma transition_3_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I null null))
         = (SenderState Sf var_buffer var_c, (senderOut_Ds null))"
  oops

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma transition_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I null null))
         = (SenderState Sf var_buffer var_c, (senderOut_Ds null))"
  oops

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_As_I null null))
         = (SenderState Sf var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) False))))"
  oops

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma transition_4_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i True))))"
  oops

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma transition_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) False))))"
  oops

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null))"
  oops

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) True))))"
  oops

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma transition_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_Ds (Msg (Pair port_i False))))"
  oops

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma transition_5_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState St var_buffer var_c, (senderOut_Ds null))"
  oops

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma transition_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) 3, (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) False))))"
  oops

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma transition_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState St var_buffer (var_c-1), (senderOut_Ds null))"
  oops

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState St var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) True))))"
  oops

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma transition_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) var_c, (senderOut_Ds null))"
  oops

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma transition_6_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair port_i True))))"
  oops

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_Ds null))"
  oops

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_Ds (Msg (Pair (last var_buffer) True))))"
  oops

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma transition_7_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I null null))
         = (SenderState St var_buffer var_c, (senderOut_Ds null))"
  oops

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma transition_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I null null))
         = (SenderState St var_buffer (var_c-1), (senderOut_Ds null))"
  oops

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_As_I null null))
         = (SenderState St var_buffer 3, (senderOut_Ds (Msg (Pair (last var_buffer) True))))"
  oops


section \<open>Step-wise lemmata for the SPF\<close>

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma step_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) True)))\<cdot>(SenderStep (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma step_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair port_i True)))\<cdot>(SenderStep (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma step_0_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair port_i False)))\<cdot>(SenderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) False)))\<cdot>(SenderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma step_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) True)))\<cdot>(SenderStep (SenderState St (butlast var_buffer) 3))"
  oops

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma step_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St (butlast var_buffer) var_c))"
  oops

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma step_1_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))"
  oops

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma step_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf var_buffer (var_c-1)))"
  oops

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) False)))\<cdot>(SenderStep (SenderState Sf var_buffer 3))"
  oops

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma step_2_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I null (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair port_i False)))\<cdot>(SenderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_As_I null (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_As_I null (Msg port_i))\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) False)))\<cdot>(SenderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma step_3_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I null null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))"
  oops

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma step_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_As_I null null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))"
  oops

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_As_I null null)\<cdot>(SenderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) False)))\<cdot>(SenderStep (SenderState Sf var_buffer 3))"
  oops

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma step_4_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair port_i True)))\<cdot>(SenderStep (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma step_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) False)))\<cdot>(SenderStep (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) True)))\<cdot>(SenderStep (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma step_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair port_i False)))\<cdot>(SenderStep (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma step_5_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St var_buffer var_c))"
  oops

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma step_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last (butlast var_buffer)) False)))\<cdot>(SenderStep (SenderState Sf (butlast var_buffer) 3))"
  oops

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma step_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St var_buffer (var_c-1)))"
  oops

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) True)))\<cdot>(SenderStep (SenderState St var_buffer 3))"
  oops

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma step_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_As_I (Msg port_as) null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState Sf (butlast var_buffer) var_c))"
  oops

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma step_6_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I null (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair port_i True)))\<cdot>(SenderStep (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_As_I null (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_As_I null (Msg port_i))\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) True)))\<cdot>(SenderStep (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma step_7_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_As_I null null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St var_buffer var_c))"
  oops

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma step_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_As_I null null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds null)\<cdot>(SenderStep (SenderState St var_buffer (var_c-1)))"
  oops

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_As_I null null)\<cdot>(SenderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_Ds (Msg (Pair (last var_buffer) True)))\<cdot>(SenderStep (SenderState St var_buffer 3))"
  oops


end