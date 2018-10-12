(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:28 PM by isartransformer 2.0.0
 *)
theory SenderAutomaton
  imports SenderDatatype SenderStates automat.dAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun senderTransitionH :: "('e SenderState \<times> (bool tsyn \<times> 'e tsyn)) \<Rightarrow> ('e SenderState \<times> ('e::countable) senderMessage tsyn SB)" where
"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i True)))))
   else if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) var_c, (senderOut_ds null)))
   else if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf var_buffer (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True)))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i False)))))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St var_buffer (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) var_c, (senderOut_ds null)))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St var_buffer (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))"

(* Transition function *)
definition senderTransition :: "('e SenderState \<times> ('e::countable) senderMessage tsyn sbElem) \<Rightarrow> ('e SenderState \<times> ('e::countable) senderMessage tsyn SB)" where
"senderTransition = (\<lambda> (s,b). (if (sbeDom b) = senderDom then senderTransitionH (s, (senderElem_get_as b, senderElem_get_i b)) else undefined))"

(* Initial state *)
definition senderInitialState :: "'e SenderState" where
"senderInitialState = SenderState St ([] ::'e list) (0::nat)"

(* Initial output *)
definition senderInitialOutput :: "('e::countable) senderMessage tsyn SB" where
"senderInitialOutput = senderOut_ds null"

(* The final automaton *)
lift_definition senderAutomaton :: "('e SenderState, ('e::countable) senderMessage tsyn) dAutomaton" is
"(senderTransition, senderInitialState, senderInitialOutput, senderDom, senderRan)"
  by (simp add: senderDom_def senderRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition senderStep :: "('e SenderState \<Rightarrow> (('e::countable) senderMessage tsyn, ('e::countable) senderMessage tsyn) SPF)" where
"senderStep = da_h senderAutomaton"

(* The final SPF *)
definition senderSPF :: "(('e::countable) senderMessage tsyn, ('e::countable) senderMessage tsyn) SPF" where
"senderSPF = da_H (senderAutomaton::('e SenderState, ('e::countable) senderMessage tsyn) dAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma senderautomaton_trans[simp]: "daTransition senderAutomaton = senderTransition"
  unfolding daTransition_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_initialstate[simp]: "daInitialState senderAutomaton = senderInitialState"
  unfolding daInitialState_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_initialoutput[simp]: "daInitialOutput senderAutomaton = senderInitialOutput"
  unfolding daInitialOutput_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_dom[simp]: "daDom senderAutomaton = senderDom"
  unfolding daDom_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_ran[simp]: "daRan senderAutomaton = senderRan"
  unfolding daRan_def
  by(simp add: senderAutomaton.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderTransition_0_0[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_0_1[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_0_2[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_0_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_0_4[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderTransition_1_0[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma senderTransition_1_1[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St (butlast var_buffer) var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderTransition_1_2[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma senderTransition_1_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_1_4[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_2_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_2_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_2_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma senderTransition_3_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma senderTransition_3_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_3_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_4_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderTransition_4_1[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_4_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_4_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_4_4[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderTransition_5_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderTransition_5_1[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma senderTransition_5_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_5_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma senderTransition_5_4[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_6_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_6_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_6_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma senderTransition_7_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma senderTransition_7_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_7_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)


section \<open>Step-wise lemmata for the SPF\<close>

(* Convert the SPF to step notation *)
lemma senderSpf2Step: "senderSPF = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St ([] ::'e::countable list) (0::nat)))"
  by(simp add: senderSPF_def da_H_def senderInitialOutput_def senderInitialState_def senderStep_def)

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderStep_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))\<cdot>(senderStep (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderStep_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i True)))\<cdot>(senderStep (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderStep_0_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderStep_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))\<cdot>(senderStep (SenderState St (butlast var_buffer) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma senderStep_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St (butlast var_buffer) var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderStep_1_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma senderStep_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderStep_2_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma senderStep_3_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma senderStep_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderStep_4_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderStep_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))\<cdot>(senderStep (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderStep_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i False)))\<cdot>(senderStep (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderStep_5_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderStep_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))\<cdot>(senderStep (SenderState Sf (butlast var_buffer) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma senderStep_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma senderStep_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf (butlast var_buffer) var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderStep_6_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma senderStep_7_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma senderStep_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)


end