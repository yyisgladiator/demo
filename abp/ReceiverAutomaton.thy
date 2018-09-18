(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 18, 2018 2:23:42 PM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

(* TODO Das sollte vielleicht wo anders hin *)
(* SWS: Ja. Oder du verwendest einfach den "#" operator....  *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"

section \<open>Datatype definition\<close>

datatype receiverMessage = ReceiverPair_ReceiverNat_ReceiverBool "(nat\<times>bool)" | ReceiverBool "bool" | ReceiverNat "nat"
instance receiverMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation receiverMessage :: message
begin
  fun ctype_receiverMessage :: "channel  \<Rightarrow> receiverMessage set" where
  "ctype_receiverMessage c = (
    if c = \<C> ''dr'' then range ReceiverPair_ReceiverNat_ReceiverBool else
    if c = \<C> ''ar'' then range ReceiverBool else
    if c = \<C> ''o'' then range ReceiverNat else
    {})"
    instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition createDrBundle :: "(nat\<times>bool) \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''dr'' \<mapsto> Msg (ReceiverPair_ReceiverNat_ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createArBundle :: "bool \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ar'' \<mapsto> Msg (ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createOBundle :: "nat \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''o'' \<mapsto> Msg (ReceiverNat x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun createTsynDrBundle :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"createTsynDrBundle (Msg x) = (createDrBundle x)" |
"createTsynDrBundle null = (sbeNull {\<C> ''dr''})"
(* SWS: Delete From Simps, the user should NEVER have to look inside this *)
(* SWS: The function should use "sbElem" internally. Not actually return an sbElem *)

fun createTsynArBundle :: "bool tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"createTsynArBundle (Msg x) = (createArBundle x)" |
"createTsynArBundle null = (sbeNull {\<C> ''ar''})"

fun createTsynOBundle :: "nat tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"createTsynOBundle (Msg x) = (createOBundle x)" |
"createTsynOBundle null = (sbeNull {\<C> ''o''})"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun createLongDrBundle :: "((nat\<times>bool) tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"createLongDrBundle (x#xs) = ubConcEq (sbe2SB (createTsynDrBundle x))\<cdot>(createLongDrBundle xs)" |
"createLongDrBundle []     = ubLeast {\<C> ''dr''}"

fun createLongArBundle :: "(bool tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"createLongArBundle (x#xs) = ubConcEq (sbe2SB (createTsynArBundle x))\<cdot>(createLongArBundle xs)" |
"createLongArBundle []     = ubLeast {\<C> ''ar''}"

fun createLongOBundle :: "(nat tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"createLongOBundle (x#xs) = ubConcEq (sbe2SB (createTsynOBundle x))\<cdot>(createLongOBundle xs)" |
"createLongOBundle []     = ubLeast {\<C> ''o''}"

(* SWS: gerne auch getter und lemma über getter. Der "sbeGetter" soll dann in der transitions-function verwendet werden *)
(* SWS: Und die function die ein "nat tsyn stream" nimmt und ein O-Bundle daraus macht (analog alle anderen channels *)

section \<open>Lemmas for "createXBundle"\<close>

lemma createDrBundle_dom [simp]: "sbeDom (createDrBundle x) = {\<C> ''dr''}"  
  (* SWS: I don't want the user to see "{\<C> ''dr''}". That should be a new definition like "revAutDom" (similar to our medium) *)
  apply(simp add: sbeDom_def createDrBundle_def)
  using createDrBundle.abs_eq createDrBundle.rep_eq by auto

lemma createDrBundle_getch [simp]: "(sbe2SB (createDrBundle x)).(\<C> ''dr'') = \<up>(Msg (ReceiverPair_ReceiverNat_ReceiverBool x))"
  by (simp add: createDrBundle.rep_eq sbe2sb_getch)

lemma createDrBundle_len [simp]: "ubLen (sbe2SB (createDrBundle x)) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createArBundle_dom [simp]: "sbeDom (createArBundle x) = {\<C> ''ar''}"
  apply(simp add: sbeDom_def createArBundle_def)
  using createArBundle.abs_eq createArBundle.rep_eq by auto

lemma createArBundle_getch [simp]: "(sbe2SB (createArBundle x)).(\<C> ''ar'') = \<up>(Msg (ReceiverBool x))"
  by (simp add: createArBundle.rep_eq sbe2sb_getch)

lemma createArBundle_len [simp]: "ubLen (sbe2SB (createArBundle x)) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createOBundle_dom [simp]: "sbeDom (createOBundle x) = {\<C> ''o''}"
  apply(simp add: sbeDom_def createOBundle_def)
  using createOBundle.abs_eq createOBundle.rep_eq by auto

lemma createOBundle_getch [simp]: "(sbe2SB (createOBundle x)).(\<C> ''o'') = \<up>(Msg (ReceiverNat x))"
  by (simp add: createOBundle.rep_eq sbe2sb_getch)

lemma createOBundle_len [simp]: "ubLen (sbe2SB (createOBundle x)) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)


section \<open>Lemmas for "createTsynXBundle"\<close>

lemma createTsynDrBundle_dom [simp]: "sbeDom (createTsynDrBundle x) = {\<C> ''dr''}"
  by (cases x, simp_all)

lemma createTsynDrBundle_len [simp]: "ubLen (sbe2DB (createTsynDrBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynArBundle_dom [simp]: "sbeDom (createTsynArBundle x) = {\<C> ''ar''}"
  by (cases x, simp_all)

lemma createTsynArBundle_len [simp]: "ubLen (sbe2DB (createTsynArBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynOBundle_dom [simp]: "sbeDom (createTsynOBundle x) = {\<C> ''o''}"
  by (cases x, simp_all)

lemma createTsynOBundle_len [simp]: "ubLen (sbe2DB (createTsynOBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops


section \<open>Lemmas for "createLongXBundle"\<close>

lemma createLongDrBundle_dom [simp]: "ubDom\<cdot>(createLongDrBundle xs) = {\<C> ''dr''}"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons a _)
      then show ?case
        proof (cases a)
          case (Msg _) then show ?thesis by (simp add: Cons.IH)
        next
          case null then show ?thesis by (simp add: Cons.IH)
        qed
  qed

lemma createLongDrBundle_len [simp]: "ubLen (createLongDrBundle xs) = Fin (length xs)"
  oops

lemma createLongArBundle_dom [simp]: "ubDom\<cdot>(createLongArBundle xs) = {\<C> ''ar''}"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons a _)
      then show ?case
        proof (cases a)
          case (Msg _) then show ?thesis by (simp add: Cons.IH)
        next
          case null then show ?thesis by (simp add: Cons.IH)
        qed
  qed

lemma createLongArBundle_len [simp]: "ubLen (createLongArBundle xs) = Fin (length xs)"
  oops

lemma createLongOBundle_dom [simp]: "ubDom\<cdot>(createLongOBundle xs) = {\<C> ''o''}"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons a _)
      then show ?case
        proof (cases a)
          case (Msg _) then show ?thesis by (simp add: Cons.IH)
        next
          case null then show ?thesis by (simp add: Cons.IH)
        qed
  qed

lemma createLongOBundle_len [simp]: "ubLen (createLongOBundle xs) = Fin (length xs)"
  oops


section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = ReceiverState ReceiverSubstate 

(* Function to get the substate *)
fun getReceiverSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
"getReceiverSubState (ReceiverState s ) = s"

(* Helper that allows us to utilize pattern matching *)
fun receiverTransitionH :: "(ReceiverState \<times> (receiverMessage tsyn)) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
"receiverTransitionH (ReceiverState Rf, (\<^cancel>\<open>dr\<mapsto>\<close>Msg (ReceiverPair_ReceiverNat_ReceiverBool port_dr))) =
  (if((snd port_dr)=True) then ((ReceiverState Rf, (sbe2SB (createArBundle (True)) \<uplus> tsynbNull (\<C> ''o''))))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (sbe2SB (createArBundle (False)) \<uplus> sbe2SB (createOBundle ((fst port_dr))))))
   else (ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))))" |
(*SWS: Always use "createTsynOBundle" (or a renamed version) instead of the "tsynbNull" or "createOBundle" *)

"receiverTransitionH (ReceiverState Rf, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>Msg (ReceiverPair_ReceiverNat_ReceiverBool port_dr))) =
  (if((snd port_dr)=True) then ((ReceiverState Rf, (sbe2SB (createArBundle (True)) \<uplus> sbe2SB (createOBundle ((fst port_dr))))))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (sbe2SB (createArBundle (False)) \<uplus> tsynbNull (\<C> ''o''))))
   else (ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')))"

(* Transition function *)
fun receiverTransition :: "(ReceiverState \<times> receiverMessage tsyn sbElem) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
"receiverTransition (s,b) = (if (sbeDom b) = {\<C> ''dr''} then receiverTransitionH (s, (Rep_sbElem b\<rightharpoonup>\<C> ''dr'')) else undefined)"
(* SWS: Generate lemma for the transition function. Similar to the step-lemma (and that will be used in the step-lemma *)

lift_definition ReceiverAutomaton :: "(ReceiverState, receiverMessage tsyn) dAutomaton" is
"(receiverTransition, ReceiverState Rt , tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  by simp

(* SWS: in practice the user will always use "da_h ReceiverAutomaton". That can be autogenerated as well *)
definition ReceiverSPF :: "(receiverMessage tsyn, receiverMessage tsyn) SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"


section \<open>Lemmata for the transitions\<close>

(* Line 18 in the MAA model *)
(* SWS: can you add the actual line? *)
lemma tbd_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (sbe2SB (createDrBundle port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (sbe2SB (createArBundle (True)) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops
(*SWS: Always use "createTsynOBundle" (or a renamed version) instead of the "tsynbNull" or "createOBundle" *)


(* Line 19 in the MAA model *)
lemma tbd_0_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (sbe2SB (createDrBundle port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (sbe2SB (createArBundle (False)) \<uplus> sbe2SB (createOBundle ((fst port_dr))))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 17 in the MAA model *)
lemma tbd_1_0:
  assumes "True"
    shows "spfConcIn  (tsynbNull (\<C> ''dr''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 14 in the MAA model *)
lemma tbd_2_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (sbe2SB (createDrBundle port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (sbe2SB (createArBundle (True)) \<uplus> sbe2SB (createOBundle ((fst port_dr))))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 15 in the MAA model *)
lemma tbd_2_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (sbe2SB (createDrBundle port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (sbe2SB (createArBundle (False)) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 16 in the MAA model *)
lemma tbd_3_0:
  assumes "True"
    shows "spfConcIn  (tsynbNull (\<C> ''dr''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops


end