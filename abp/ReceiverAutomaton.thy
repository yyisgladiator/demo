(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 5, 2018 3:18:20 PM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

(* TODO Das sollte vielleicht wo anders hin *)
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

lift_definition createDrBundle :: "(nat\<times>bool) \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda>x. [\<C> ''dr'' \<mapsto> \<up>(Msg (ReceiverPair_ReceiverNat_ReceiverBool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createArBundle :: "bool \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda>x. [\<C> ''ar'' \<mapsto> \<up>(Msg (ReceiverBool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createOBundle :: "nat \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda>x. [\<C> ''o'' \<mapsto> \<up>(Msg (ReceiverNat x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun createTsynDrBundle :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn SB" where
"createTsynDrBundle (Msg x) = (createDrBundle x)" |
"createTsynDrBundle null = (tsynbNull (\<C> ''dr''))"

fun createTsynArBundle :: "bool tsyn \<Rightarrow> receiverMessage tsyn SB" where
"createTsynArBundle (Msg x) = (createArBundle x)" |
"createTsynArBundle null = (tsynbNull (\<C> ''ar''))"

fun createTsynOBundle :: "nat tsyn \<Rightarrow> receiverMessage tsyn SB" where
"createTsynOBundle (Msg x) = (createOBundle x)" |
"createTsynOBundle null = (tsynbNull (\<C> ''o''))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun createLongDrBundle :: "((nat\<times>bool) tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"createLongDrBundle (x#xs) = ubConcEq (createTsynDrBundle x)\<cdot>(createLongDrBundle xs)" |
"createLongDrBundle []     = ubLeast {\<C> ''dr''}"

fun createLongArBundle :: "(bool tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"createLongArBundle (x#xs) = ubConcEq (createTsynArBundle x)\<cdot>(createLongArBundle xs)" |
"createLongArBundle []     = ubLeast {\<C> ''ar''}"

fun createLongOBundle :: "(nat tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"createLongOBundle (x#xs) = ubConcEq (createTsynOBundle x)\<cdot>(createLongOBundle xs)" |
"createLongOBundle []     = ubLeast {\<C> ''o''}"


section \<open>Lemmas for "createXBundle"\<close>

lemma createDrBundle_dom [simp]: "ubDom\<cdot>(createDrBundle x) = {\<C> ''dr''}"
  by (simp add: createDrBundle.rep_eq ubdom_insert)

lemma createDrBundle_getch [simp]: "(createDrBundle x).(\<C> ''dr'') = \<up>(Msg (ReceiverPair_ReceiverNat_ReceiverBool x))"
  by (simp add: createDrBundle.rep_eq ubgetch_insert)

lemma createDrBundle_len [simp]: "ubLen (createDrBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createArBundle_dom [simp]: "ubDom\<cdot>(createArBundle x) = {\<C> ''ar''}"
  by (simp add: createArBundle.rep_eq ubdom_insert)

lemma createArBundle_getch [simp]: "(createArBundle x).(\<C> ''ar'') = \<up>(Msg (ReceiverBool x))"
  by (simp add: createArBundle.rep_eq ubgetch_insert)

lemma createArBundle_len [simp]: "ubLen (createArBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createOBundle_dom [simp]: "ubDom\<cdot>(createOBundle x) = {\<C> ''o''}"
  by (simp add: createOBundle.rep_eq ubdom_insert)

lemma createOBundle_getch [simp]: "(createOBundle x).(\<C> ''o'') = \<up>(Msg (ReceiverNat x))"
  by (simp add: createOBundle.rep_eq ubgetch_insert)

lemma createOBundle_len [simp]: "ubLen (createOBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)


section \<open>Lemmas for "createTsynXBundle"\<close>

lemma createTsynDrBundle_dom [simp]: "ubDom\<cdot>(createTsynDrBundle x) = {\<C> ''dr''}"
  by (cases x, simp_all)

lemma createTsynDrBundle_len [simp]: "ubLen (createTsynDrBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynArBundle_dom [simp]: "ubDom\<cdot>(createTsynArBundle x) = {\<C> ''ar''}"
  by (cases x, simp_all)

lemma createTsynArBundle_len [simp]: "ubLen (createTsynArBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynOBundle_dom [simp]: "ubDom\<cdot>(createTsynOBundle x) = {\<C> ''o''}"
  by (cases x, simp_all)

lemma createTsynOBundle_len [simp]: "ubLen (createTsynOBundle x) = Fin 1"
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
  (if((snd port_dr)=True) then ((ReceiverState Rf, (createArBundle (True) \<uplus> tsynbNull (\<C> ''o''))))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (createArBundle (False) \<uplus> createOBundle ((fst port_dr)))))
   else (ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))))" |

"receiverTransitionH (ReceiverState Rf, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>Msg (ReceiverPair_ReceiverNat_ReceiverBool port_dr))) =
  (if((snd port_dr)=True) then ((ReceiverState Rf, (createArBundle (True) \<uplus> createOBundle ((fst port_dr)))))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (createArBundle (False) \<uplus> tsynbNull (\<C> ''o''))))
   else (ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')))"

(* Transition function *)
fun receiverTransition :: "(ReceiverState \<times> receiverMessage tsyn sbElem) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
"receiverTransition (s,b) = (if dom(Rep_sbElem b) = {\<C> ''dr''} then receiverTransitionH (s, (Rep_sbElem b\<rightharpoonup>\<C> ''dr'')) else undefined)"

lift_definition ReceiverAutomaton :: "(ReceiverState, receiverMessage tsyn) dAutomaton" is
"(receiverTransition, ReceiverState Rt , tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  by simp

definition ReceiverSPF :: "receiverMessage tsyn SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"


section \<open>Lemmata for the transitions\<close>

(* Line 20 in the MAA model *)
lemma tbd_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (createDrBundle port_dr)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (createArBundle (True) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 21 in the MAA model *)
lemma tbd_0_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (createDrBundle port_dr)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (createArBundle (False) \<uplus> createOBundle ((fst port_dr)))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 19 in the MAA model *)
lemma tbd_1_0:
  assumes "True"
    shows "spfConcIn  (tsynbNull (\<C> ''dr''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 16 in the MAA model *)
lemma tbd_2_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (createDrBundle port_dr)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (createArBundle (True) \<uplus> createOBundle ((fst port_dr)))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 17 in the MAA model *)
lemma tbd_2_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (createDrBundle port_dr)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (createArBundle (False) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 18 in the MAA model *)
lemma tbd_3_0:
  assumes "True"
    shows "spfConcIn  (tsynbNull (\<C> ''dr''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops


end