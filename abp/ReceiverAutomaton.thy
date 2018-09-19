(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 19, 2018 11:04:38 PM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

(* Helper for easier generation *)
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

(* Create one sbElem for all input streams *)
fun createSbElem_Dr :: "((nat\<times>bool) tsyn) \<Rightarrow> (receiverMessage tsyn sbElem)" where
"createSbElem_Dr null = Abs_sbElem [\<C> ''dr'' \<mapsto> null]" |
"createSbElem_Dr (Msg port_dr) = Abs_sbElem [\<C> ''dr'' \<mapsto> Msg (ReceiverPair_ReceiverNat_ReceiverBool port_dr)]"

(* Create one SB for all input streams *)
fun createBundle_Dr :: "((nat\<times>bool) tsyn) \<Rightarrow> (receiverMessage tsyn SB)" where
"createBundle_Dr port_dr  = (sbe2SB (createSbElem_Dr port_dr ))"

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

fun createTsynDrBundle :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn SB" where
"createTsynDrBundle (Msg x) = sbe2SB (createDrBundle x)" |
"createTsynDrBundle null = sbe2SB (sbeNull {\<C> ''dr''})"

declare createTsynDrBundle.simps[simp del]

fun createTsynArBundle :: "bool tsyn \<Rightarrow> receiverMessage tsyn SB" where
"createTsynArBundle (Msg x) = sbe2SB (createArBundle x)" |
"createTsynArBundle null = sbe2SB (sbeNull {\<C> ''ar''})"

declare createTsynArBundle.simps[simp del]

fun createTsynOBundle :: "nat tsyn \<Rightarrow> receiverMessage tsyn SB" where
"createTsynOBundle (Msg x) = sbe2SB (createOBundle x)" |
"createTsynOBundle null = sbe2SB (sbeNull {\<C> ''o''})"

declare createTsynOBundle.simps[simp del]


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

lemma createDrBundle_dom [simp]: "sbeDom (createDrBundle x) = {\<C> ''dr''}"
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

lemma createTsynDrBundle_dom [simp]: "ubDom\<cdot>(createTsynDrBundle x) = {\<C> ''dr''}"
  by (cases x, simp_all add: createTsynDrBundle.simps)

lemma createTsynDrBundle_len [simp]: "ubLen (sbe2DB (createTsynDrBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynArBundle_dom [simp]: "ubDom\<cdot>(createTsynArBundle x) = {\<C> ''ar''}"
  by (cases x, simp_all add: createTsynArBundle.simps)

lemma createTsynArBundle_len [simp]: "ubLen (sbe2DB (createTsynArBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynOBundle_dom [simp]: "ubDom\<cdot>(createTsynOBundle x) = {\<C> ''o''}"
  by (cases x, simp_all add: createTsynOBundle.simps)

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

(* The final automaton *)
lift_definition ReceiverAutomaton :: "(ReceiverState, receiverMessage tsyn) dAutomaton" is
"(receiverTransition, ReceiverState Rt , tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  by simp

(* Stream processing function for each state (handy for step lemmata) *)
definition ReceiverStep :: "(ReceiverState \<Rightarrow> (receiverMessage tsyn, receiverMessage tsyn) SPF)" where
"ReceiverStep = da_h ReceiverAutomaton"

(* The final SPF *)
definition ReceiverSPF :: "(receiverMessage tsyn, receiverMessage tsyn) SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma transition_0_0:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rf ), (createSbElem_Dr (Msg port_dr)))
         = (ReceiverState Rf, (sbe2SB (createArBundle (True)) \<uplus> tsynbNull (\<C> ''o'')))"
  oops

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma transition_0_1:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rf ), (createSbElem_Dr (Msg port_dr)))
         = (ReceiverState Rt, (sbe2SB (createArBundle (False)) \<uplus> sbe2SB (createOBundle ((fst port_dr)))))"
  oops

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma transition_1_0:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rf ), (createSbElem_Dr null))
         = (ReceiverState Rf, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')))"
  oops

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma transition_2_0:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rt ), (createSbElem_Dr (Msg port_dr)))
         = (ReceiverState Rf, (sbe2SB (createArBundle (True)) \<uplus> sbe2SB (createOBundle ((fst port_dr)))))"
  oops

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma transition_2_1:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rt ), (createSbElem_Dr (Msg port_dr)))
         = (ReceiverState Rt, (sbe2SB (createArBundle (False)) \<uplus> tsynbNull (\<C> ''o'')))"
  oops

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma transition_3_0:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rt ), (createSbElem_Dr null))
         = (ReceiverState Rt, (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')))"
  oops


section \<open>Step-wise lemmata for the SPF\<close>

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma step_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (createBundle_Dr (Msg port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (sbe2SB (createArBundle (True)) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma step_0_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (createBundle_Dr (Msg port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (sbe2SB (createArBundle (False)) \<uplus> sbe2SB (createOBundle ((fst port_dr))))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma step_1_0:
  assumes "True"
    shows "spfConcIn  (createBundle_Dr null)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma step_2_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (createBundle_Dr (Msg port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (sbe2SB (createArBundle (True)) \<uplus> sbe2SB (createOBundle ((fst port_dr))))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rf))"
  oops

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma step_2_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (createBundle_Dr (Msg port_dr))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (sbe2SB (createArBundle (False)) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma step_3_0:
  assumes "True"
    shows "spfConcIn  (createBundle_Dr null)\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt ))
         = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(da_h ReceiverAutomaton (ReceiverState Rt))"
  oops


end