(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 1, 2018 1:17:47 AM by isartransformer 1.0.0
 *)
theory MediumAutomaton
  imports bundle.tsynBundle automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Datatype definition\<close>

datatype ('e::countable) mediumMessage = DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE "'e"

instance mediumMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation mediumMessage :: (countable) message
begin
  fun ctype_mediumMessage :: "channel \<Rightarrow> ('e::countable) mediumMessage set" where
  "ctype_mediumMessage c = (
    if c = \<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar'' then range DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE else
    if c = \<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as'' then range DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Domain and range\<close>

definition mediumDom :: "channel set" where
"mediumDom = {\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar''}"

definition mediumRan :: "channel set" where
"mediumRan = {\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as''}"


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition mediumElem_raw_ar :: "'e \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar'' \<mapsto> Msg (DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition mediumElem_raw_as :: "'e \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as'' \<mapsto> Msg (DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun mediumElem_ar :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElem_ar (Msg port_ar) = mediumElem_raw_ar port_ar" |
"mediumElem_ar null = sbeNull {\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar''}"

declare mediumElem_ar.simps[simp del]

definition medium_ar :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_ar port_ar = sbe2SB (mediumElem_ar port_ar)"

fun mediumElem_as :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElem_as (Msg port_as) = mediumElem_raw_as port_as" |
"mediumElem_as null = sbeNull {\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as''}"

declare mediumElem_as.simps[simp del]

definition medium_as :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_as port_as = sbe2SB (mediumElem_as port_as)"

(* Create one sbElem for all input channels *)
definition mediumElemIn_ar :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElemIn_ar port_ar = (mediumElem_ar port_ar)"

(* Create one sbElem for all output channels *)
definition mediumElemOut_as :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElemOut_as port_as = (mediumElem_as port_as)"

(* Create one SB for all input channels *)
definition mediumIn_ar :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_ar port_ar = (sbe2SB (mediumElemIn_ar port_ar))"

(* Create one SB for all output channels *)
definition mediumOut_as :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_as port_as = (sbe2SB (mediumElemOut_as port_as))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun medium_list_ar :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_list_ar (x#xs) = ubConcEq (medium_ar x)\<cdot>(medium_list_ar xs)" |
"medium_list_ar []     = ubLeast {\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar''}"

declare medium_list_ar.simps[simp del]

fun medium_list_as :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_list_as (x#xs) = ubConcEq (medium_as x)\<cdot>(medium_list_as xs)" |
"medium_list_as []     = ubLeast {\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as''}"

declare medium_list_as.simps[simp del]

(* Create one SB for all input channels *)
fun mediumIn_list_ar :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_list_ar ((port_ar)#xs) = ubConcEq (mediumIn_ar port_ar)\<cdot>(mediumIn_list_ar xs)" |
"mediumIn_list_ar [] = ubLeast mediumDom"

(* Create one SB for all output channels *)
fun mediumOut_list_as :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_list_as ((port_as)#xs) = ubConcEq (mediumOut_as port_as)\<cdot>(mediumOut_list_as xs)" |
"mediumOut_list_as [] = ubLeast mediumRan"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition DoNotUse_07592f9396884104b3e743d922fc2e1c_medium_stream_ar_h :: "'e tsyn stream \<Rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar'') \<mapsto> (tsynMap (DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition medium_stream_ar :: "('e) tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"DoNotUse_07592f9396884104b3e743d922fc2e1c_medium_stream_ar_h"
  sorry

lift_definition DoNotUse_07592f9396884104b3e743d922fc2e1c_medium_stream_as_h :: "'e tsyn stream \<Rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as'') \<mapsto> (tsynMap (DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition medium_stream_as :: "('e) tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"DoNotUse_07592f9396884104b3e743d922fc2e1c_medium_stream_as_h"
  sorry

(* Create one SB for all input channels *)
definition mediumIn_stream_ar :: "'e tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_stream_ar = (\<Lambda>  port_ar. (medium_stream_ar\<cdot>port_ar))"

(* Create one SB for all output channels *)
definition mediumOut_stream_as :: "'e tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_stream_as = (\<Lambda>  port_as. (medium_stream_as\<cdot>port_as))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun mediumElem_get_ar :: "('e::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_ar sbe = undefined"

lift_definition medium_get_stream_ar :: "('e::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE)\<cdot>(sb . (\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_ar''))"
  by(simp add: cfun_def)

fun mediumElem_get_as :: "('e::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_as sbe = undefined"

lift_definition medium_get_stream_as :: "('e::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_07592f9396884104b3e743d922fc2e1c_MediumE)\<cdot>(sb . (\<C> ''DoNotUse_07592f9396884104b3e743d922fc2e1c_as''))"
  by(simp add: cfun_def)


section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype MediumSubstate = Single

(* And these have also the variables *)
datatype MediumState = MediumState MediumSubstate (* c = *) "nat"

(* Function to get the substate *)
fun getMediumSubState :: "MediumState \<Rightarrow> MediumSubstate" where
"getMediumSubState (MediumState s _) = s"

(* Functions to get the variables *)
fun getC :: "MediumState \<Rightarrow> nat" where
"getC (MediumState _ var_c) = var_c"

(* Helper that allows us to utilize pattern matching *)
fun mediumTransitionH :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>Msg port_ar)) =
  (if(var_c>0) then (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})
   else if(var_c=0) then (Rev {(MediumState Single var_c, (mediumOut_as (Msg (port_ar)))) | var_c . (True)})
   else (Rev {(MediumState Single var_c, (mediumOut_as null))}))" |

"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>null)) =
  (if(var_c>0) then (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})
   else if(var_c=0) then (Rev {(MediumState Single var_c, (mediumOut_as null)) | var_c . (True)})
   else (Rev {(MediumState Single var_c, (mediumOut_as null))}))"

(* Transition function *)
definition mediumTransition :: "(MediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then mediumTransitionH (s, (mediumElem_get_ar b)) else undefined))"

(* Initial states with initial outputs *)
definition mediumInitials :: "(MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumInitials = Rev (setflat\<cdot>{{(MediumState Single (var_c::nat), (mediumOut_as null)) | var_c . (True)}})"

(* The final automaton *)
lift_definition mediumAutomaton :: "(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(mediumTransition, mediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition mediumStep :: "MediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"mediumStep = nda_h mediumAutomaton"

(* The final SPS *)
definition mediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"mediumSPS = nda_H (mediumAutomaton::(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma mediumautomaton_trans[simp]: "ndaTransition\<cdot>mediumAutomaton = mediumTransition"
  sorry

lemma mediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>mediumAutomaton = mediumInitials"
  sorry

lemma mediumautomaton_dom[simp]: "ndaDom\<cdot>mediumAutomaton = mediumDom"
  sorry

lemma mediumautomaton_ran[simp]: "ndaRan\<cdot>mediumAutomaton = mediumRan"
  sorry


section \<open>Lemmas for single tsyn setter\<close>

lemma mediumelemin_ar_dom[simp]: "sbeDom (mediumElemIn_ar port_ar) = mediumDom"
  sorry

lemma mediumelemout_as_dom[simp]: "sbeDom (mediumElemOut_as port_as) = mediumRan"
  sorry

lemma mediumin_ar_dom[simp]: "ubDom\<cdot>(mediumIn_ar port_ar) = mediumDom"
  sorry

lemma mediumout_as_dom[simp]: "ubDom\<cdot>(mediumOut_as port_as) = mediumRan"
  sorry


section \<open>Lemmas for getter\<close>

subsection \<open>Identity lemmas for single sbElems\<close>

lemma mediumelem_ar_id[simp]: "mediumElem_get_ar (mediumElem_ar x) = x"
  sorry

lemma mediumelem_as_id[simp]: "mediumElem_get_as (mediumElem_as x) = x"
  sorry


subsection \<open>Identity lemmas for single SBs from streams\<close>

lemma medium_stream_ar_id[simp]: "medium_get_stream_ar\<cdot>(medium_stream_ar\<cdot>x) = x"
  sorry

lemma medium_stream_as_id[simp]: "medium_get_stream_as\<cdot>(medium_stream_as\<cdot>x) = x"
  sorry


subsection \<open>Identity lemmas for input sbElems\<close>

lemma mediumelemin_ar_ar_id[simp]: "mediumElem_get_ar (mediumElemIn_ar port_ar) = port_ar"
  sorry


subsection \<open>Identity lemmas for output sbElems\<close>

lemma mediumelemout_as_as_id[simp]: "mediumElem_get_as (mediumElemOut_as port_as) = port_as"
  sorry


subsection \<open>Identity lemmas for input SBs\<close>

lemma mediumin_ar_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_ar port_ar) = \<up>port_ar"
  sorry


subsection \<open>Identity lemmas for output SBs\<close>

lemma mediumout_as_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_as port_as) = \<up>port_as"
  sorry


subsection \<open>Identity lemmas for input SBs from streams\<close>

lemma mediumin_stream_ar_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_stream_ar\<cdot>port_ar) = port_ar"
  sorry


subsection \<open>Identity lemmas for output SBs from streams\<close>

lemma mediumout_stream_as_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_stream_as\<cdot>port_as) = port_as"
  sorry


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumTransition_0_0:
  assumes "var_c>0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar (Msg port_ar)))
         = (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})"
  oops

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumTransition_0_1:
  assumes "var_c=0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar (Msg port_ar)))
         = (Rev {(MediumState Single var_c, (mediumOut_as (Msg (port_ar)))) | var_c . (True)})"
  oops

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumTransition_1_0:
  assumes "var_c>0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar null))
         = (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})"
  oops

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumTransition_1_1:
  assumes "var_c=0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar null))
         = (Rev {(MediumState Single var_c, (mediumOut_as null)) | var_c . (True)})"
  oops


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma mediumSps2Step: "mediumSPS = uspecFlatten mediumDom mediumRan
    (Rev {spsConcOut (mediumOut_as null) (mediumStep (MediumState Single (var_c::nat))) | var_c . (True)})"
sorry

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumStep_0_0:
  assumes "var_c>0"
    shows "spsConcIn  (mediumIn_ar (Msg port_ar)) (mediumStep (MediumState Single var_c))
         = spsConcOut (mediumOut_as null) (mediumStep (MediumState Single (var_c-1)))"
  oops

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumStep_0_1:
  assumes "var_c=0"
    shows "spsConcIn  (mediumIn_ar (Msg port_ar)) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as (Msg (port_ar))) (mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumStep_1_0:
  assumes "var_c>0"
    shows "spsConcIn  (mediumIn_ar null) (mediumStep (MediumState Single var_c))
         = spsConcOut (mediumOut_as null) (mediumStep (MediumState Single (var_c-1)))"
  oops

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumStep_1_1:
  assumes "var_c=0"
    shows "spsConcIn  (mediumIn_ar null) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as null) (mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops


end