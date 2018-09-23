(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 23, 2018 6:42:30 PM by isartransformer 1.0.0
 *)
theory MediumAutomaton
  imports bundle.tsynBundle automat.ndAutomaton

begin

(* TODO SWS: Move this to...? *)
setup_lifting type_definition_cfun

(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Datatype definition\<close>

datatype ('e::countable,'f::countable) mediumMessage = MediumE "'e" | MediumF "'f"

instance mediumMessage :: (countable, countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation mediumMessage :: (countable, countable) message
begin
  fun ctype_mediumMessage :: "channel \<Rightarrow> ('e::countable,'f::countable) mediumMessage set" where
  "ctype_mediumMessage c = (
    if c = \<C> ''ar'' then range MediumE else
    if c = \<C> ''ar2'' then range MediumF else
    if c = \<C> ''as'' then range MediumE else
    if c = \<C> ''as2'' then range MediumF else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition mediumElem_raw_ar :: "'e \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ar'' \<mapsto> Msg (MediumE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition mediumElem_raw_ar2 :: "'f \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ar2'' \<mapsto> Msg (MediumF x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition mediumElem_raw_as :: "'e \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''as'' \<mapsto> Msg (MediumE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition mediumElem_raw_as2 :: "'f \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''as2'' \<mapsto> Msg (MediumF x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun mediumElem_ar :: "'e tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" where
"mediumElem_ar (Msg port_ar) = mediumElem_raw_ar port_ar" |
"mediumElem_ar null = sbeNull {\<C> ''ar''}"

declare mediumElem_ar.simps[simp del]

definition medium_ar :: "'e tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_ar port_ar = sbe2SB (mediumElem_ar port_ar)"

fun mediumElem_ar2 :: "'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" where
"mediumElem_ar2 (Msg port_ar2) = mediumElem_raw_ar2 port_ar2" |
"mediumElem_ar2 null = sbeNull {\<C> ''ar2''}"

declare mediumElem_ar2.simps[simp del]

definition medium_ar2 :: "'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_ar2 port_ar2 = sbe2SB (mediumElem_ar2 port_ar2)"

fun mediumElem_as :: "'e tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" where
"mediumElem_as (Msg port_as) = mediumElem_raw_as port_as" |
"mediumElem_as null = sbeNull {\<C> ''as''}"

declare mediumElem_as.simps[simp del]

definition medium_as :: "'e tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_as port_as = sbe2SB (mediumElem_as port_as)"

fun mediumElem_as2 :: "'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" where
"mediumElem_as2 (Msg port_as2) = mediumElem_raw_as2 port_as2" |
"mediumElem_as2 null = sbeNull {\<C> ''as2''}"

declare mediumElem_as2.simps[simp del]

definition medium_as2 :: "'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_as2 port_as2 = sbe2SB (mediumElem_as2 port_as2)"

(* Create one sbElem for all input channels *)
definition mediumElemIn_ar_ar2 :: "'e tsyn \<Rightarrow> 'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" where
"mediumElemIn_ar_ar2 port_ar port_ar2 = (mediumElem_ar port_ar) \<plusminus> (mediumElem_ar2 port_ar2)"

(* Create one sbElem for all output channels *)
definition mediumElemOut_as_as2 :: "'e tsyn \<Rightarrow> 'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn sbElem" where
"mediumElemOut_as_as2 port_as port_as2 = (mediumElem_as port_as) \<plusminus> (mediumElem_as2 port_as2)"

(* Create one SB for all input channels *)
definition mediumIn_ar_ar2 :: "'e tsyn \<Rightarrow> 'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"mediumIn_ar_ar2 port_ar port_ar2 = (sbe2SB (mediumElemIn_ar_ar2 port_ar port_ar2))"

(* Create one SB for all output channels *)
definition mediumOut_as_as2 :: "'e tsyn \<Rightarrow> 'f tsyn \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"mediumOut_as_as2 port_as port_as2 = (sbe2SB (mediumElemOut_as_as2 port_as port_as2))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun medium_list_ar :: "('e tsyn) list \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_list_ar (x#xs) = ubConcEq (medium_ar x)\<cdot>(medium_list_ar xs)" |
"medium_list_ar []     = ubLeast {\<C> ''ar''}"

fun medium_list_ar2 :: "('f tsyn) list \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_list_ar2 (x#xs) = ubConcEq (medium_ar2 x)\<cdot>(medium_list_ar2 xs)" |
"medium_list_ar2 []     = ubLeast {\<C> ''ar2''}"

fun medium_list_as :: "('e tsyn) list \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_list_as (x#xs) = ubConcEq (medium_as x)\<cdot>(medium_list_as xs)" |
"medium_list_as []     = ubLeast {\<C> ''as''}"

fun medium_list_as2 :: "('f tsyn) list \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"medium_list_as2 (x#xs) = ubConcEq (medium_as2 x)\<cdot>(medium_list_as2 xs)" |
"medium_list_as2 []     = ubLeast {\<C> ''as2''}"

(* Create one SB for all input channels *)
definition mediumIn_list_ar_ar2 :: "'e tsyn list \<Rightarrow> 'f tsyn list \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"mediumIn_list_ar_ar2 port_ar port_ar2 = (medium_list_ar port_ar) \<uplus> (medium_list_ar2 port_ar2)"

(* Create one SB for all output channels *)
definition mediumOut_list_as_as2 :: "'e tsyn list \<Rightarrow> 'f tsyn list \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"mediumOut_list_as_as2 port_as port_as2 = (medium_list_as port_as) \<uplus> (medium_list_as2 port_as2)"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition medium_stream_ar_h :: "'e tsyn stream \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''ar'') \<mapsto> (tsynMap (MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition medium_stream_ar :: "('e) tsyn stream \<rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"medium_stream_ar_h"
  sorry

lift_definition medium_stream_ar2_h :: "'f tsyn stream \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''ar2'') \<mapsto> (tsynMap (MediumF)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition medium_stream_ar2 :: "('f) tsyn stream \<rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"medium_stream_ar2_h"
  sorry

lift_definition medium_stream_as_h :: "'e tsyn stream \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''as'') \<mapsto> (tsynMap (MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition medium_stream_as :: "('e) tsyn stream \<rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"medium_stream_as_h"
  sorry

lift_definition medium_stream_as2_h :: "'f tsyn stream \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''as2'') \<mapsto> (tsynMap (MediumF)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition medium_stream_as2 :: "('f) tsyn stream \<rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" is
"medium_stream_as2_h"
  sorry

(* Create one SB for all input channels *)
definition mediumIn_stream_ar_ar2 :: "'e tsyn stream \<rightarrow> 'f tsyn stream \<rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"mediumIn_stream_ar_ar2 = (\<Lambda>  port_ar port_ar2. (medium_stream_ar\<cdot>port_ar) \<uplus> (medium_stream_ar2\<cdot>port_ar2))"

(* Create one SB for all output channels *)
definition mediumOut_stream_as_as2 :: "'e tsyn stream \<rightarrow> 'f tsyn stream \<rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SB" where
"mediumOut_stream_as_as2 = (\<Lambda>  port_as port_as2. (medium_stream_as\<cdot>port_as) \<uplus> (medium_stream_as2\<cdot>port_as2))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun mediumElem_get_ar :: "('e::countable,'f::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_ar sbe = undefined"

lift_definition medium_get_stream_ar :: "('e::countable,'f::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv MediumE)\<cdot>(sb . (\<C> ''ar''))"
  by(simp add: cfun_def)

fun mediumElem_get_ar2 :: "('e::countable,'f::countable) mediumMessage tsyn sbElem \<Rightarrow> ('f) tsyn" where
"mediumElem_get_ar2 sbe = undefined"

lift_definition medium_get_stream_ar2 :: "('e::countable,'f::countable) mediumMessage tsyn SB \<rightarrow> 'f tsyn stream" is
"\<lambda>sb. tsynMap (inv MediumF)\<cdot>(sb . (\<C> ''ar2''))"
  by(simp add: cfun_def)

fun mediumElem_get_as :: "('e::countable,'f::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_as sbe = undefined"

lift_definition medium_get_stream_as :: "('e::countable,'f::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv MediumE)\<cdot>(sb . (\<C> ''as''))"
  by(simp add: cfun_def)

fun mediumElem_get_as2 :: "('e::countable,'f::countable) mediumMessage tsyn sbElem \<Rightarrow> ('f) tsyn" where
"mediumElem_get_as2 sbe = undefined"

lift_definition medium_get_stream_as2 :: "('e::countable,'f::countable) mediumMessage tsyn SB \<rightarrow> 'f tsyn stream" is
"\<lambda>sb. tsynMap (inv MediumF)\<cdot>(sb . (\<C> ''as2''))"
  by(simp add: cfun_def)



section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype MediumSubstate = Single

(* And these have also the variables *)
datatype 'k MediumState = MediumState MediumSubstate (* c = *) "'k"

(* Function to get the substate *)
fun getMediumSubState :: "'k MediumState \<Rightarrow> MediumSubstate" where
"getMediumSubState (MediumState s _) = s"

(* Functions to get the variables *)
fun getC :: "'k MediumState \<Rightarrow> 'k" where
"getC (MediumState _ var_c) = var_c"

(* Helper that allows us to utilize pattern matching *)
fun mediumTransitionH :: "('k MediumState \<times> ('e tsyn \<times> 'f tsyn)) \<Rightarrow> ('k MediumState \<times> ('e::countable,'f::countable) mediumMessage tsyn SB) set rev" where
"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>Msg port_ar, \<^cancel>\<open>ar2\<mapsto>\<close>Msg port_ar2)) =
  (Rev {(MediumState Single var_c, (mediumOut_as_as2 (Msg (port_ar)) (Msg (port_ar2)))) | var_c . (True)})" |

"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>Msg port_ar, \<^cancel>\<open>ar2\<mapsto>\<close>null)) =
  (Rev {(MediumState Single var_c, (mediumOut_as_as2 (Msg (port_ar)) null)) | var_c . (True)})" |

"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>null, \<^cancel>\<open>ar2\<mapsto>\<close>Msg port_ar2)) =
  (Rev {(MediumState Single var_c, (mediumOut_as_as2 null (Msg (port_ar2)))) | var_c . (True)})" |

"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>null, \<^cancel>\<open>ar2\<mapsto>\<close>null)) =
  (Rev {(MediumState Single var_c, (mediumOut_as_as2 null null)) | var_c . (True)})"

(* Domain *)
definition mediumDom :: "channel set" where
"mediumDom = {\<C> ''ar'', \<C> ''ar2''}"

(* Range *)
definition mediumRan :: "channel set" where
"mediumRan = {\<C> ''as'', \<C> ''as2''}"

(* Transition function *)
definition mediumTransition :: "('k MediumState \<times> ('e::countable,'f::countable) mediumMessage tsyn sbElem) \<Rightarrow> ('k MediumState \<times> ('e::countable,'f::countable) mediumMessage tsyn SB) set rev" where
"mediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then mediumTransitionH (s, (mediumElem_get_ar b, mediumElem_get_ar2 b)) else undefined))"

(* Initial states with initial outputs *)
definition mediumInitials :: "('k MediumState \<times> ('e::countable,'f::countable) mediumMessage tsyn SB) set rev" where
"mediumInitials = Rev (setflat\<cdot>{{(MediumState Single var_c, (mediumOut_as_as2 null null)) | var_c . (True)}})"

(* The final automaton *)
lift_definition mediumAutomaton :: "('k MediumState, ('e::countable,'f::countable) mediumMessage tsyn) ndAutomaton" is
"(mediumTransition, mediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition mediumStep :: "'k MediumState \<Rightarrow> ('e::countable,'f::countable) mediumMessage tsyn SPS" where
"mediumStep = nda_h mediumAutomaton"

(* The final SPF *)
definition mediumSPS :: "('e::countable,'f::countable) mediumMessage tsyn SPS" where
"mediumSPS = nda_H (mediumAutomaton::('k MediumState, ('e::countable,'f::countable) mediumMessage tsyn) ndAutomaton)"


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

lemma mediumelemin_ar_ar2_dom[simp]: "sbeDom (mediumElemIn_ar_ar2 port_ar port_ar2) = mediumDom"
  sorry

lemma mediumelemout_as_as2_dom[simp]: "sbeDom (mediumElemOut_as_as2 port_as port_as2) = mediumRan"
  sorry

lemma mediumin_ar_ar2_dom[simp]: "ubDom\<cdot>(mediumIn_ar_ar2 port_ar port_ar2) = mediumDom"
  sorry

lemma mediumout_as_as2_dom[simp]: "ubDom\<cdot>(mediumOut_as_as2 port_as port_as2) = mediumRan"
  sorry


section \<open>Lemmas for getter\<close>

subsection \<open>Identity lemmas for single sbElems\<close>

lemma mediumelem_ar_id[simp]: "mediumElem_get_ar (mediumElem_ar port_ar) = port_ar"
  sorry

lemma mediumelem_ar2_id[simp]: "mediumElem_get_ar2 (mediumElem_ar2 port_ar2) = port_ar2"
  sorry

lemma mediumelem_as_id[simp]: "mediumElem_get_as (mediumElem_as port_as) = port_as"
  sorry

lemma mediumelem_as2_id[simp]: "mediumElem_get_as2 (mediumElem_as2 port_as2) = port_as2"
  sorry


subsection \<open>Identity lemmas for single SBs from streams\<close>

lemma medium_stream_ar_id[simp]: "medium_get_stream_ar\<cdot>(medium_stream_ar\<cdot>port_ar) = port_ar"
  sorry

lemma medium_stream_ar2_id[simp]: "medium_get_stream_ar2\<cdot>(medium_stream_ar2\<cdot>port_ar2) = port_ar2"
  sorry

lemma medium_stream_as_id[simp]: "medium_get_stream_as\<cdot>(medium_stream_as\<cdot>port_as) = port_as"
  sorry

lemma medium_stream_as2_id[simp]: "medium_get_stream_as2\<cdot>(medium_stream_as2\<cdot>port_as2) = port_as2"
  sorry


subsection \<open>Identity lemmas for input sbElems\<close>

lemma mediumelemin_ar_ar2_ar_id[simp]: "mediumElem_get_ar (mediumElemIn_ar_ar2 port_ar port_ar2) = port_ar"
  sorry

lemma mediumelemin_ar_ar2_ar2_id[simp]: "mediumElem_get_ar2 (mediumElemIn_ar_ar2 port_ar port_ar2) = port_ar2"
  sorry


subsection \<open>Identity lemmas for output sbElems\<close>

lemma mediumelemout_as_as2_as_id[simp]: "mediumElem_get_as (mediumElemOut_as_as2 port_as port_as2) = port_as"
  sorry

lemma mediumelemout_as_as2_as2_id[simp]: "mediumElem_get_as2 (mediumElemOut_as_as2 port_as port_as2) = port_as2"
  sorry


subsection \<open>Identity lemmas for input SBs\<close>

lemma mediumin_ar_ar2_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_ar_ar2 port_ar port_ar2) = \<up>port_ar"
  sorry

lemma mediumin_ar_ar2_ar2_id[simp]: "medium_get_stream_ar2\<cdot>(mediumIn_ar_ar2 port_ar port_ar2) = \<up>port_ar2"
  sorry


subsection \<open>Identity lemmas for output SBs\<close>

lemma mediumout_as_as2_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_as_as2 port_as port_as2) = \<up>port_as"
  sorry

lemma mediumout_as_as2_as2_id[simp]: "medium_get_stream_as2\<cdot>(mediumOut_as_as2 port_as port_as2) = \<up>port_as2"
  sorry


subsection \<open>Identity lemmas for input SBs from lists\<close>

lemma mediumin_list_ar_ar2_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_list_ar_ar2 port_ar port_ar2) = <port_ar>"
  sorry

lemma mediumin_list_ar_ar2_ar2_id[simp]: "medium_get_stream_ar2\<cdot>(mediumIn_list_ar_ar2 port_ar port_ar2) = <port_ar2>"
  sorry


subsection \<open>Identity lemmas for output SBs from lists\<close>

lemma mediumout_list_as_as2_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_list_as_as2 port_as port_as2) = <port_as>"
  sorry

lemma mediumout_list_as_as2_as2_id[simp]: "medium_get_stream_as2\<cdot>(mediumOut_list_as_as2 port_as port_as2) = <port_as2>"
  sorry


subsection \<open>Identity lemmas for input SBs from streams\<close>

lemma mediumin_stream_ar_ar2_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_stream_ar_ar2\<cdot>port_ar\<cdot>port_ar2) = port_ar"
  sorry

lemma mediumin_stream_ar_ar2_ar2_id[simp]: "medium_get_stream_ar2\<cdot>(mediumIn_stream_ar_ar2\<cdot>port_ar\<cdot>port_ar2) = port_ar2"
  sorry


subsection \<open>Identity lemmas for output SBs from streams\<close>

lemma mediumout_stream_as_as2_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_stream_as_as2\<cdot>port_as\<cdot>port_as2) = port_as"
  sorry

lemma mediumout_stream_as_as2_as2_id[simp]: "medium_get_stream_as2\<cdot>(mediumOut_stream_as_as2\<cdot>port_as\<cdot>port_as2) = port_as2"
  sorry


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumTransition_0_0:
  assumes "True"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar_ar2 (Msg port_ar) (Msg port_ar2)))
         = (Rev {(MediumState Single var_c, (mediumOut_as_as2 (Msg (port_ar)) (Msg (port_ar2)))) | var_c . (True)})"
  oops

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumTransition_1_0:
  assumes "True"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar_ar2 (Msg port_ar) null))
         = (Rev {(MediumState Single var_c, (mediumOut_as_as2 (Msg (port_ar)) null)) | var_c . (True)})"
  oops

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumTransition_2_0:
  assumes "True"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar_ar2 null (Msg port_ar2)))
         = (Rev {(MediumState Single var_c, (mediumOut_as_as2 null (Msg (port_ar2)))) | var_c . (True)})"
  oops

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumTransition_3_0:
  assumes "True"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar_ar2 null null))
         = (Rev {(MediumState Single var_c, (mediumOut_as_as2 null null)) | var_c . (True)})"
  oops


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma mediumSps2Step: "mediumSPS = uspecFlatten mediumDom mediumRan
    (Rev {spsConcOut (mediumOut_as_as2 null null)\<cdot>(mediumStep (MediumState Single var_c)) | var_c . (True)})"
sorry

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumStep_0_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_ar_ar2 (Msg port_ar) (Msg port_ar2)) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as_as2 (Msg (port_ar)) (Msg (port_ar2)))\<cdot>(mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumStep_1_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_ar_ar2 (Msg port_ar) null) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as_as2 (Msg (port_ar)) null)\<cdot>(mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumStep_2_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_ar_ar2 null (Msg port_ar2)) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as_as2 null (Msg (port_ar2)))\<cdot>(mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops

(* Line 17:  Single / {c = rand {i. True}, as = ar, as2 = ar2}; *)
lemma mediumStep_3_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_ar_ar2 null null) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as_as2 null null)\<cdot>(mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops


end