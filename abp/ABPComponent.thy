(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 1, 2018 2:45:43 PM by isartransformer 1.0.0
 *)
theory ABPComponent
  imports SenderAutomaton MediumAutomaton ReceiverAutomaton spec.SPS

begin


(* Dummy *)
definition uspecComp :: "('m,'m) ufun uspec ⇒ ('m,'m) ufun uspec ⇒ ('m,'m) ufun uspec" (infixl "⨂" 50) where
"uspecComp S1 S2 ≡ undefined"

(* Dummy *)
definition uspecSerComp :: "('in,'m) ufun uspec ⇒ ('m,'out) ufun uspec ⇒ ('in,'out) ufun uspec" (infixl "○" 50) where
"uspecSerComp S1 S2 ≡ undefined"


section ‹Datatype definition›

datatype ('e::countable) abpMessage = DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE "'e" | DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool "bool" | DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool "('e×bool)"

instance abpMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: (countable) message
begin
  fun ctype_abpMessage :: "channel ⇒ ('e::countable) abpMessage set" where
  "ctype_abpMessage c = (
    if c = 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o'' then range DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE else
    if c = 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i'' then range DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE else
    if c = 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar'' then range DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool else
    if c = 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr'' then range DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool else
    if c = 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar'' then range DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool else
    if c = 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as'' then range DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool else
    undefined)"
  instance
    by(intro_classes)
end


section ‹Domain and range›

definition aBPDom :: "channel set" where
"aBPDom = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''}"

definition aBPRan :: "channel set" where
"aBPRan = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''}"


subsection ‹sender›

definition aBPSenderDom :: "channel set" where
"aBPSenderDom = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as'', 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''}"

definition aBPSenderRan :: "channel set" where
"aBPSenderRan = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''}"


subsection ‹mediumSr›

definition aBPMediumSrDom :: "channel set" where
"aBPMediumSrDom = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''}"

definition aBPMediumSrRan :: "channel set" where
"aBPMediumSrRan = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''}"


subsection ‹receiver›

definition aBPReceiverDom :: "channel set" where
"aBPReceiverDom = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''}"

definition aBPReceiverRan :: "channel set" where
"aBPReceiverRan = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar'', 𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''}"


subsection ‹mediumRs›

definition aBPMediumRsDom :: "channel set" where
"aBPMediumRsDom = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar''}"

definition aBPMediumRsRan :: "channel set" where
"aBPMediumRsRan = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as''}"


section ‹Helpers to create a bundle from a single raw element›

lift_definition aBPElem_raw_receiver_o__o :: "'e ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o'' ↦ Msg (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_i__sender_i :: "'e ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i'' ↦ Msg (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_sender_ds__mediumSr_ar :: "('e×bool) ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar'' ↦ Msg (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_mediumSr_as__receiver_dr :: "('e×bool) ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr'' ↦ Msg (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_receiver_ar__mediumRs_ar :: "bool ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar'' ↦ Msg (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_mediumRs_as__sender_as :: "bool ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as'' ↦ Msg (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section ‹Helpers to create a bundle from a single tsyn element›

fun aBPElem_receiver_o__o :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_receiver_o__o (Msg receiver_port_o__port_o) = aBPElem_raw_receiver_o__o receiver_port_o__port_o" |
"aBPElem_receiver_o__o null = sbeNull {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''}"

declare aBPElem_receiver_o__o.simps[simp del]

definition aBP_receiver_o__o :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_receiver_o__o receiver_port_o__port_o = sbe2SB (aBPElem_receiver_o__o receiver_port_o__port_o)"

fun aBPElem_i__sender_i :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_i__sender_i (Msg port_i__sender_port_i) = aBPElem_raw_i__sender_i port_i__sender_port_i" |
"aBPElem_i__sender_i null = sbeNull {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''}"

declare aBPElem_i__sender_i.simps[simp del]

definition aBP_i__sender_i :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_i__sender_i port_i__sender_port_i = sbe2SB (aBPElem_i__sender_i port_i__sender_port_i)"

fun aBPElem_sender_ds__mediumSr_ar :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_sender_ds__mediumSr_ar (Msg sender_port_ds__mediumSr_port_ar) = aBPElem_raw_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar" |
"aBPElem_sender_ds__mediumSr_ar null = sbeNull {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''}"

declare aBPElem_sender_ds__mediumSr_ar.simps[simp del]

definition aBP_sender_ds__mediumSr_ar :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar = sbe2SB (aBPElem_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar)"

fun aBPElem_mediumSr_as__receiver_dr :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_mediumSr_as__receiver_dr (Msg mediumSr_port_as__receiver_port_dr) = aBPElem_raw_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr" |
"aBPElem_mediumSr_as__receiver_dr null = sbeNull {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''}"

declare aBPElem_mediumSr_as__receiver_dr.simps[simp del]

definition aBP_mediumSr_as__receiver_dr :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr = sbe2SB (aBPElem_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr)"

fun aBPElem_receiver_ar__mediumRs_ar :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_receiver_ar__mediumRs_ar (Msg receiver_port_ar__mediumRs_port_ar) = aBPElem_raw_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar" |
"aBPElem_receiver_ar__mediumRs_ar null = sbeNull {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar''}"

declare aBPElem_receiver_ar__mediumRs_ar.simps[simp del]

definition aBP_receiver_ar__mediumRs_ar :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar = sbe2SB (aBPElem_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar)"

fun aBPElem_mediumRs_as__sender_as :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_mediumRs_as__sender_as (Msg mediumRs_port_as__sender_port_as) = aBPElem_raw_mediumRs_as__sender_as mediumRs_port_as__sender_port_as" |
"aBPElem_mediumRs_as__sender_as null = sbeNull {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as''}"

declare aBPElem_mediumRs_as__sender_as.simps[simp del]

definition aBP_mediumRs_as__sender_as :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_mediumRs_as__sender_as mediumRs_port_as__sender_port_as = sbe2SB (aBPElem_mediumRs_as__sender_as mediumRs_port_as__sender_port_as)"

(* Create one sbElem for all input channels *)
definition aBPElemIn_i :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElemIn_i port_i = (aBPElem_i__sender_i port_i)"

(* Create one sbElem for all output channels *)
definition aBPElemOut_o :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElemOut_o port_o = (aBPElem_receiver_o__o port_o)"

(* Create one SB for all input channels *)
definition aBPIn_i :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPIn_i port_i = (sbe2SB (aBPElemIn_i port_i))"

(* Create one SB for all output channels *)
definition aBPOut_o :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPOut_o port_o = (sbe2SB (aBPElemOut_o port_o))"


subsection ‹sender›

(* Create one sbElem for all input channels *)
definition aBPSenderElemIn_as_i :: "bool tsyn ⇒ 'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPSenderElemIn_as_i port_as port_i = (aBPElem_mediumRs_as__sender_as port_as) ± (aBPElem_i__sender_i port_i)"

(* Create one sbElem for all output channels *)
definition aBPSenderElemOut_ds :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPSenderElemOut_ds port_ds = (aBPElem_sender_ds__mediumSr_ar port_ds)"

(* Create one SB for all input channels *)
definition aBPSenderIn_as_i :: "bool tsyn ⇒ 'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPSenderIn_as_i port_as port_i = (sbe2SB (aBPSenderElemIn_as_i port_as port_i))"

(* Create one SB for all output channels *)
definition aBPSenderOut_ds :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPSenderOut_ds port_ds = (sbe2SB (aBPSenderElemOut_ds port_ds))"


subsection ‹mediumSr›

(* Create one sbElem for all input channels *)
definition aBPMediumSrElemIn_ar :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumSrElemIn_ar port_ar = (aBPElem_sender_ds__mediumSr_ar port_ar)"

(* Create one sbElem for all output channels *)
definition aBPMediumSrElemOut_as :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumSrElemOut_as port_as = (aBPElem_mediumSr_as__receiver_dr port_as)"

(* Create one SB for all input channels *)
definition aBPMediumSrIn_ar :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrIn_ar port_ar = (sbe2SB (aBPMediumSrElemIn_ar port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumSrOut_as :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrOut_as port_as = (sbe2SB (aBPMediumSrElemOut_as port_as))"


subsection ‹receiver›

(* Create one sbElem for all input channels *)
definition aBPReceiverElemIn_dr :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPReceiverElemIn_dr port_dr = (aBPElem_mediumSr_as__receiver_dr port_dr)"

(* Create one sbElem for all output channels *)
definition aBPReceiverElemOut_ar_o :: "bool tsyn ⇒ 'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPReceiverElemOut_ar_o port_ar port_o = (aBPElem_receiver_ar__mediumRs_ar port_ar) ± (aBPElem_receiver_o__o port_o)"

(* Create one SB for all input channels *)
definition aBPReceiverIn_dr :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPReceiverIn_dr port_dr = (sbe2SB (aBPReceiverElemIn_dr port_dr))"

(* Create one SB for all output channels *)
definition aBPReceiverOut_ar_o :: "bool tsyn ⇒ 'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPReceiverOut_ar_o port_ar port_o = (sbe2SB (aBPReceiverElemOut_ar_o port_ar port_o))"


subsection ‹mediumRs›

(* Create one sbElem for all input channels *)
definition aBPMediumRsElemIn_ar :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumRsElemIn_ar port_ar = (aBPElem_receiver_ar__mediumRs_ar port_ar)"

(* Create one sbElem for all output channels *)
definition aBPMediumRsElemOut_as :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumRsElemOut_as port_as = (aBPElem_mediumRs_as__sender_as port_as)"

(* Create one SB for all input channels *)
definition aBPMediumRsIn_ar :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsIn_ar port_ar = (sbe2SB (aBPMediumRsElemIn_ar port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumRsOut_as :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsOut_as port_as = (sbe2SB (aBPMediumRsElemOut_as port_as))"


section ‹Helpers to create a bundle from a tsyn list of elements›

fun aBP_list_receiver_o__o :: "('e tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_list_receiver_o__o (x#xs) = ubConcEq (aBP_receiver_o__o x)⋅(aBP_list_receiver_o__o xs)" |
"aBP_list_receiver_o__o []     = ubLeast {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''}"

declare aBP_list_receiver_o__o.simps[simp del]

fun aBP_list_i__sender_i :: "('e tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_list_i__sender_i (x#xs) = ubConcEq (aBP_i__sender_i x)⋅(aBP_list_i__sender_i xs)" |
"aBP_list_i__sender_i []     = ubLeast {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''}"

declare aBP_list_i__sender_i.simps[simp del]

fun aBP_list_sender_ds__mediumSr_ar :: "(('e×bool) tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_list_sender_ds__mediumSr_ar (x#xs) = ubConcEq (aBP_sender_ds__mediumSr_ar x)⋅(aBP_list_sender_ds__mediumSr_ar xs)" |
"aBP_list_sender_ds__mediumSr_ar []     = ubLeast {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''}"

declare aBP_list_sender_ds__mediumSr_ar.simps[simp del]

fun aBP_list_mediumSr_as__receiver_dr :: "(('e×bool) tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_list_mediumSr_as__receiver_dr (x#xs) = ubConcEq (aBP_mediumSr_as__receiver_dr x)⋅(aBP_list_mediumSr_as__receiver_dr xs)" |
"aBP_list_mediumSr_as__receiver_dr []     = ubLeast {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''}"

declare aBP_list_mediumSr_as__receiver_dr.simps[simp del]

fun aBP_list_receiver_ar__mediumRs_ar :: "(bool tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_list_receiver_ar__mediumRs_ar (x#xs) = ubConcEq (aBP_receiver_ar__mediumRs_ar x)⋅(aBP_list_receiver_ar__mediumRs_ar xs)" |
"aBP_list_receiver_ar__mediumRs_ar []     = ubLeast {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar''}"

declare aBP_list_receiver_ar__mediumRs_ar.simps[simp del]

fun aBP_list_mediumRs_as__sender_as :: "(bool tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_list_mediumRs_as__sender_as (x#xs) = ubConcEq (aBP_mediumRs_as__sender_as x)⋅(aBP_list_mediumRs_as__sender_as xs)" |
"aBP_list_mediumRs_as__sender_as []     = ubLeast {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as''}"

declare aBP_list_mediumRs_as__sender_as.simps[simp del]

(* Create one SB for all input channels *)
fun aBPIn_list_i :: "('e tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPIn_list_i ((port_i)#xs) = ubConcEq (aBPIn_i port_i)⋅(aBPIn_list_i xs)" |
"aBPIn_list_i [] = ubLeast aBPDom"

(* Create one SB for all output channels *)
fun aBPOut_list_o :: "('e tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPOut_list_o ((port_o)#xs) = ubConcEq (aBPOut_o port_o)⋅(aBPOut_list_o xs)" |
"aBPOut_list_o [] = ubLeast aBPRan"


subsection ‹sender›

(* Create one SB for all input channels *)
fun aBPSenderIn_list_as_i :: "(bool tsyn×'e tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPSenderIn_list_as_i ((port_as,port_i)#xs) = ubConcEq (aBPSenderIn_as_i port_as port_i)⋅(aBPSenderIn_list_as_i xs)" |
"aBPSenderIn_list_as_i [] = ubLeast aBPSenderDom"

(* Create one SB for all output channels *)
fun aBPSenderOut_list_ds :: "(('e×bool) tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPSenderOut_list_ds ((port_ds)#xs) = ubConcEq (aBPSenderOut_ds port_ds)⋅(aBPSenderOut_list_ds xs)" |
"aBPSenderOut_list_ds [] = ubLeast aBPSenderRan"


subsection ‹mediumSr›

(* Create one SB for all input channels *)
fun aBPMediumSrIn_list_ar :: "(('e×bool) tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrIn_list_ar ((port_ar)#xs) = ubConcEq (aBPMediumSrIn_ar port_ar)⋅(aBPMediumSrIn_list_ar xs)" |
"aBPMediumSrIn_list_ar [] = ubLeast aBPMediumSrDom"

(* Create one SB for all output channels *)
fun aBPMediumSrOut_list_as :: "(('e×bool) tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrOut_list_as ((port_as)#xs) = ubConcEq (aBPMediumSrOut_as port_as)⋅(aBPMediumSrOut_list_as xs)" |
"aBPMediumSrOut_list_as [] = ubLeast aBPMediumSrRan"


subsection ‹receiver›

(* Create one SB for all input channels *)
fun aBPReceiverIn_list_dr :: "(('e×bool) tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPReceiverIn_list_dr ((port_dr)#xs) = ubConcEq (aBPReceiverIn_dr port_dr)⋅(aBPReceiverIn_list_dr xs)" |
"aBPReceiverIn_list_dr [] = ubLeast aBPReceiverDom"

(* Create one SB for all output channels *)
fun aBPReceiverOut_list_ar_o :: "(bool tsyn×'e tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPReceiverOut_list_ar_o ((port_ar,port_o)#xs) = ubConcEq (aBPReceiverOut_ar_o port_ar port_o)⋅(aBPReceiverOut_list_ar_o xs)" |
"aBPReceiverOut_list_ar_o [] = ubLeast aBPReceiverRan"


subsection ‹mediumRs›

(* Create one SB for all input channels *)
fun aBPMediumRsIn_list_ar :: "(bool tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsIn_list_ar ((port_ar)#xs) = ubConcEq (aBPMediumRsIn_ar port_ar)⋅(aBPMediumRsIn_list_ar xs)" |
"aBPMediumRsIn_list_ar [] = ubLeast aBPMediumRsDom"

(* Create one SB for all output channels *)
fun aBPMediumRsOut_list_as :: "(bool tsyn) list ⇒ ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsOut_list_as ((port_as)#xs) = ubConcEq (aBPMediumRsOut_as port_as)⋅(aBPMediumRsOut_list_as xs)" |
"aBPMediumRsOut_list_as [] = ubLeast aBPMediumRsRan"


section ‹Helpers to create a bundle from a tsyn stream of elements›

lift_definition DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_o__o_h :: "'e tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o'') ↦ (tsynMap (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto (* TODO War angeblich mal fertig, hat jetzt aber noch ein Goal *)
  sorry

lift_definition aBP_stream_receiver_o__o :: "('e) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_o__o_h"
  apply(auto simp add: cfun_def DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_o__o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_o__o_h.rep_eq ubrep_well)

lift_definition DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_i__sender_i_h :: "'e tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i'') ↦ (tsynMap (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto (* TODO War angeblich mal fertig, hat jetzt aber noch ein Goal *)
  sorry

lift_definition aBP_stream_i__sender_i :: "('e) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_i__sender_i_h"
  apply(auto simp add: cfun_def DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_i__sender_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_i__sender_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_sender_ds__mediumSr_ar_h :: "('e×bool) tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar'') ↦ (tsynMap (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto (* TODO War angeblich mal fertig, hat jetzt aber noch ein Goal *)
  sorry

lift_definition aBP_stream_sender_ds__mediumSr_ar :: "(('e×bool)) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_sender_ds__mediumSr_ar_h"
  apply(auto simp add: cfun_def DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_sender_ds__mediumSr_ar_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_sender_ds__mediumSr_ar_h.rep_eq ubrep_well)

lift_definition DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumSr_as__receiver_dr_h :: "('e×bool) tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr'') ↦ (tsynMap (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto (* TODO War angeblich mal fertig, hat jetzt aber noch ein Goal *)
  sorry

lift_definition aBP_stream_mediumSr_as__receiver_dr :: "(('e×bool)) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumSr_as__receiver_dr_h"
  apply(auto simp add: cfun_def DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumSr_as__receiver_dr_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumSr_as__receiver_dr_h.rep_eq ubrep_well)

lift_definition DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_ar__mediumRs_ar_h :: "bool tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar'') ↦ (tsynMap (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto (* TODO War angeblich mal fertig, hat jetzt aber noch ein Goal *)
  sorry

lift_definition aBP_stream_receiver_ar__mediumRs_ar :: "(bool) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_ar__mediumRs_ar_h"
  apply(auto simp add: cfun_def DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_ar__mediumRs_ar_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_receiver_ar__mediumRs_ar_h.rep_eq ubrep_well)

lift_definition DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumRs_as__sender_as_h :: "bool tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as'') ↦ (tsynMap (DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto (* TODO War angeblich mal fertig, hat jetzt aber noch ein Goal *)
  sorry

lift_definition aBP_stream_mediumRs_as__sender_as :: "(bool) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumRs_as__sender_as_h"
  apply(auto simp add: cfun_def DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumRs_as__sender_as_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_aBP_stream_mediumRs_as__sender_as_h.rep_eq ubrep_well)

(* Create one SB for all input channels *)
definition aBPIn_stream_i :: "'e tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPIn_stream_i = (Λ  port_i. (aBP_stream_i__sender_i⋅port_i))"

(* Create one SB for all output channels *)
definition aBPOut_stream_o :: "'e tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPOut_stream_o = (Λ  port_o. (aBP_stream_receiver_o__o⋅port_o))"


subsection ‹sender›

(* Create one SB for all input channels *)
definition aBPSenderIn_stream_as_i :: "bool tsyn stream → 'e tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPSenderIn_stream_as_i = (Λ  port_as port_i. (aBP_stream_mediumRs_as__sender_as⋅port_as) ⊎ (aBP_stream_i__sender_i⋅port_i))"

(* Create one SB for all output channels *)
definition aBPSenderOut_stream_ds :: "('e×bool) tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPSenderOut_stream_ds = (Λ  port_ds. (aBP_stream_sender_ds__mediumSr_ar⋅port_ds))"


subsection ‹mediumSr›

(* Create one SB for all input channels *)
definition aBPMediumSrIn_stream_ar :: "('e×bool) tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrIn_stream_ar = (Λ  port_ar. (aBP_stream_sender_ds__mediumSr_ar⋅port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumSrOut_stream_as :: "('e×bool) tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrOut_stream_as = (Λ  port_as. (aBP_stream_mediumSr_as__receiver_dr⋅port_as))"


subsection ‹receiver›

(* Create one SB for all input channels *)
definition aBPReceiverIn_stream_dr :: "('e×bool) tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPReceiverIn_stream_dr = (Λ  port_dr. (aBP_stream_mediumSr_as__receiver_dr⋅port_dr))"

(* Create one SB for all output channels *)
definition aBPReceiverOut_stream_ar_o :: "bool tsyn stream → 'e tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPReceiverOut_stream_ar_o = (Λ  port_ar port_o. (aBP_stream_receiver_ar__mediumRs_ar⋅port_ar) ⊎ (aBP_stream_receiver_o__o⋅port_o))"


subsection ‹mediumRs›

(* Create one SB for all input channels *)
definition aBPMediumRsIn_stream_ar :: "bool tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsIn_stream_ar = (Λ  port_ar. (aBP_stream_receiver_ar__mediumRs_ar⋅port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumRsOut_stream_as :: "bool tsyn stream → ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsOut_stream_as = (Λ  port_as. (aBP_stream_mediumRs_as__sender_as⋅port_as))"


section ‹Helpers to get tsyn elements and streams from sbElems and SBs›

definition aBPElem_get_receiver_o__o :: "('e::countable) abpMessage tsyn sbElem ⇒ ('e) tsyn" where
"aBPElem_get_receiver_o__o sbe = tsynApplyElem (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE) ((Rep_sbElem sbe) ⇀ (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''))"

lift_definition aBP_get_stream_receiver_o__o :: "('e::countable) abpMessage tsyn SB → 'e tsyn stream" is
"λsb. tsynMap (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE)⋅(sb . (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''))"
  by(simp add: cfun_def)

definition aBPElem_get_i__sender_i :: "('e::countable) abpMessage tsyn sbElem ⇒ ('e) tsyn" where
"aBPElem_get_i__sender_i sbe = tsynApplyElem (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE) ((Rep_sbElem sbe) ⇀ (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''))"

lift_definition aBP_get_stream_i__sender_i :: "('e::countable) abpMessage tsyn SB → 'e tsyn stream" is
"λsb. tsynMap (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPE)⋅(sb . (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''))"
  by(simp add: cfun_def)

definition aBPElem_get_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn sbElem ⇒ (('e×bool)) tsyn" where
"aBPElem_get_sender_ds__mediumSr_ar sbe = tsynApplyElem (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool) ((Rep_sbElem sbe) ⇀ (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''))"

lift_definition aBP_get_stream_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn SB → ('e×bool) tsyn stream" is
"λsb. tsynMap (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool)⋅(sb . (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''))"
  by(simp add: cfun_def)

definition aBPElem_get_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn sbElem ⇒ (('e×bool)) tsyn" where
"aBPElem_get_mediumSr_as__receiver_dr sbe = tsynApplyElem (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool) ((Rep_sbElem sbe) ⇀ (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''))"

lift_definition aBP_get_stream_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn SB → ('e×bool) tsyn stream" is
"λsb. tsynMap (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPPair_E_Bool)⋅(sb . (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''))"
  by(simp add: cfun_def)

definition aBPElem_get_receiver_ar__mediumRs_ar :: "('e::countable) abpMessage tsyn sbElem ⇒ (bool) tsyn" where
"aBPElem_get_receiver_ar__mediumRs_ar sbe = tsynApplyElem (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool) ((Rep_sbElem sbe) ⇀ (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar''))"

lift_definition aBP_get_stream_receiver_ar__mediumRs_ar :: "('e::countable) abpMessage tsyn SB → bool tsyn stream" is
"λsb. tsynMap (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool)⋅(sb . (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar''))"
  by(simp add: cfun_def)

definition aBPElem_get_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn sbElem ⇒ (bool) tsyn" where
"aBPElem_get_mediumRs_as__sender_as sbe = tsynApplyElem (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool) ((Rep_sbElem sbe) ⇀ (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as''))"

lift_definition aBP_get_stream_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn SB → bool tsyn stream" is
"λsb. tsynMap (inv DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_ABPBool)⋅(sb . (𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as''))"
  by(simp add: cfun_def)


section ‹Converter›


subsection ‹sender›

lift_definition senderInConvert :: "('e::countable) abpMessage tsyn SB → ('e) senderMessage tsyn SB" is
"λsb. senderIn_stream_as_i⋅(aBP_get_stream_mediumRs_as__sender_as⋅sb)⋅(aBP_get_stream_i__sender_i⋅sb)"
  by (simp add: cfun_def)

lift_definition senderOutConvert :: "('e) senderMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPSenderOut_stream_ds⋅(sender_get_stream_ds⋅sb)"
  by (simp add: cfun_def)

definition senderInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ ('e) senderMessage tsyn SB" where
"senderInConverterSPF = ufLift aBPSenderDom senderInConvert"

definition senderOutConverterSPF :: "('e) senderMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" where
"senderOutConverterSPF = ufLift aBPSenderRan senderOutConvert"


subsection ‹mediumSr›

lift_definition mediumSrInConvert :: "('e::countable) abpMessage tsyn SB → (('e×bool)) mediumMessage tsyn SB" is
"λsb. mediumIn_stream_ar⋅(aBP_get_stream_sender_ds__mediumSr_ar⋅sb)"
  by (simp add: cfun_def)

lift_definition mediumSrOutConvert :: "(('e×bool)) mediumMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPMediumSrOut_stream_as⋅(medium_get_stream_as⋅sb)"
  by (simp add: cfun_def)

definition mediumSrInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ (('e×bool)) mediumMessage tsyn SB" where
"mediumSrInConverterSPF = ufLift aBPMediumSrDom mediumSrInConvert"

definition mediumSrOutConverterSPF :: "(('e×bool)) mediumMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" where
"mediumSrOutConverterSPF = ufLift aBPMediumSrRan mediumSrOutConvert"


subsection ‹receiver›

lift_definition receiverInConvert :: "('e::countable) abpMessage tsyn SB → ('e) receiverMessage tsyn SB" is
"λsb. receiverIn_stream_dr⋅(aBP_get_stream_mediumSr_as__receiver_dr⋅sb)"
  by (simp add: cfun_def)

lift_definition receiverOutConvert :: "('e) receiverMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPReceiverOut_stream_ar_o⋅(receiver_get_stream_ar⋅sb)⋅(receiver_get_stream_o⋅sb)"
  by (simp add: cfun_def)

definition receiverInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ ('e) receiverMessage tsyn SB" where
"receiverInConverterSPF = ufLift aBPReceiverDom receiverInConvert"

definition receiverOutConverterSPF :: "('e) receiverMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" where
"receiverOutConverterSPF = ufLift aBPReceiverRan receiverOutConvert"


subsection ‹mediumRs›

lift_definition mediumRsInConvert :: "('e::countable) abpMessage tsyn SB → (bool) mediumMessage tsyn SB" is
"λsb. mediumIn_stream_ar⋅(aBP_get_stream_receiver_ar__mediumRs_ar⋅sb)"
  by (simp add: cfun_def)

lift_definition mediumRsOutConvert :: "(bool) mediumMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPMediumRsOut_stream_as⋅(medium_get_stream_as⋅sb)"
  by (simp add: cfun_def)

definition mediumRsInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ (bool) mediumMessage tsyn SB" where
"mediumRsInConverterSPF = ufLift aBPMediumRsDom mediumRsInConvert"

definition mediumRsOutConverterSPF :: "(bool) mediumMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" where
"mediumRsOutConverterSPF = ufLift aBPMediumRsRan mediumRsOutConvert"


section ‹Instances›

definition aBPSender :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"aBPSender = (senderInConverterSPF∘senderSPF∘senderOutConverterSPF)"

definition aBPMediumSr :: "('e::countable) abpMessage tsyn SPS" where
"aBPMediumSr = ((uspecConst mediumSrInConverterSPF)○mediumSPS○(uspecConst mediumSrOutConverterSPF))"

definition aBPReceiver :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"aBPReceiver = (receiverInConverterSPF∘receiverSPF∘receiverOutConverterSPF)"

definition aBPMediumRs :: "('e::countable) abpMessage tsyn SPS" where
"aBPMediumRs = ((uspecConst mediumRsInConverterSPF)○mediumSPS○(uspecConst mediumRsOutConverterSPF))"


section ‹Final definition›

definition aBPSPS :: "('e::countable) abpMessage tsyn SPS" where
"aBPSPS = ((uspecConst aBPSender)⨂aBPMediumSr⨂(uspecConst aBPReceiver)⨂aBPMediumRs)"


section ‹Lemmas for single tsyn setter›

lemma abpelem_receiver_o__o_dom[simp]: "sbeDom (aBPElem_receiver_o__o x) = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_o__o''}"
  apply(cases x)
  apply(simp add: aBPElem_receiver_o__o.simps sbeDom_def aBPElem_raw_receiver_o__o.rep_eq)
  by(simp add: aBPElem_receiver_o__o.simps)

lemma abpelem_i__sender_i_dom[simp]: "sbeDom (aBPElem_i__sender_i x) = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_i__sender_i''}"
  apply(cases x)
  apply(simp add: aBPElem_i__sender_i.simps sbeDom_def aBPElem_raw_i__sender_i.rep_eq)
  by(simp add: aBPElem_i__sender_i.simps)

lemma abpelem_sender_ds__mediumsr_ar_dom[simp]: "sbeDom (aBPElem_sender_ds__mediumSr_ar x) = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_sender_ds__mediumSr_ar''}"
  apply(cases x)
  apply(simp add: aBPElem_sender_ds__mediumSr_ar.simps sbeDom_def aBPElem_raw_sender_ds__mediumSr_ar.rep_eq)
  by(simp add: aBPElem_sender_ds__mediumSr_ar.simps)

lemma abpelem_mediumsr_as__receiver_dr_dom[simp]: "sbeDom (aBPElem_mediumSr_as__receiver_dr x) = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumSr_as__receiver_dr''}"
  apply(cases x)
  apply(simp add: aBPElem_mediumSr_as__receiver_dr.simps sbeDom_def aBPElem_raw_mediumSr_as__receiver_dr.rep_eq)
  by(simp add: aBPElem_mediumSr_as__receiver_dr.simps)

lemma abpelem_receiver_ar__mediumrs_ar_dom[simp]: "sbeDom (aBPElem_receiver_ar__mediumRs_ar x) = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_receiver_ar__mediumRs_ar''}"
  apply(cases x)
  apply(simp add: aBPElem_receiver_ar__mediumRs_ar.simps sbeDom_def aBPElem_raw_receiver_ar__mediumRs_ar.rep_eq)
  by(simp add: aBPElem_receiver_ar__mediumRs_ar.simps)

lemma abpelem_mediumrs_as__sender_as_dom[simp]: "sbeDom (aBPElem_mediumRs_as__sender_as x) = {𝒞 ''DoNotUse_ce22bc7f75e04442b8925f6407a24a0a_mediumRs_as__sender_as''}"
  apply(cases x)
  apply(simp add: aBPElem_mediumRs_as__sender_as.simps sbeDom_def aBPElem_raw_mediumRs_as__sender_as.rep_eq)
  by(simp add: aBPElem_mediumRs_as__sender_as.simps)

lemma abpelemin_i_dom[simp]: "sbeDom (aBPElemIn_i port_i) = aBPDom"
  by(auto simp add: aBPElemIn_i_def aBPDom_def)

lemma abpelemout_o_dom[simp]: "sbeDom (aBPElemOut_o port_o) = aBPRan"
  by(auto simp add: aBPElemOut_o_def aBPRan_def)

lemma abpin_i_dom[simp]: "ubDom⋅(aBPIn_i port_i) = aBPDom"
  by(simp add: aBPIn_i_def)

lemma abpout_o_dom[simp]: "ubDom⋅(aBPOut_o port_o) = aBPRan"
  by(simp add: aBPOut_o_def)


subsection ‹sender›

lemma abpsenderelemin_as_i_dom[simp]: "sbeDom (aBPSenderElemIn_as_i port_as port_i) = aBPSenderDom"
  sorry

lemma abpsenderelemout_ds_dom[simp]: "sbeDom (aBPSenderElemOut_ds port_ds) = aBPSenderRan"
  sorry

lemma abpsenderin_as_i_dom[simp]: "ubDom⋅(aBPSenderIn_as_i port_as port_i) = aBPSenderDom"
  sorry

lemma abpsenderout_ds_dom[simp]: "ubDom⋅(aBPSenderOut_ds port_ds) = aBPSenderRan"
  sorry


subsection ‹mediumSr›

lemma abpmediumsrelemin_ar_dom[simp]: "sbeDom (aBPMediumSrElemIn_ar port_ar) = aBPMediumSrDom"
  sorry

lemma abpmediumsrelemout_as_dom[simp]: "sbeDom (aBPMediumSrElemOut_as port_as) = aBPMediumSrRan"
  sorry

lemma abpmediumsrin_ar_dom[simp]: "ubDom⋅(aBPMediumSrIn_ar port_ar) = aBPMediumSrDom"
  sorry

lemma abpmediumsrout_as_dom[simp]: "ubDom⋅(aBPMediumSrOut_as port_as) = aBPMediumSrRan"
  sorry


subsection ‹receiver›

lemma abpreceiverelemin_dr_dom[simp]: "sbeDom (aBPReceiverElemIn_dr port_dr) = aBPReceiverDom"
  sorry

lemma abpreceiverelemout_ar_o_dom[simp]: "sbeDom (aBPReceiverElemOut_ar_o port_ar port_o) = aBPReceiverRan"
  sorry

lemma abpreceiverin_dr_dom[simp]: "ubDom⋅(aBPReceiverIn_dr port_dr) = aBPReceiverDom"
  sorry

lemma abpreceiverout_ar_o_dom[simp]: "ubDom⋅(aBPReceiverOut_ar_o port_ar port_o) = aBPReceiverRan"
  sorry


subsection ‹mediumRs›

lemma abpmediumrselemin_ar_dom[simp]: "sbeDom (aBPMediumRsElemIn_ar port_ar) = aBPMediumRsDom"
  sorry

lemma abpmediumrselemout_as_dom[simp]: "sbeDom (aBPMediumRsElemOut_as port_as) = aBPMediumRsRan"
  sorry

lemma abpmediumrsin_ar_dom[simp]: "ubDom⋅(aBPMediumRsIn_ar port_ar) = aBPMediumRsDom"
  sorry

lemma abpmediumrsout_as_dom[simp]: "ubDom⋅(aBPMediumRsOut_as port_as) = aBPMediumRsRan"
  sorry


section ‹Lemmas for getter›

subsection ‹Identity lemmas for single sbElems›

lemma abpelem_receiver_o__o_id[simp]: "aBPElem_get_receiver_o__o (aBPElem_receiver_o__o x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_receiver_o__o.simps)
  unfolding aBPElem_get_receiver_o__o_def aBPElem_raw_receiver_o__o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_i__sender_i_id[simp]: "aBPElem_get_i__sender_i (aBPElem_i__sender_i x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_i__sender_i.simps)
  unfolding aBPElem_get_i__sender_i_def aBPElem_raw_i__sender_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_sender_ds__mediumsr_ar_id[simp]: "aBPElem_get_sender_ds__mediumSr_ar (aBPElem_sender_ds__mediumSr_ar x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_sender_ds__mediumSr_ar.simps)
  unfolding aBPElem_get_sender_ds__mediumSr_ar_def aBPElem_raw_sender_ds__mediumSr_ar.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_mediumsr_as__receiver_dr_id[simp]: "aBPElem_get_mediumSr_as__receiver_dr (aBPElem_mediumSr_as__receiver_dr x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_mediumSr_as__receiver_dr.simps)
  unfolding aBPElem_get_mediumSr_as__receiver_dr_def aBPElem_raw_mediumSr_as__receiver_dr.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_receiver_ar__mediumrs_ar_id[simp]: "aBPElem_get_receiver_ar__mediumRs_ar (aBPElem_receiver_ar__mediumRs_ar x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_receiver_ar__mediumRs_ar.simps)
  unfolding aBPElem_get_receiver_ar__mediumRs_ar_def aBPElem_raw_receiver_ar__mediumRs_ar.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_mediumrs_as__sender_as_id[simp]: "aBPElem_get_mediumRs_as__sender_as (aBPElem_mediumRs_as__sender_as x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_mediumRs_as__sender_as.simps)
  unfolding aBPElem_get_mediumRs_as__sender_as_def aBPElem_raw_mediumRs_as__sender_as.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsection ‹Identity lemmas for single SBs from streams›

lemma abp_stream_receiver_o__o_id[simp]: "aBP_get_stream_receiver_o__o⋅(aBP_stream_receiver_o__o⋅x) = x"
  sorry

lemma abp_stream_i__sender_i_id[simp]: "aBP_get_stream_i__sender_i⋅(aBP_stream_i__sender_i⋅x) = x"
  sorry

lemma abp_stream_sender_ds__mediumsr_ar_id[simp]: "aBP_get_stream_sender_ds__mediumSr_ar⋅(aBP_stream_sender_ds__mediumSr_ar⋅x) = x"
  sorry

lemma abp_stream_mediumsr_as__receiver_dr_id[simp]: "aBP_get_stream_mediumSr_as__receiver_dr⋅(aBP_stream_mediumSr_as__receiver_dr⋅x) = x"
  sorry

lemma abp_stream_receiver_ar__mediumrs_ar_id[simp]: "aBP_get_stream_receiver_ar__mediumRs_ar⋅(aBP_stream_receiver_ar__mediumRs_ar⋅x) = x"
  sorry

lemma abp_stream_mediumrs_as__sender_as_id[simp]: "aBP_get_stream_mediumRs_as__sender_as⋅(aBP_stream_mediumRs_as__sender_as⋅x) = x"
  sorry


subsection ‹Identity lemmas for input sbElems›

lemma abpelemin_i_i__sender_i_id[simp]: "aBPElem_get_i__sender_i (aBPElemIn_i port_i__sender_port_i) = port_i__sender_port_i"
  sorry


subsection ‹Identity lemmas for output sbElems›

lemma abpelemout_o_receiver_o__o_id[simp]: "aBPElem_get_receiver_o__o (aBPElemOut_o receiver_port_o__port_o) = receiver_port_o__port_o"
  sorry


subsection ‹Identity lemmas for input SBs›

lemma abpin_i_i__sender_i_id[simp]: "aBP_get_stream_i__sender_i⋅(aBPIn_i port_i__sender_port_i) = ↑port_i__sender_port_i"
  apply(simp add: aBP_get_stream_i__sender_i_def aBPIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: aBPDom_def aBPElemIn_i_def)
  apply(cases port_i__sender_port_i)
  apply(auto simp add: aBPElem_i__sender_i.simps)
  unfolding aBPElem_get_i__sender_i_def aBPElem_raw_i__sender_i.rep_eq
  (* TODO Ab hier funktioniert der Beweis nicht mehr *)
  (*apply auto
  apply (meson f_inv_into_f rangeI abpMessage.inject(1))
  by(simp add: sbeNull.rep_eq)*)
  sorry


subsection ‹Identity lemmas for output SBs›

lemma abpout_o_receiver_o__o_id[simp]: "aBP_get_stream_receiver_o__o⋅(aBPOut_o receiver_port_o__port_o) = ↑receiver_port_o__port_o"
  sorry


subsection ‹Identity lemmas for input SBs from streams›

lemma abpin_stream_i_i__sender_i_id[simp]: "aBP_get_stream_i__sender_i⋅(aBPIn_stream_i⋅port_i__sender_port_i) = port_i__sender_port_i"
  sorry


subsection ‹Identity lemmas for output SBs from streams›

lemma abpout_stream_o_receiver_o__o_id[simp]: "aBP_get_stream_receiver_o__o⋅(aBPOut_stream_o⋅receiver_port_o__port_o) = receiver_port_o__port_o"
  sorry


end