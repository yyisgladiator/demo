(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 29, 2018 5:54:16 PM by isartransformer 1.0.0
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

datatype ('e::countable) abpMessage = DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE "'e" | DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool "bool" | DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool "('e×bool)"

instance abpMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: (countable) message
begin
  fun ctype_abpMessage :: "channel ⇒ ('e::countable) abpMessage set" where
  "ctype_abpMessage c = (
    if c = 𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_o__o'' then range DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE else
    if c = 𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_i__sender_i'' then range DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE else
    if c = 𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_sender_ds__mediumSr_ar'' then range DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool else
    if c = 𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumSr_as__receiver_dr'' then range DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool else
    if c = 𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_ar__mediumRs_ar'' then range DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool else
    if c = 𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumRs_as__sender_as'' then range DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool else
    undefined)"
  instance
    by(intro_classes)
end


section ‹Helpers to create a bundle from a single raw element›

lift_definition aBPElem_raw_receiver_o__o :: "'e ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_o__o'' ↦ Msg (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_i__sender_i :: "'e ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_i__sender_i'' ↦ Msg (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_sender_ds__mediumSr_ar :: "('e×bool) ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_sender_ds__mediumSr_ar'' ↦ Msg (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_mediumSr_as__receiver_dr :: "('e×bool) ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumSr_as__receiver_dr'' ↦ Msg (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_receiver_ar__mediumRs_ar :: "bool ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_ar__mediumRs_ar'' ↦ Msg (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition aBPElem_raw_mediumRs_as__sender_as :: "bool ⇒ ('e::countable) abpMessage tsyn sbElem" is
"λx. [𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumRs_as__sender_as'' ↦ Msg (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section ‹Helpers to create a bundle from a single tsyn element›

fun aBPElem_receiver_o__o :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_receiver_o__o (Msg receiver_port_o__port_o) = aBPElem_raw_receiver_o__o receiver_port_o__port_o" |
"aBPElem_receiver_o__o null = sbeNull {𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_o__o''}"

declare aBPElem_receiver_o__o.simps[simp del]

definition aBP_receiver_o__o :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_receiver_o__o receiver_port_o__port_o = sbe2SB (aBPElem_receiver_o__o receiver_port_o__port_o)"

fun aBPElem_i__sender_i :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_i__sender_i (Msg port_i__sender_port_i) = aBPElem_raw_i__sender_i port_i__sender_port_i" |
"aBPElem_i__sender_i null = sbeNull {𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_i__sender_i''}"

declare aBPElem_i__sender_i.simps[simp del]

definition aBP_i__sender_i :: "'e tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_i__sender_i port_i__sender_port_i = sbe2SB (aBPElem_i__sender_i port_i__sender_port_i)"

fun aBPElem_sender_ds__mediumSr_ar :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_sender_ds__mediumSr_ar (Msg sender_port_ds__mediumSr_port_ar) = aBPElem_raw_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar" |
"aBPElem_sender_ds__mediumSr_ar null = sbeNull {𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_sender_ds__mediumSr_ar''}"

declare aBPElem_sender_ds__mediumSr_ar.simps[simp del]

definition aBP_sender_ds__mediumSr_ar :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar = sbe2SB (aBPElem_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar)"

fun aBPElem_mediumSr_as__receiver_dr :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_mediumSr_as__receiver_dr (Msg mediumSr_port_as__receiver_port_dr) = aBPElem_raw_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr" |
"aBPElem_mediumSr_as__receiver_dr null = sbeNull {𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumSr_as__receiver_dr''}"

declare aBPElem_mediumSr_as__receiver_dr.simps[simp del]

definition aBP_mediumSr_as__receiver_dr :: "('e×bool) tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr = sbe2SB (aBPElem_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr)"

fun aBPElem_receiver_ar__mediumRs_ar :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_receiver_ar__mediumRs_ar (Msg receiver_port_ar__mediumRs_port_ar) = aBPElem_raw_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar" |
"aBPElem_receiver_ar__mediumRs_ar null = sbeNull {𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_ar__mediumRs_ar''}"

declare aBPElem_receiver_ar__mediumRs_ar.simps[simp del]

definition aBP_receiver_ar__mediumRs_ar :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn SB" where
"aBP_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar = sbe2SB (aBPElem_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar)"

fun aBPElem_mediumRs_as__sender_as :: "bool tsyn ⇒ ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_mediumRs_as__sender_as (Msg mediumRs_port_as__sender_port_as) = aBPElem_raw_mediumRs_as__sender_as mediumRs_port_as__sender_port_as" |
"aBPElem_mediumRs_as__sender_as null = sbeNull {𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumRs_as__sender_as''}"

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


section ‹Helpers to create a bundle from a tsyn stream of elements›

lift_definition DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_receiver_o__o_h :: "'e tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_o__o'') ↦ (tsynMap (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition aBP_stream_receiver_o__o :: "('e) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_receiver_o__o_h"
  sorry

lift_definition DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_i__sender_i_h :: "'e tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_i__sender_i'') ↦ (tsynMap (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition aBP_stream_i__sender_i :: "('e) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_i__sender_i_h"
  sorry

lift_definition DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_sender_ds__mediumSr_ar_h :: "('e×bool) tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_sender_ds__mediumSr_ar'') ↦ (tsynMap (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition aBP_stream_sender_ds__mediumSr_ar :: "(('e×bool)) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_sender_ds__mediumSr_ar_h"
  sorry

lift_definition DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_mediumSr_as__receiver_dr_h :: "('e×bool) tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumSr_as__receiver_dr'') ↦ (tsynMap (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition aBP_stream_mediumSr_as__receiver_dr :: "(('e×bool)) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_mediumSr_as__receiver_dr_h"
  sorry

lift_definition DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_receiver_ar__mediumRs_ar_h :: "bool tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_ar__mediumRs_ar'') ↦ (tsynMap (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition aBP_stream_receiver_ar__mediumRs_ar :: "(bool) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_receiver_ar__mediumRs_ar_h"
  sorry

lift_definition DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_mediumRs_as__sender_as_h :: "bool tsyn stream ⇒ ('e::countable) abpMessage tsyn SB" is
"λ s. [(𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumRs_as__sender_as'') ↦ (tsynMap (DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool)⋅s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition aBP_stream_mediumRs_as__sender_as :: "(bool) tsyn stream → ('e::countable) abpMessage tsyn SB" is
"DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_aBP_stream_mediumRs_as__sender_as_h"
  sorry

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

fun aBPElem_get_receiver_o__o :: "('e::countable) abpMessage tsyn sbElem ⇒ ('e) tsyn" where
"aBPElem_get_receiver_o__o sbe = undefined"

lift_definition aBP_get_stream_receiver_o__o :: "('e::countable) abpMessage tsyn SB → 'e tsyn stream" is
"λsb. tsynMap (inv DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE)⋅(sb . (𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_o__o''))"
  by(simp add: cfun_def)

fun aBPElem_get_i__sender_i :: "('e::countable) abpMessage tsyn sbElem ⇒ ('e) tsyn" where
"aBPElem_get_i__sender_i sbe = undefined"

lift_definition aBP_get_stream_i__sender_i :: "('e::countable) abpMessage tsyn SB → 'e tsyn stream" is
"λsb. tsynMap (inv DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPE)⋅(sb . (𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_i__sender_i''))"
  by(simp add: cfun_def)

fun aBPElem_get_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn sbElem ⇒ (('e×bool)) tsyn" where
"aBPElem_get_sender_ds__mediumSr_ar sbe = undefined"

lift_definition aBP_get_stream_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn SB → ('e×bool) tsyn stream" is
"λsb. tsynMap (inv DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool)⋅(sb . (𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_sender_ds__mediumSr_ar''))"
  by(simp add: cfun_def)

fun aBPElem_get_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn sbElem ⇒ (('e×bool)) tsyn" where
"aBPElem_get_mediumSr_as__receiver_dr sbe = undefined"

lift_definition aBP_get_stream_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn SB → ('e×bool) tsyn stream" is
"λsb. tsynMap (inv DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPPair_E_Bool)⋅(sb . (𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumSr_as__receiver_dr''))"
  by(simp add: cfun_def)

fun aBPElem_get_receiver_ar__mediumRs_ar :: "('e::countable) abpMessage tsyn sbElem ⇒ (bool) tsyn" where
"aBPElem_get_receiver_ar__mediumRs_ar sbe = undefined"

lift_definition aBP_get_stream_receiver_ar__mediumRs_ar :: "('e::countable) abpMessage tsyn SB → bool tsyn stream" is
"λsb. tsynMap (inv DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool)⋅(sb . (𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_receiver_ar__mediumRs_ar''))"
  by(simp add: cfun_def)

fun aBPElem_get_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn sbElem ⇒ (bool) tsyn" where
"aBPElem_get_mediumRs_as__sender_as sbe = undefined"

lift_definition aBP_get_stream_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn SB → bool tsyn stream" is
"λsb. tsynMap (inv DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_ABPBool)⋅(sb . (𝒞 ''DoNotUse_5b2352bc0cd24bc7b6c3f6f480670fcb_mediumRs_as__sender_as''))"
  by(simp add: cfun_def)


section ‹Converter›


subsection ‹sender›

lift_definition senderInConvert :: "('e::countable) abpMessage tsyn SB → ('e) senderMessage tsyn SB" is
"λsb. senderIn_stream_as_i⋅(aBP_get_stream_mediumRs_as__sender_as⋅sb)⋅(aBP_get_stream_i__sender_i⋅sb)"
  by (simp add: cfun_def)

lift_definition senderOutConvert :: "('e) senderMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPSenderOut_stream_ds⋅(sender_get_stream_ds⋅sb)"
  by (simp add: cfun_def)

lift_definition senderInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ ('e) senderMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ senderInConvert⋅sb))"
  sorry

lift_definition senderOutConverterSPF :: "('e) senderMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ senderOutConvert⋅sb))"
  sorry


subsection ‹mediumSr›

lift_definition mediumSrInConvert :: "('e::countable) abpMessage tsyn SB → (('e×bool)) mediumMessage tsyn SB" is
"λsb. mediumIn_stream_ar⋅(aBP_get_stream_sender_ds__mediumSr_ar⋅sb)"
  by (simp add: cfun_def)

lift_definition mediumSrOutConvert :: "(('e×bool)) mediumMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPMediumSrOut_stream_as⋅(medium_get_stream_as⋅sb)"
  by (simp add: cfun_def)

lift_definition mediumSrInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ (('e×bool)) mediumMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ mediumSrInConvert⋅sb))"
  sorry

lift_definition mediumSrOutConverterSPF :: "(('e×bool)) mediumMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ mediumSrOutConvert⋅sb))"
  sorry


subsection ‹receiver›

lift_definition receiverInConvert :: "('e::countable) abpMessage tsyn SB → ('e) receiverMessage tsyn SB" is
"λsb. receiverIn_stream_dr⋅(aBP_get_stream_mediumSr_as__receiver_dr⋅sb)"
  by (simp add: cfun_def)

lift_definition receiverOutConvert :: "('e) receiverMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPReceiverOut_stream_ar_o⋅(receiver_get_stream_ar⋅sb)⋅(receiver_get_stream_o⋅sb)"
  by (simp add: cfun_def)

lift_definition receiverInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ ('e) receiverMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ receiverInConvert⋅sb))"
  sorry

lift_definition receiverOutConverterSPF :: "('e) receiverMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ receiverOutConvert⋅sb))"
  sorry


subsection ‹mediumRs›

lift_definition mediumRsInConvert :: "('e::countable) abpMessage tsyn SB → (bool) mediumMessage tsyn SB" is
"λsb. mediumIn_stream_ar⋅(aBP_get_stream_receiver_ar__mediumRs_ar⋅sb)"
  by (simp add: cfun_def)

lift_definition mediumRsOutConvert :: "(bool) mediumMessage tsyn SB → ('e::countable) abpMessage tsyn SB" is
"λsb. aBPMediumRsOut_stream_as⋅(medium_get_stream_as⋅sb)"
  by (simp add: cfun_def)

lift_definition mediumRsInConverterSPF :: "('e::countable) abpMessage tsyn SB ⇛ (bool) mediumMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ mediumRsInConvert⋅sb))"
  sorry

lift_definition mediumRsOutConverterSPF :: "(bool) mediumMessage tsyn SB ⇛ ('e::countable) abpMessage tsyn SB" is
"(Λ sb . ((ubDom⋅sb = undefined) ↝ mediumRsOutConvert⋅sb))"
  sorry


section ‹Instances›

definition sender :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"sender = (senderInConverterSPF∘senderSPF∘senderOutConverterSPF)"

definition mediumSr :: "('e::countable) abpMessage tsyn SPS" where
"mediumSr = ((uspecConst mediumSrInConverterSPF)○mediumSPS○(uspecConst mediumSrOutConverterSPF))"

definition receiver :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"receiver = (receiverInConverterSPF∘receiverSPF∘receiverOutConverterSPF)"

definition mediumRs :: "('e::countable) abpMessage tsyn SPS" where
"mediumRs = ((uspecConst mediumRsInConverterSPF)○mediumSPS○(uspecConst mediumRsOutConverterSPF))"


section ‹Final definition›

definition aBPSPS :: "('e::countable) abpMessage tsyn SPS" where
"aBPSPS = ((uspecConst sender)⨂mediumSr⨂(uspecConst receiver)⨂mediumRs)"


section ‹Lemmas for getter›

subsection ‹Identity lemmas for single sbElems›

lemma abpelem_receiver_o__o_id[simp]: "aBPElem_get_receiver_o__o (aBPElem_receiver_o__o x) = x"
  sorry

lemma abpelem_i__sender_i_id[simp]: "aBPElem_get_i__sender_i (aBPElem_i__sender_i x) = x"
  sorry

lemma abpelem_sender_ds__mediumsr_ar_id[simp]: "aBPElem_get_sender_ds__mediumSr_ar (aBPElem_sender_ds__mediumSr_ar x) = x"
  sorry

lemma abpelem_mediumsr_as__receiver_dr_id[simp]: "aBPElem_get_mediumSr_as__receiver_dr (aBPElem_mediumSr_as__receiver_dr x) = x"
  sorry

lemma abpelem_receiver_ar__mediumrs_ar_id[simp]: "aBPElem_get_receiver_ar__mediumRs_ar (aBPElem_receiver_ar__mediumRs_ar x) = x"
  sorry

lemma abpelem_mediumrs_as__sender_as_id[simp]: "aBPElem_get_mediumRs_as__sender_as (aBPElem_mediumRs_as__sender_as x) = x"
  sorry


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