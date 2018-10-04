(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory SenderDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) senderMessage = DoNotUse_0b0ad6_SenderBool "bool" | DoNotUse_0b0ad6_SenderE "'e" | DoNotUse_0b0ad6_SenderPair_E_Bool "('e\<times>bool)"

instance senderMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation senderMessage :: (countable) message
begin
  fun ctype_senderMessage :: "channel \<Rightarrow> ('e::countable) senderMessage set" where
  "ctype_senderMessage c = (
    if c = \<C> ''DoNotUse_0b0ad6_as'' then range DoNotUse_0b0ad6_SenderBool else
    if c = \<C> ''DoNotUse_0b0ad6_i'' then range DoNotUse_0b0ad6_SenderE else
    if c = \<C> ''DoNotUse_0b0ad6_ds'' then range DoNotUse_0b0ad6_SenderPair_E_Bool else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition senderDom :: "channel set" where
"senderDom = {\<C> ''DoNotUse_0b0ad6_as'', \<C> ''DoNotUse_0b0ad6_i''}"

definition senderRan :: "channel set" where
"senderRan = {\<C> ''DoNotUse_0b0ad6_ds''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use senderElemIn_as_i instead *)
lift_definition senderElem_raw_as :: "bool \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_0b0ad6_as'' \<mapsto> Msg (DoNotUse_0b0ad6_SenderBool x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use senderElemIn_as_i instead *)
lift_definition senderElem_raw_i :: "'e \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_0b0ad6_i'' \<mapsto> Msg (DoNotUse_0b0ad6_SenderE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use senderElemOut_ds instead *)
lift_definition senderElem_raw_ds :: "('e\<times>bool) \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_0b0ad6_ds'' \<mapsto> Msg (DoNotUse_0b0ad6_SenderPair_E_Bool x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use senderElemIn_as_i instead *)
fun senderElem_as :: "bool tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_as (Msg port_as) = senderElem_raw_as port_as" |
"senderElem_as null = sbeNull {\<C> ''DoNotUse_0b0ad6_as''}"

(* Do not use this, use senderElemIn_as_i instead *)
fun senderElem_i :: "'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_i (Msg port_i) = senderElem_raw_i port_i" |
"senderElem_i null = sbeNull {\<C> ''DoNotUse_0b0ad6_i''}"

(* Do not use this, use senderElemOut_ds instead *)
fun senderElem_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_ds (Msg port_ds) = senderElem_raw_ds port_ds" |
"senderElem_ds null = sbeNull {\<C> ''DoNotUse_0b0ad6_ds''}"

declare senderElem_as.simps[simp del]

declare senderElem_i.simps[simp del]

declare senderElem_ds.simps[simp del]

(* Do not use this, use senderIn_as_i instead *)
definition sender_as :: "bool tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_as port_as = sbe2SB (senderElem_as port_as)"

(* Do not use this, use senderIn_as_i instead *)
definition sender_i :: "'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_i port_i = sbe2SB (senderElem_i port_i)"

(* Do not use this, use senderOut_ds instead *)
definition sender_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_ds port_ds = sbe2SB (senderElem_ds port_ds)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition senderElemIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElemIn_as_i port_as port_i = (senderElem_as port_as) \<plusminus> (senderElem_i port_i)"

(* Create one sbElem for all output channels *)
definition senderElemOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElemOut_ds port_ds = (senderElem_ds port_ds)"

(* Create one SB for all input channels *)
definition senderIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_as_i port_as port_i = (sbe2SB (senderElemIn_as_i port_as port_i))"

(* Create one SB for all output channels *)
definition senderOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_ds port_ds = (sbe2SB (senderElemOut_ds port_ds))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use senderIn_list_as_i instead *)
fun sender_list_as :: "(bool tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_as (x#xs) = ubConcEq (sender_as x)\<cdot>(sender_list_as xs)" |
"sender_list_as []     = ubLeast {\<C> ''DoNotUse_0b0ad6_as''}"

declare sender_list_as.simps[simp del]

(* Do not use this, use senderIn_list_as_i instead *)
fun sender_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_i (x#xs) = ubConcEq (sender_i x)\<cdot>(sender_list_i xs)" |
"sender_list_i []     = ubLeast {\<C> ''DoNotUse_0b0ad6_i''}"

declare sender_list_i.simps[simp del]

(* Do not use this, use senderOut_list_ds instead *)
fun sender_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_ds (x#xs) = ubConcEq (sender_ds x)\<cdot>(sender_list_ds xs)" |
"sender_list_ds []     = ubLeast {\<C> ''DoNotUse_0b0ad6_ds''}"

declare sender_list_ds.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun senderIn_list_as_i :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_list_as_i ((port_as,port_i)#xs) = ubConcEq (senderIn_as_i port_as port_i)\<cdot>(senderIn_list_as_i xs)" |
"senderIn_list_as_i [] = ubLeast senderDom"

(* Create one SB for all output channels *)
fun senderOut_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_list_ds ((port_ds)#xs) = ubConcEq (senderOut_ds port_ds)\<cdot>(senderOut_list_ds xs)" |
"senderOut_list_ds [] = ubLeast senderRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_0b0ad6_sender_stream_as_h :: "bool tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_0b0ad6_as'') \<mapsto> (tsynMap (DoNotUse_0b0ad6_SenderBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use senderIn_stream_as_i instead *)
lift_definition sender_stream_as :: "(bool) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_0b0ad6_sender_stream_as_h"
  apply(auto simp add: cfun_def DoNotUse_0b0ad6_sender_stream_as_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_0b0ad6_sender_stream_as_h.rep_eq ubrep_well)

lift_definition DoNotUse_0b0ad6_sender_stream_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_0b0ad6_i'') \<mapsto> (tsynMap (DoNotUse_0b0ad6_SenderE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use senderIn_stream_as_i instead *)
lift_definition sender_stream_i :: "('e) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_0b0ad6_sender_stream_i_h"
  apply(auto simp add: cfun_def DoNotUse_0b0ad6_sender_stream_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_0b0ad6_sender_stream_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_0b0ad6_sender_stream_ds_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_0b0ad6_ds'') \<mapsto> (tsynMap (DoNotUse_0b0ad6_SenderPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use senderOut_stream_ds instead *)
lift_definition sender_stream_ds :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_0b0ad6_sender_stream_ds_h"
  apply(auto simp add: cfun_def DoNotUse_0b0ad6_sender_stream_ds_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_0b0ad6_sender_stream_ds_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition senderIn_stream_as_i :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_stream_as_i = (\<Lambda>  port_as port_i. (sender_stream_as\<cdot>port_as) \<uplus> (sender_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition senderOut_stream_ds :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_stream_ds = (\<Lambda>  port_ds. (sender_stream_ds\<cdot>port_ds))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition senderElem_get_as :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"senderElem_get_as sbe = tsynApplyElem (inv DoNotUse_0b0ad6_SenderBool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_0b0ad6_as''))"

definition senderElem_get_i :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"senderElem_get_i sbe = tsynApplyElem (inv DoNotUse_0b0ad6_SenderE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_0b0ad6_i''))"

definition senderElem_get_ds :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"senderElem_get_ds sbe = tsynApplyElem (inv DoNotUse_0b0ad6_SenderPair_E_Bool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_0b0ad6_ds''))"


subsection \<open>SB to stream\<close>

lift_definition sender_get_stream_as :: "('e::countable) senderMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_0b0ad6_SenderBool)\<cdot>(sb . (\<C> ''DoNotUse_0b0ad6_as''))"
  by(simp add: cfun_def)

lift_definition sender_get_stream_i :: "('e::countable) senderMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_0b0ad6_SenderE)\<cdot>(sb . (\<C> ''DoNotUse_0b0ad6_i''))"
  by(simp add: cfun_def)

lift_definition sender_get_stream_ds :: "('e::countable) senderMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_0b0ad6_SenderPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_0b0ad6_ds''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma senderelem_as_dom[simp]: "sbeDom (senderElem_as x) = {\<C> ''DoNotUse_0b0ad6_as''}"
  apply(cases x)
  apply(simp add: senderElem_as.simps sbeDom_def senderElem_raw_as.rep_eq)
  by(simp add: senderElem_as.simps)

lemma senderelem_i_dom[simp]: "sbeDom (senderElem_i x) = {\<C> ''DoNotUse_0b0ad6_i''}"
  apply(cases x)
  apply(simp add: senderElem_i.simps sbeDom_def senderElem_raw_i.rep_eq)
  by(simp add: senderElem_i.simps)

lemma senderelem_ds_dom[simp]: "sbeDom (senderElem_ds x) = {\<C> ''DoNotUse_0b0ad6_ds''}"
  apply(cases x)
  apply(simp add: senderElem_ds.simps sbeDom_def senderElem_raw_ds.rep_eq)
  by(simp add: senderElem_ds.simps)

lemma sender_as_dom[simp]: "ubDom\<cdot>(sender_as x) = {\<C> ''DoNotUse_0b0ad6_as''}"
  by(simp add: sender_as_def)

lemma sender_as_len[simp]: "ubLen (sender_as x) = 1"
  by(simp add: sender_as_def)

lemma sender_i_dom[simp]: "ubDom\<cdot>(sender_i x) = {\<C> ''DoNotUse_0b0ad6_i''}"
  by(simp add: sender_i_def)

lemma sender_i_len[simp]: "ubLen (sender_i x) = 1"
  by(simp add: sender_i_def)

lemma sender_ds_dom[simp]: "ubDom\<cdot>(sender_ds x) = {\<C> ''DoNotUse_0b0ad6_ds''}"
  by(simp add: sender_ds_def)

lemma sender_ds_len[simp]: "ubLen (sender_ds x) = 1"
  by(simp add: sender_ds_def)


subsubsection \<open>In/Out\<close>

lemma senderelemin_as_i_dom[simp]: "sbeDom (senderElemIn_as_i port_as port_i) = senderDom"
  by(auto simp add: senderElemIn_as_i_def senderDom_def)

lemma senderelemout_ds_dom[simp]: "sbeDom (senderElemOut_ds port_ds) = senderRan"
  by(auto simp add: senderElemOut_ds_def senderRan_def)

lemma senderin_as_i_dom[simp]: "ubDom\<cdot>(senderIn_as_i port_as port_i) = senderDom"
  by(simp add: senderIn_as_i_def)

lemma senderin_as_i_len[simp]: "ubLen (senderIn_as_i port_as port_i) = 1"
  by(simp add: senderIn_as_i_def senderDom_def)

lemma senderout_ds_dom[simp]: "ubDom\<cdot>(senderOut_ds port_ds) = senderRan"
  by(simp add: senderOut_ds_def)

lemma senderout_ds_len[simp]: "ubLen (senderOut_ds port_ds) = 1"
  by(simp add: senderOut_ds_def senderRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma sender_stream_as_dom[simp]: "ubDom\<cdot>(sender_stream_as\<cdot>x) = {\<C> ''DoNotUse_0b0ad6_as''}"
  by(simp add: sender_stream_as.rep_eq ubdom_insert DoNotUse_0b0ad6_sender_stream_as_h.rep_eq)

lemma sender_stream_as_len[simp]: "ubLen (sender_stream_as\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: sender_stream_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_0b0ad6_sender_stream_as_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma sender_stream_as_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_0b0ad6_as''} "
    shows "sender_stream_as\<cdot>(sender_get_stream_as\<cdot>ub) = ub"
  apply(simp add: sender_stream_as.rep_eq sender_get_stream_as.rep_eq)
  apply(simp add: DoNotUse_0b0ad6_sender_stream_as_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma sender_stream_i_dom[simp]: "ubDom\<cdot>(sender_stream_i\<cdot>x) = {\<C> ''DoNotUse_0b0ad6_i''}"
  by(simp add: sender_stream_i.rep_eq ubdom_insert DoNotUse_0b0ad6_sender_stream_i_h.rep_eq)

lemma sender_stream_i_len[simp]: "ubLen (sender_stream_i\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: sender_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_0b0ad6_sender_stream_i_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma sender_stream_i_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_0b0ad6_i''} "
    shows "sender_stream_i\<cdot>(sender_get_stream_i\<cdot>ub) = ub"
  apply(simp add: sender_stream_i.rep_eq sender_get_stream_i.rep_eq)
  apply(simp add: DoNotUse_0b0ad6_sender_stream_i_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma sender_stream_ds_dom[simp]: "ubDom\<cdot>(sender_stream_ds\<cdot>x) = {\<C> ''DoNotUse_0b0ad6_ds''}"
  by(simp add: sender_stream_ds.rep_eq ubdom_insert DoNotUse_0b0ad6_sender_stream_ds_h.rep_eq)

lemma sender_stream_ds_len[simp]: "ubLen (sender_stream_ds\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: sender_stream_ds.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_0b0ad6_sender_stream_ds_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma sender_stream_ds_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_0b0ad6_ds''} "
    shows "sender_stream_ds\<cdot>(sender_get_stream_ds\<cdot>ub) = ub"
  apply(simp add: sender_stream_ds.rep_eq sender_get_stream_ds.rep_eq)
  apply(simp add: DoNotUse_0b0ad6_sender_stream_ds_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma senderin_stream_as_i_dom[simp]: "ubDom\<cdot>(senderIn_stream_as_i\<cdot>port_as\<cdot>port_i) = senderDom"
  apply(simp add: senderIn_stream_as_i_def ubclUnion_ubundle_def)
  by(auto simp add: senderDom_def)

lemma senderout_stream_ds_dom[simp]: "ubDom\<cdot>(senderOut_stream_ds\<cdot>port_ds) = senderRan"
  apply(simp add: senderOut_stream_ds_def ubclUnion_ubundle_def)
  by(auto simp add: senderRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma senderelem_get_as_id[simp]: "senderElem_get_as (senderElem_as x) = x"
  apply(cases x)
  apply(auto simp add: senderElem_as.simps)
  unfolding senderElem_get_as_def senderElem_raw_as.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI senderMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma senderelem_get_i_id[simp]: "senderElem_get_i (senderElem_i x) = x"
  apply(cases x)
  apply(auto simp add: senderElem_i.simps)
  unfolding senderElem_get_i_def senderElem_raw_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI senderMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma senderelem_get_ds_id[simp]: "senderElem_get_ds (senderElem_ds x) = x"
  apply(cases x)
  apply(auto simp add: senderElem_ds.simps)
  unfolding senderElem_get_ds_def senderElem_raw_ds.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI senderMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma senderelem_get_as_in_as_id[simp]: "senderElem_get_as (senderElemIn_as_i port_as port_i) = port_as"
  apply(simp add: senderElemIn_as_i_def senderElem_get_as_def)
  by(metis senderElem_get_as_def senderelem_get_as_id)

lemma senderelem_get_i_in_i_id[simp]: "senderElem_get_i (senderElemIn_as_i port_as port_i) = port_i"
  apply(simp add: senderElemIn_as_i_def senderElem_get_i_def)
  by(metis senderElem_get_i_def senderelem_get_i_id)

lemma senderelem_get_ds_out_ds_id[simp]: "senderElem_get_ds (senderElemOut_ds port_ds) = port_ds"
  apply(simp add: senderElemOut_ds_def senderElem_get_ds_def)
  by(metis senderElem_get_ds_def senderelem_get_ds_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma sender_get_stream_as_id[simp]: "sender_get_stream_as\<cdot>(sender_stream_as\<cdot>x) = x"
  apply(simp add: sender_get_stream_as.rep_eq sender_stream_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_0b0ad6_sender_stream_as_h.rep_eq)
  by (simp add: inj_def)

lemma sender_get_stream_as_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_0b0ad6_as''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_0b0ad6_as''}"
      and "sender_get_stream_as\<cdot>ub1 = sender_get_stream_as\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) sender_stream_as_id by metis

lemma sender_get_stream_as_conc[simp]:
  assumes "\<C> ''DoNotUse_0b0ad6_as'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_0b0ad6_as'' \<in> ubDom\<cdot>ub2"
    shows "sender_get_stream_as\<cdot>(ubConc ub1\<cdot>ub2) = (sender_get_stream_as\<cdot>ub1) \<bullet> (sender_get_stream_as\<cdot>ub2)"
  apply(simp add: sender_get_stream_as.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma sender_get_stream_i_id[simp]: "sender_get_stream_i\<cdot>(sender_stream_i\<cdot>x) = x"
  apply(simp add: sender_get_stream_i.rep_eq sender_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_0b0ad6_sender_stream_i_h.rep_eq)
  by (simp add: inj_def)

lemma sender_get_stream_i_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_0b0ad6_i''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_0b0ad6_i''}"
      and "sender_get_stream_i\<cdot>ub1 = sender_get_stream_i\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) sender_stream_i_id by metis

lemma sender_get_stream_i_conc[simp]:
  assumes "\<C> ''DoNotUse_0b0ad6_i'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_0b0ad6_i'' \<in> ubDom\<cdot>ub2"
    shows "sender_get_stream_i\<cdot>(ubConc ub1\<cdot>ub2) = (sender_get_stream_i\<cdot>ub1) \<bullet> (sender_get_stream_i\<cdot>ub2)"
  apply(simp add: sender_get_stream_i.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma sender_get_stream_ds_id[simp]: "sender_get_stream_ds\<cdot>(sender_stream_ds\<cdot>x) = x"
  apply(simp add: sender_get_stream_ds.rep_eq sender_stream_ds.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_0b0ad6_sender_stream_ds_h.rep_eq)
  by (simp add: inj_def)

lemma sender_get_stream_ds_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_0b0ad6_ds''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_0b0ad6_ds''}"
      and "sender_get_stream_ds\<cdot>ub1 = sender_get_stream_ds\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) sender_stream_ds_id by metis

lemma sender_get_stream_ds_conc[simp]:
  assumes "\<C> ''DoNotUse_0b0ad6_ds'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_0b0ad6_ds'' \<in> ubDom\<cdot>ub2"
    shows "sender_get_stream_ds\<cdot>(ubConc ub1\<cdot>ub2) = (sender_get_stream_ds\<cdot>ub1) \<bullet> (sender_get_stream_ds\<cdot>ub2)"
  apply(simp add: sender_get_stream_ds.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma sender_get_stream_as_in_as_id[simp]: "sender_get_stream_as\<cdot>(senderIn_stream_as_i\<cdot>port_as\<cdot>port_i) = port_as"
  apply(auto simp add: sender_get_stream_as.rep_eq senderIn_stream_as_i_def ubclUnion_ubundle_def)
  by (metis sender_get_stream_as.rep_eq sender_get_stream_as_id)

lemma sender_get_stream_i_in_i_id[simp]: "sender_get_stream_i\<cdot>(senderIn_stream_as_i\<cdot>port_as\<cdot>port_i) = port_i"
  apply(auto simp add: sender_get_stream_i.rep_eq senderIn_stream_as_i_def ubclUnion_ubundle_def)
  by (metis sender_get_stream_i.rep_eq sender_get_stream_i_id)

lemma sender_get_stream_ds_out_ds_id[simp]: "sender_get_stream_ds\<cdot>(senderOut_stream_ds\<cdot>port_ds) = port_ds"
  apply(auto simp add: sender_get_stream_ds.rep_eq senderOut_stream_ds_def ubclUnion_ubundle_def)
  by (metis sender_get_stream_ds.rep_eq sender_get_stream_ds_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma sender_get_stream_as_single[simp]: "sender_get_stream_as\<cdot>(sender_as x) = \<up>x"
  apply(simp add: sender_get_stream_as.rep_eq sender_as_def)
  by (metis senderElem_get_as_def senderelem_get_as_id)

lemma sender_get_stream_i_single[simp]: "sender_get_stream_i\<cdot>(sender_i x) = \<up>x"
  apply(simp add: sender_get_stream_i.rep_eq sender_i_def)
  by (metis senderElem_get_i_def senderelem_get_i_id)

lemma sender_get_stream_ds_single[simp]: "sender_get_stream_ds\<cdot>(sender_ds x) = \<up>x"
  apply(simp add: sender_get_stream_ds.rep_eq sender_ds_def)
  by (metis senderElem_get_ds_def senderelem_get_ds_id)


subsubsection \<open>In/Out\<close>

lemma sender_get_stream_as_single_in_as_id[simp]: "sender_get_stream_as\<cdot>(senderIn_as_i port_as port_i) = \<up>port_as"
  apply(simp add: sender_get_stream_as_def senderIn_as_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: senderDom_def senderElemIn_as_i_def)
  apply(cases port_as)
  apply(auto simp add: senderElem_as.simps)
  unfolding senderElem_get_as_def senderElem_raw_as.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma sender_get_stream_i_single_in_i_id[simp]: "sender_get_stream_i\<cdot>(senderIn_as_i port_as port_i) = \<up>port_i"
  apply(simp add: sender_get_stream_i_def senderIn_as_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: senderDom_def senderElemIn_as_i_def)
  apply(cases port_i)
  apply(auto simp add: senderElem_i.simps)
  unfolding senderElem_get_i_def senderElem_raw_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma sender_get_stream_ds_single_out_ds_id[simp]: "sender_get_stream_ds\<cdot>(senderOut_ds port_ds) = \<up>port_ds"
  apply(simp add: sender_get_stream_ds_def senderOut_ds_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: senderDom_def senderElemOut_ds_def)
  apply(cases port_ds)
  apply(auto simp add: senderElem_ds.simps)
  unfolding senderElem_get_ds_def senderElem_raw_ds.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma sender_stream_as_conc:
  "sender_stream_as\<cdot>(\<up>elem \<bullet> s) = ubConc (sender_as elem)\<cdot>(sender_stream_as\<cdot>s)"
  apply (rule sender_get_stream_as_eq)
  by simp_all

lemma sender_stream_i_conc:
  "sender_stream_i\<cdot>(\<up>elem \<bullet> s) = ubConc (sender_i elem)\<cdot>(sender_stream_i\<cdot>s)"
  apply (rule sender_get_stream_i_eq)
  by simp_all

lemma sender_stream_ds_conc:
  "sender_stream_ds\<cdot>(\<up>elem \<bullet> s) = ubConc (sender_ds elem)\<cdot>(sender_stream_ds\<cdot>s)"
  apply (rule sender_get_stream_ds_eq)
  by simp_all


end