(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory ReceiverDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) receiverMessage = DoNotUse_8ccffd_ReceiverPair_E_Bool "('e\<times>bool)" | DoNotUse_8ccffd_ReceiverBool "bool" | DoNotUse_8ccffd_ReceiverE "'e"

instance receiverMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation receiverMessage :: (countable) message
begin
  fun ctype_receiverMessage :: "channel \<Rightarrow> ('e::countable) receiverMessage set" where
  "ctype_receiverMessage c = (
    if c = \<C> ''DoNotUse_8ccffd_dr'' then range DoNotUse_8ccffd_ReceiverPair_E_Bool else
    if c = \<C> ''DoNotUse_8ccffd_ar'' then range DoNotUse_8ccffd_ReceiverBool else
    if c = \<C> ''DoNotUse_8ccffd_o'' then range DoNotUse_8ccffd_ReceiverE else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition receiverDom :: "channel set" where
"receiverDom = {\<C> ''DoNotUse_8ccffd_dr''}"

definition receiverRan :: "channel set" where
"receiverRan = {\<C> ''DoNotUse_8ccffd_ar'', \<C> ''DoNotUse_8ccffd_o''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use receiverElemIn_dr instead *)
lift_definition receiverElem_raw_dr :: "('e\<times>bool) \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_8ccffd_dr'' \<mapsto> Msg (DoNotUse_8ccffd_ReceiverPair_E_Bool x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use receiverElemOut_ar_o instead *)
lift_definition receiverElem_raw_ar :: "bool \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_8ccffd_ar'' \<mapsto> Msg (DoNotUse_8ccffd_ReceiverBool x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use receiverElemOut_ar_o instead *)
lift_definition receiverElem_raw_o :: "'e \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_8ccffd_o'' \<mapsto> Msg (DoNotUse_8ccffd_ReceiverE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use receiverElemIn_dr instead *)
fun receiverElem_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElem_dr (Msg port_dr) = receiverElem_raw_dr port_dr" |
"receiverElem_dr null = sbeNull {\<C> ''DoNotUse_8ccffd_dr''}"

(* Do not use this, use receiverElemOut_ar_o instead *)
fun receiverElem_ar :: "bool tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElem_ar (Msg port_ar) = receiverElem_raw_ar port_ar" |
"receiverElem_ar null = sbeNull {\<C> ''DoNotUse_8ccffd_ar''}"

(* Do not use this, use receiverElemOut_ar_o instead *)
fun receiverElem_o :: "'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElem_o (Msg port_o) = receiverElem_raw_o port_o" |
"receiverElem_o null = sbeNull {\<C> ''DoNotUse_8ccffd_o''}"

declare receiverElem_dr.simps[simp del]

declare receiverElem_ar.simps[simp del]

declare receiverElem_o.simps[simp del]

(* Do not use this, use receiverIn_dr instead *)
definition receiver_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_dr port_dr = sbe2SB (receiverElem_dr port_dr)"

(* Do not use this, use receiverOut_ar_o instead *)
definition receiver_ar :: "bool tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_ar port_ar = sbe2SB (receiverElem_ar port_ar)"

(* Do not use this, use receiverOut_ar_o instead *)
definition receiver_o :: "'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_o port_o = sbe2SB (receiverElem_o port_o)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition receiverElemIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElemIn_dr port_dr = (receiverElem_dr port_dr)"

(* Create one sbElem for all output channels *)
definition receiverElemOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElemOut_ar_o port_ar port_o = (receiverElem_ar port_ar) \<plusminus> (receiverElem_o port_o)"

(* Create one SB for all input channels *)
definition receiverIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverIn_dr port_dr = (sbe2SB (receiverElemIn_dr port_dr))"

(* Create one SB for all output channels *)
definition receiverOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverOut_ar_o port_ar port_o = (sbe2SB (receiverElemOut_ar_o port_ar port_o))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use receiverIn_list_dr instead *)
fun receiver_list_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_list_dr (x#xs) = ubConcEq (receiver_dr x)\<cdot>(receiver_list_dr xs)" |
"receiver_list_dr []     = ubLeast {\<C> ''DoNotUse_8ccffd_dr''}"

declare receiver_list_dr.simps[simp del]

(* Do not use this, use receiverOut_list_ar_o instead *)
fun receiver_list_ar :: "(bool tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_list_ar (x#xs) = ubConcEq (receiver_ar x)\<cdot>(receiver_list_ar xs)" |
"receiver_list_ar []     = ubLeast {\<C> ''DoNotUse_8ccffd_ar''}"

declare receiver_list_ar.simps[simp del]

(* Do not use this, use receiverOut_list_ar_o instead *)
fun receiver_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_list_o (x#xs) = ubConcEq (receiver_o x)\<cdot>(receiver_list_o xs)" |
"receiver_list_o []     = ubLeast {\<C> ''DoNotUse_8ccffd_o''}"

declare receiver_list_o.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun receiverIn_list_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverIn_list_dr ((port_dr)#xs) = ubConcEq (receiverIn_dr port_dr)\<cdot>(receiverIn_list_dr xs)" |
"receiverIn_list_dr [] = ubLeast receiverDom"

(* Create one SB for all output channels *)
fun receiverOut_list_ar_o :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverOut_list_ar_o ((port_ar,port_o)#xs) = ubConcEq (receiverOut_ar_o port_ar port_o)\<cdot>(receiverOut_list_ar_o xs)" |
"receiverOut_list_ar_o [] = ubLeast receiverRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_8ccffd_receiver_stream_dr_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_8ccffd_dr'') \<mapsto> (tsynMap (DoNotUse_8ccffd_ReceiverPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use receiverIn_stream_dr instead *)
lift_definition receiver_stream_dr :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" is
"DoNotUse_8ccffd_receiver_stream_dr_h"
  apply(auto simp add: cfun_def DoNotUse_8ccffd_receiver_stream_dr_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_8ccffd_receiver_stream_dr_h.rep_eq ubrep_well)

lift_definition DoNotUse_8ccffd_receiver_stream_ar_h :: "bool tsyn stream \<Rightarrow> ('e::countable) receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_8ccffd_ar'') \<mapsto> (tsynMap (DoNotUse_8ccffd_ReceiverBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use receiverOut_stream_ar_o instead *)
lift_definition receiver_stream_ar :: "(bool) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" is
"DoNotUse_8ccffd_receiver_stream_ar_h"
  apply(auto simp add: cfun_def DoNotUse_8ccffd_receiver_stream_ar_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_8ccffd_receiver_stream_ar_h.rep_eq ubrep_well)

lift_definition DoNotUse_8ccffd_receiver_stream_o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_8ccffd_o'') \<mapsto> (tsynMap (DoNotUse_8ccffd_ReceiverE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use receiverOut_stream_ar_o instead *)
lift_definition receiver_stream_o :: "('e) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" is
"DoNotUse_8ccffd_receiver_stream_o_h"
  apply(auto simp add: cfun_def DoNotUse_8ccffd_receiver_stream_o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_8ccffd_receiver_stream_o_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition receiverIn_stream_dr :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverIn_stream_dr = (\<Lambda>  port_dr. (receiver_stream_dr\<cdot>port_dr))"

(* Create one SB for all output channels *)
definition receiverOut_stream_ar_o :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverOut_stream_ar_o = (\<Lambda>  port_ar port_o. (receiver_stream_ar\<cdot>port_ar) \<uplus> (receiver_stream_o\<cdot>port_o))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition receiverElem_get_dr :: "('e::countable) receiverMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"receiverElem_get_dr sbe = tsynApplyElem (inv DoNotUse_8ccffd_ReceiverPair_E_Bool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_8ccffd_dr''))"

definition receiverElem_get_ar :: "('e::countable) receiverMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"receiverElem_get_ar sbe = tsynApplyElem (inv DoNotUse_8ccffd_ReceiverBool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_8ccffd_ar''))"

definition receiverElem_get_o :: "('e::countable) receiverMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"receiverElem_get_o sbe = tsynApplyElem (inv DoNotUse_8ccffd_ReceiverE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_8ccffd_o''))"


subsection \<open>SB to stream\<close>

lift_definition receiver_get_stream_dr :: "('e::countable) receiverMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_8ccffd_ReceiverPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_8ccffd_dr''))"
  by(simp add: cfun_def)

lift_definition receiver_get_stream_ar :: "('e::countable) receiverMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_8ccffd_ReceiverBool)\<cdot>(sb . (\<C> ''DoNotUse_8ccffd_ar''))"
  by(simp add: cfun_def)

lift_definition receiver_get_stream_o :: "('e::countable) receiverMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_8ccffd_ReceiverE)\<cdot>(sb . (\<C> ''DoNotUse_8ccffd_o''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma receiverelem_dr_dom[simp]: "sbeDom (receiverElem_dr x) = {\<C> ''DoNotUse_8ccffd_dr''}"
  apply(cases x)
  apply(simp add: receiverElem_dr.simps sbeDom_def receiverElem_raw_dr.rep_eq)
  by(simp add: receiverElem_dr.simps)

lemma receiverelem_ar_dom[simp]: "sbeDom (receiverElem_ar x) = {\<C> ''DoNotUse_8ccffd_ar''}"
  apply(cases x)
  apply(simp add: receiverElem_ar.simps sbeDom_def receiverElem_raw_ar.rep_eq)
  by(simp add: receiverElem_ar.simps)

lemma receiverelem_o_dom[simp]: "sbeDom (receiverElem_o x) = {\<C> ''DoNotUse_8ccffd_o''}"
  apply(cases x)
  apply(simp add: receiverElem_o.simps sbeDom_def receiverElem_raw_o.rep_eq)
  by(simp add: receiverElem_o.simps)

lemma receiver_dr_dom[simp]: "ubDom\<cdot>(receiver_dr x) = {\<C> ''DoNotUse_8ccffd_dr''}"
  by(simp add: receiver_dr_def)

lemma receiver_dr_len[simp]: "ubLen (receiver_dr x) = 1"
  by(simp add: receiver_dr_def)

lemma receiver_ar_dom[simp]: "ubDom\<cdot>(receiver_ar x) = {\<C> ''DoNotUse_8ccffd_ar''}"
  by(simp add: receiver_ar_def)

lemma receiver_ar_len[simp]: "ubLen (receiver_ar x) = 1"
  by(simp add: receiver_ar_def)

lemma receiver_o_dom[simp]: "ubDom\<cdot>(receiver_o x) = {\<C> ''DoNotUse_8ccffd_o''}"
  by(simp add: receiver_o_def)

lemma receiver_o_len[simp]: "ubLen (receiver_o x) = 1"
  by(simp add: receiver_o_def)


subsubsection \<open>In/Out\<close>

lemma receiverelemin_dr_dom[simp]: "sbeDom (receiverElemIn_dr port_dr) = receiverDom"
  by(auto simp add: receiverElemIn_dr_def receiverDom_def)

lemma receiverelemout_ar_o_dom[simp]: "sbeDom (receiverElemOut_ar_o port_ar port_o) = receiverRan"
  by(auto simp add: receiverElemOut_ar_o_def receiverRan_def)

lemma receiverin_dr_dom[simp]: "ubDom\<cdot>(receiverIn_dr port_dr) = receiverDom"
  by(simp add: receiverIn_dr_def)

lemma receiverin_dr_len[simp]: "ubLen (receiverIn_dr port_dr) = 1"
  by(simp add: receiverIn_dr_def receiverDom_def)

lemma receiverout_ar_o_dom[simp]: "ubDom\<cdot>(receiverOut_ar_o port_ar port_o) = receiverRan"
  by(simp add: receiverOut_ar_o_def)

lemma receiverout_ar_o_len[simp]: "ubLen (receiverOut_ar_o port_ar port_o) = 1"
  by(simp add: receiverOut_ar_o_def receiverRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma receiver_stream_dr_dom[simp]: "ubDom\<cdot>(receiver_stream_dr\<cdot>x) = {\<C> ''DoNotUse_8ccffd_dr''}"
  by(simp add: receiver_stream_dr.rep_eq ubdom_insert DoNotUse_8ccffd_receiver_stream_dr_h.rep_eq)

lemma receiver_stream_dr_len[simp]: "ubLen (receiver_stream_dr\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: receiver_stream_dr.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8ccffd_receiver_stream_dr_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma receiver_stream_dr_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_8ccffd_dr''} "
    shows "receiver_stream_dr\<cdot>(receiver_get_stream_dr\<cdot>ub) = ub"
  apply(simp add: receiver_stream_dr.rep_eq receiver_get_stream_dr.rep_eq)
  apply(simp add: DoNotUse_8ccffd_receiver_stream_dr_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma receiver_stream_ar_dom[simp]: "ubDom\<cdot>(receiver_stream_ar\<cdot>x) = {\<C> ''DoNotUse_8ccffd_ar''}"
  by(simp add: receiver_stream_ar.rep_eq ubdom_insert DoNotUse_8ccffd_receiver_stream_ar_h.rep_eq)

lemma receiver_stream_ar_len[simp]: "ubLen (receiver_stream_ar\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: receiver_stream_ar.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8ccffd_receiver_stream_ar_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma receiver_stream_ar_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_8ccffd_ar''} "
    shows "receiver_stream_ar\<cdot>(receiver_get_stream_ar\<cdot>ub) = ub"
  apply(simp add: receiver_stream_ar.rep_eq receiver_get_stream_ar.rep_eq)
  apply(simp add: DoNotUse_8ccffd_receiver_stream_ar_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma receiver_stream_o_dom[simp]: "ubDom\<cdot>(receiver_stream_o\<cdot>x) = {\<C> ''DoNotUse_8ccffd_o''}"
  by(simp add: receiver_stream_o.rep_eq ubdom_insert DoNotUse_8ccffd_receiver_stream_o_h.rep_eq)

lemma receiver_stream_o_len[simp]: "ubLen (receiver_stream_o\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: receiver_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8ccffd_receiver_stream_o_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma receiver_stream_o_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_8ccffd_o''} "
    shows "receiver_stream_o\<cdot>(receiver_get_stream_o\<cdot>ub) = ub"
  apply(simp add: receiver_stream_o.rep_eq receiver_get_stream_o.rep_eq)
  apply(simp add: DoNotUse_8ccffd_receiver_stream_o_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma receiverin_stream_dr_dom[simp]: "ubDom\<cdot>(receiverIn_stream_dr\<cdot>port_dr) = receiverDom"
  apply(simp add: receiverIn_stream_dr_def ubclUnion_ubundle_def)
  by(auto simp add: receiverDom_def)

lemma receiverout_stream_ar_o_dom[simp]: "ubDom\<cdot>(receiverOut_stream_ar_o\<cdot>port_ar\<cdot>port_o) = receiverRan"
  apply(simp add: receiverOut_stream_ar_o_def ubclUnion_ubundle_def)
  by(auto simp add: receiverRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma receiverelem_get_dr_id[simp]: "receiverElem_get_dr (receiverElem_dr x) = x"
  apply(cases x)
  apply(auto simp add: receiverElem_dr.simps)
  unfolding receiverElem_get_dr_def receiverElem_raw_dr.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI receiverMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma receiverelem_get_ar_id[simp]: "receiverElem_get_ar (receiverElem_ar x) = x"
  apply(cases x)
  apply(auto simp add: receiverElem_ar.simps)
  unfolding receiverElem_get_ar_def receiverElem_raw_ar.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI receiverMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma receiverelem_get_o_id[simp]: "receiverElem_get_o (receiverElem_o x) = x"
  apply(cases x)
  apply(auto simp add: receiverElem_o.simps)
  unfolding receiverElem_get_o_def receiverElem_raw_o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI receiverMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma receiverelem_get_dr_in_dr_id[simp]: "receiverElem_get_dr (receiverElemIn_dr port_dr) = port_dr"
  apply(simp add: receiverElemIn_dr_def receiverElem_get_dr_def)
  by(metis receiverElem_get_dr_def receiverelem_get_dr_id)

lemma receiverelem_get_ar_out_ar_id[simp]: "receiverElem_get_ar (receiverElemOut_ar_o port_ar port_o) = port_ar"
  apply(simp add: receiverElemOut_ar_o_def receiverElem_get_ar_def)
  by(metis receiverElem_get_ar_def receiverelem_get_ar_id)

lemma receiverelem_get_o_out_o_id[simp]: "receiverElem_get_o (receiverElemOut_ar_o port_ar port_o) = port_o"
  apply(simp add: receiverElemOut_ar_o_def receiverElem_get_o_def)
  by(metis receiverElem_get_o_def receiverelem_get_o_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma receiver_get_stream_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiver_stream_dr\<cdot>x) = x"
  apply(simp add: receiver_get_stream_dr.rep_eq receiver_stream_dr.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8ccffd_receiver_stream_dr_h.rep_eq)
  by (simp add: inj_def)

lemma receiver_get_stream_dr_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_8ccffd_dr''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_8ccffd_dr''}"
      and "receiver_get_stream_dr\<cdot>ub1 = receiver_get_stream_dr\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) receiver_stream_dr_id by metis

lemma receiver_get_stream_dr_conc[simp]:
  assumes "\<C> ''DoNotUse_8ccffd_dr'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_8ccffd_dr'' \<in> ubDom\<cdot>ub2"
    shows "receiver_get_stream_dr\<cdot>(ubConc ub1\<cdot>ub2) = (receiver_get_stream_dr\<cdot>ub1) \<bullet> (receiver_get_stream_dr\<cdot>ub2)"
  apply(simp add: receiver_get_stream_dr.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma receiver_get_stream_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiver_stream_ar\<cdot>x) = x"
  apply(simp add: receiver_get_stream_ar.rep_eq receiver_stream_ar.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8ccffd_receiver_stream_ar_h.rep_eq)
  by (simp add: inj_def)

lemma receiver_get_stream_ar_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_8ccffd_ar''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_8ccffd_ar''}"
      and "receiver_get_stream_ar\<cdot>ub1 = receiver_get_stream_ar\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) receiver_stream_ar_id by metis

lemma receiver_get_stream_ar_conc[simp]:
  assumes "\<C> ''DoNotUse_8ccffd_ar'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_8ccffd_ar'' \<in> ubDom\<cdot>ub2"
    shows "receiver_get_stream_ar\<cdot>(ubConc ub1\<cdot>ub2) = (receiver_get_stream_ar\<cdot>ub1) \<bullet> (receiver_get_stream_ar\<cdot>ub2)"
  apply(simp add: receiver_get_stream_ar.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma receiver_get_stream_o_id[simp]: "receiver_get_stream_o\<cdot>(receiver_stream_o\<cdot>x) = x"
  apply(simp add: receiver_get_stream_o.rep_eq receiver_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8ccffd_receiver_stream_o_h.rep_eq)
  by (simp add: inj_def)

lemma receiver_get_stream_o_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_8ccffd_o''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_8ccffd_o''}"
      and "receiver_get_stream_o\<cdot>ub1 = receiver_get_stream_o\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) receiver_stream_o_id by metis

lemma receiver_get_stream_o_conc[simp]:
  assumes "\<C> ''DoNotUse_8ccffd_o'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_8ccffd_o'' \<in> ubDom\<cdot>ub2"
    shows "receiver_get_stream_o\<cdot>(ubConc ub1\<cdot>ub2) = (receiver_get_stream_o\<cdot>ub1) \<bullet> (receiver_get_stream_o\<cdot>ub2)"
  apply(simp add: receiver_get_stream_o.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma receiver_get_stream_dr_in_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiverIn_stream_dr\<cdot>port_dr) = port_dr"
  apply(auto simp add: receiver_get_stream_dr.rep_eq receiverIn_stream_dr_def ubclUnion_ubundle_def)
  by (metis receiver_get_stream_dr.rep_eq receiver_get_stream_dr_id)

lemma receiver_get_stream_ar_out_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_stream_ar_o\<cdot>port_ar\<cdot>port_o) = port_ar"
  apply(auto simp add: receiver_get_stream_ar.rep_eq receiverOut_stream_ar_o_def ubclUnion_ubundle_def)
  by (metis receiver_get_stream_ar.rep_eq receiver_get_stream_ar_id)

lemma receiver_get_stream_o_out_o_id[simp]: "receiver_get_stream_o\<cdot>(receiverOut_stream_ar_o\<cdot>port_ar\<cdot>port_o) = port_o"
  apply(auto simp add: receiver_get_stream_o.rep_eq receiverOut_stream_ar_o_def ubclUnion_ubundle_def)
  by (metis receiver_get_stream_o.rep_eq receiver_get_stream_o_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma receiver_get_stream_dr_single[simp]: "receiver_get_stream_dr\<cdot>(receiver_dr x) = \<up>x"
  apply(simp add: receiver_get_stream_dr.rep_eq receiver_dr_def)
  by (metis receiverElem_get_dr_def receiverelem_get_dr_id)

lemma receiver_get_stream_ar_single[simp]: "receiver_get_stream_ar\<cdot>(receiver_ar x) = \<up>x"
  apply(simp add: receiver_get_stream_ar.rep_eq receiver_ar_def)
  by (metis receiverElem_get_ar_def receiverelem_get_ar_id)

lemma receiver_get_stream_o_single[simp]: "receiver_get_stream_o\<cdot>(receiver_o x) = \<up>x"
  apply(simp add: receiver_get_stream_o.rep_eq receiver_o_def)
  by (metis receiverElem_get_o_def receiverelem_get_o_id)


subsubsection \<open>In/Out\<close>

lemma receiver_get_stream_dr_single_in_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiverIn_dr port_dr) = \<up>port_dr"
  apply(simp add: receiver_get_stream_dr_def receiverIn_dr_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: receiverDom_def receiverElemIn_dr_def)
  apply(cases port_dr)
  apply(auto simp add: receiverElem_dr.simps)
  unfolding receiverElem_get_dr_def receiverElem_raw_dr.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma receiver_get_stream_ar_single_out_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_ar_o port_ar port_o) = \<up>port_ar"
  apply(simp add: receiver_get_stream_ar_def receiverOut_ar_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: receiverDom_def receiverElemOut_ar_o_def)
  apply(cases port_ar)
  apply(auto simp add: receiverElem_ar.simps)
  unfolding receiverElem_get_ar_def receiverElem_raw_ar.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma receiver_get_stream_o_single_out_o_id[simp]: "receiver_get_stream_o\<cdot>(receiverOut_ar_o port_ar port_o) = \<up>port_o"
  apply(simp add: receiver_get_stream_o_def receiverOut_ar_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: receiverDom_def receiverElemOut_ar_o_def)
  apply(cases port_o)
  apply(auto simp add: receiverElem_o.simps)
  unfolding receiverElem_get_o_def receiverElem_raw_o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma receiver_stream_dr_conc:
  "receiver_stream_dr\<cdot>(\<up>elem \<bullet> s) = ubConc (receiver_dr elem)\<cdot>(receiver_stream_dr\<cdot>s)"
  apply (rule receiver_get_stream_dr_eq)
  by simp_all

lemma receiver_stream_ar_conc:
  "receiver_stream_ar\<cdot>(\<up>elem \<bullet> s) = ubConc (receiver_ar elem)\<cdot>(receiver_stream_ar\<cdot>s)"
  apply (rule receiver_get_stream_ar_eq)
  by simp_all

lemma receiver_stream_o_conc:
  "receiver_stream_o\<cdot>(\<up>elem \<bullet> s) = ubConc (receiver_o elem)\<cdot>(receiver_stream_o\<cdot>s)"
  apply (rule receiver_get_stream_o_eq)
  by simp_all


end