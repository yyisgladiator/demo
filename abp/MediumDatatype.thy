(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory MediumDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) mediumMessage = DoNotUse_3ececf_MediumE "'e"

instance mediumMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation mediumMessage :: (countable) message
begin
  fun ctype_mediumMessage :: "channel \<Rightarrow> ('e::countable) mediumMessage set" where
  "ctype_mediumMessage c = (
    if c = \<C> ''DoNotUse_3ececf_ar'' then range DoNotUse_3ececf_MediumE else
    if c = \<C> ''DoNotUse_3ececf_as'' then range DoNotUse_3ececf_MediumE else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition mediumDom :: "channel set" where
"mediumDom = {\<C> ''DoNotUse_3ececf_ar''}"

definition mediumRan :: "channel set" where
"mediumRan = {\<C> ''DoNotUse_3ececf_as''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use mediumElemIn_ar instead *)
lift_definition mediumElem_raw_ar :: "'e \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_3ececf_ar'' \<mapsto> Msg (DoNotUse_3ececf_MediumE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use mediumElemOut_as instead *)
lift_definition mediumElem_raw_as :: "'e \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_3ececf_as'' \<mapsto> Msg (DoNotUse_3ececf_MediumE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use mediumElemIn_ar instead *)
fun mediumElem_ar :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElem_ar (Msg port_ar) = mediumElem_raw_ar port_ar" |
"mediumElem_ar null = sbeNull {\<C> ''DoNotUse_3ececf_ar''}"

(* Do not use this, use mediumElemOut_as instead *)
fun mediumElem_as :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElem_as (Msg port_as) = mediumElem_raw_as port_as" |
"mediumElem_as null = sbeNull {\<C> ''DoNotUse_3ececf_as''}"

declare mediumElem_ar.simps[simp del]

declare mediumElem_as.simps[simp del]

(* Do not use this, use mediumIn_ar instead *)
definition medium_ar :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_ar port_ar = sbe2SB (mediumElem_ar port_ar)"

(* Do not use this, use mediumOut_as instead *)
definition medium_as :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_as port_as = sbe2SB (mediumElem_as port_as)"


subsubsection \<open>In/Out\<close>

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


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use mediumIn_list_ar instead *)
fun medium_list_ar :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_list_ar (x#xs) = ubConcEq (medium_ar x)\<cdot>(medium_list_ar xs)" |
"medium_list_ar []     = ubLeast {\<C> ''DoNotUse_3ececf_ar''}"

declare medium_list_ar.simps[simp del]

(* Do not use this, use mediumOut_list_as instead *)
fun medium_list_as :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_list_as (x#xs) = ubConcEq (medium_as x)\<cdot>(medium_list_as xs)" |
"medium_list_as []     = ubLeast {\<C> ''DoNotUse_3ececf_as''}"

declare medium_list_as.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun mediumIn_list_ar :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_list_ar ((port_ar)#xs) = ubConcEq (mediumIn_ar port_ar)\<cdot>(mediumIn_list_ar xs)" |
"mediumIn_list_ar [] = ubLeast mediumDom"

(* Create one SB for all output channels *)
fun mediumOut_list_as :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_list_as ((port_as)#xs) = ubConcEq (mediumOut_as port_as)\<cdot>(mediumOut_list_as xs)" |
"mediumOut_list_as [] = ubLeast mediumRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_3ececf_medium_stream_ar_h :: "'e tsyn stream \<Rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_3ececf_ar'') \<mapsto> (tsynMap (DoNotUse_3ececf_MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use mediumIn_stream_ar instead *)
lift_definition medium_stream_ar :: "('e) tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"DoNotUse_3ececf_medium_stream_ar_h"
  apply(auto simp add: cfun_def DoNotUse_3ececf_medium_stream_ar_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_3ececf_medium_stream_ar_h.rep_eq ubrep_well)

lift_definition DoNotUse_3ececf_medium_stream_as_h :: "'e tsyn stream \<Rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_3ececf_as'') \<mapsto> (tsynMap (DoNotUse_3ececf_MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use mediumOut_stream_as instead *)
lift_definition medium_stream_as :: "('e) tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"DoNotUse_3ececf_medium_stream_as_h"
  apply(auto simp add: cfun_def DoNotUse_3ececf_medium_stream_as_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_3ececf_medium_stream_as_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition mediumIn_stream_ar :: "'e tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_stream_ar = (\<Lambda>  port_ar. (medium_stream_ar\<cdot>port_ar))"

(* Create one SB for all output channels *)
definition mediumOut_stream_as :: "'e tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_stream_as = (\<Lambda>  port_as. (medium_stream_as\<cdot>port_as))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition mediumElem_get_ar :: "('e::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_ar sbe = tsynApplyElem (inv DoNotUse_3ececf_MediumE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_3ececf_ar''))"

definition mediumElem_get_as :: "('e::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_as sbe = tsynApplyElem (inv DoNotUse_3ececf_MediumE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_3ececf_as''))"


subsection \<open>SB to stream\<close>

lift_definition medium_get_stream_ar :: "('e::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_3ececf_MediumE)\<cdot>(sb . (\<C> ''DoNotUse_3ececf_ar''))"
  by(simp add: cfun_def)

lift_definition medium_get_stream_as :: "('e::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_3ececf_MediumE)\<cdot>(sb . (\<C> ''DoNotUse_3ececf_as''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma mediumelem_ar_dom[simp]: "sbeDom (mediumElem_ar x) = {\<C> ''DoNotUse_3ececf_ar''}"
  apply(cases x)
  apply(simp add: mediumElem_ar.simps sbeDom_def mediumElem_raw_ar.rep_eq)
  by(simp add: mediumElem_ar.simps)

lemma mediumelem_as_dom[simp]: "sbeDom (mediumElem_as x) = {\<C> ''DoNotUse_3ececf_as''}"
  apply(cases x)
  apply(simp add: mediumElem_as.simps sbeDom_def mediumElem_raw_as.rep_eq)
  by(simp add: mediumElem_as.simps)

lemma medium_ar_dom[simp]: "ubDom\<cdot>(medium_ar x) = {\<C> ''DoNotUse_3ececf_ar''}"
  by(simp add: medium_ar_def)

lemma medium_ar_len[simp]: "ubLen (medium_ar x) = 1"
  by(simp add: medium_ar_def)

lemma medium_as_dom[simp]: "ubDom\<cdot>(medium_as x) = {\<C> ''DoNotUse_3ececf_as''}"
  by(simp add: medium_as_def)

lemma medium_as_len[simp]: "ubLen (medium_as x) = 1"
  by(simp add: medium_as_def)


subsubsection \<open>In/Out\<close>

lemma mediumelemin_ar_dom[simp]: "sbeDom (mediumElemIn_ar port_ar) = mediumDom"
  by(auto simp add: mediumElemIn_ar_def mediumDom_def)

lemma mediumelemout_as_dom[simp]: "sbeDom (mediumElemOut_as port_as) = mediumRan"
  by(auto simp add: mediumElemOut_as_def mediumRan_def)

lemma mediumin_ar_dom[simp]: "ubDom\<cdot>(mediumIn_ar port_ar) = mediumDom"
  by(simp add: mediumIn_ar_def)

lemma mediumin_ar_len[simp]: "ubLen (mediumIn_ar port_ar) = 1"
  by(simp add: mediumIn_ar_def mediumDom_def)

lemma mediumout_as_dom[simp]: "ubDom\<cdot>(mediumOut_as port_as) = mediumRan"
  by(simp add: mediumOut_as_def)

lemma mediumout_as_len[simp]: "ubLen (mediumOut_as port_as) = 1"
  by(simp add: mediumOut_as_def mediumRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma medium_stream_ar_dom[simp]: "ubDom\<cdot>(medium_stream_ar\<cdot>x) = {\<C> ''DoNotUse_3ececf_ar''}"
  by(simp add: medium_stream_ar.rep_eq ubdom_insert DoNotUse_3ececf_medium_stream_ar_h.rep_eq)

lemma medium_stream_ar_len[simp]: "ubLen (medium_stream_ar\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: medium_stream_ar.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_3ececf_medium_stream_ar_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma medium_stream_ar_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_3ececf_ar''} "
    shows "medium_stream_ar\<cdot>(medium_get_stream_ar\<cdot>ub) = ub"
  apply(simp add: medium_stream_ar.rep_eq medium_get_stream_ar.rep_eq)
  apply(simp add: DoNotUse_3ececf_medium_stream_ar_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma medium_stream_as_dom[simp]: "ubDom\<cdot>(medium_stream_as\<cdot>x) = {\<C> ''DoNotUse_3ececf_as''}"
  by(simp add: medium_stream_as.rep_eq ubdom_insert DoNotUse_3ececf_medium_stream_as_h.rep_eq)

lemma medium_stream_as_len[simp]: "ubLen (medium_stream_as\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: medium_stream_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_3ececf_medium_stream_as_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma medium_stream_as_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_3ececf_as''} "
    shows "medium_stream_as\<cdot>(medium_get_stream_as\<cdot>ub) = ub"
  apply(simp add: medium_stream_as.rep_eq medium_get_stream_as.rep_eq)
  apply(simp add: DoNotUse_3ececf_medium_stream_as_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma mediumin_stream_ar_dom[simp]: "ubDom\<cdot>(mediumIn_stream_ar\<cdot>port_ar) = mediumDom"
  apply(simp add: mediumIn_stream_ar_def ubclUnion_ubundle_def)
  by(auto simp add: mediumDom_def)

lemma mediumout_stream_as_dom[simp]: "ubDom\<cdot>(mediumOut_stream_as\<cdot>port_as) = mediumRan"
  apply(simp add: mediumOut_stream_as_def ubclUnion_ubundle_def)
  by(auto simp add: mediumRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma mediumelem_get_ar_id[simp]: "mediumElem_get_ar (mediumElem_ar x) = x"
  apply(cases x)
  apply(auto simp add: mediumElem_ar.simps)
  unfolding mediumElem_get_ar_def mediumElem_raw_ar.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI mediumMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma mediumelem_get_as_id[simp]: "mediumElem_get_as (mediumElem_as x) = x"
  apply(cases x)
  apply(auto simp add: mediumElem_as.simps)
  unfolding mediumElem_get_as_def mediumElem_raw_as.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI mediumMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma mediumelem_get_ar_in_ar_id[simp]: "mediumElem_get_ar (mediumElemIn_ar port_ar) = port_ar"
  apply(simp add: mediumElemIn_ar_def mediumElem_get_ar_def)
  by(metis mediumElem_get_ar_def mediumelem_get_ar_id)

lemma mediumelem_get_as_out_as_id[simp]: "mediumElem_get_as (mediumElemOut_as port_as) = port_as"
  apply(simp add: mediumElemOut_as_def mediumElem_get_as_def)
  by(metis mediumElem_get_as_def mediumelem_get_as_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma medium_get_stream_ar_id[simp]: "medium_get_stream_ar\<cdot>(medium_stream_ar\<cdot>x) = x"
  apply(simp add: medium_get_stream_ar.rep_eq medium_stream_ar.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_3ececf_medium_stream_ar_h.rep_eq)
  by (simp add: inj_def)

lemma medium_get_stream_ar_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_3ececf_ar''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_3ececf_ar''}"
      and "medium_get_stream_ar\<cdot>ub1 = medium_get_stream_ar\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) medium_stream_ar_id by metis

lemma medium_get_stream_ar_conc[simp]:
  assumes "\<C> ''DoNotUse_3ececf_ar'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_3ececf_ar'' \<in> ubDom\<cdot>ub2"
    shows "medium_get_stream_ar\<cdot>(ubConc ub1\<cdot>ub2) = (medium_get_stream_ar\<cdot>ub1) \<bullet> (medium_get_stream_ar\<cdot>ub2)"
  apply(simp add: medium_get_stream_ar.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma medium_get_stream_as_id[simp]: "medium_get_stream_as\<cdot>(medium_stream_as\<cdot>x) = x"
  apply(simp add: medium_get_stream_as.rep_eq medium_stream_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_3ececf_medium_stream_as_h.rep_eq)
  by (simp add: inj_def)

lemma medium_get_stream_as_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_3ececf_as''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_3ececf_as''}"
      and "medium_get_stream_as\<cdot>ub1 = medium_get_stream_as\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) medium_stream_as_id by metis

lemma medium_get_stream_as_conc[simp]:
  assumes "\<C> ''DoNotUse_3ececf_as'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_3ececf_as'' \<in> ubDom\<cdot>ub2"
    shows "medium_get_stream_as\<cdot>(ubConc ub1\<cdot>ub2) = (medium_get_stream_as\<cdot>ub1) \<bullet> (medium_get_stream_as\<cdot>ub2)"
  apply(simp add: medium_get_stream_as.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma medium_get_stream_ar_in_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_stream_ar\<cdot>port_ar) = port_ar"
  apply(auto simp add: medium_get_stream_ar.rep_eq mediumIn_stream_ar_def ubclUnion_ubundle_def)
  by (metis medium_get_stream_ar.rep_eq medium_get_stream_ar_id)

lemma medium_get_stream_as_out_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_stream_as\<cdot>port_as) = port_as"
  apply(auto simp add: medium_get_stream_as.rep_eq mediumOut_stream_as_def ubclUnion_ubundle_def)
  by (metis medium_get_stream_as.rep_eq medium_get_stream_as_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma medium_get_stream_ar_single[simp]: "medium_get_stream_ar\<cdot>(medium_ar x) = \<up>x"
  apply(simp add: medium_get_stream_ar.rep_eq medium_ar_def)
  by (metis mediumElem_get_ar_def mediumelem_get_ar_id)

lemma medium_get_stream_as_single[simp]: "medium_get_stream_as\<cdot>(medium_as x) = \<up>x"
  apply(simp add: medium_get_stream_as.rep_eq medium_as_def)
  by (metis mediumElem_get_as_def mediumelem_get_as_id)


subsubsection \<open>In/Out\<close>

lemma medium_get_stream_ar_single_in_ar_id[simp]: "medium_get_stream_ar\<cdot>(mediumIn_ar port_ar) = \<up>port_ar"
  apply(simp add: medium_get_stream_ar_def mediumIn_ar_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: mediumDom_def mediumElemIn_ar_def)
  apply(cases port_ar)
  apply(auto simp add: mediumElem_ar.simps)
  unfolding mediumElem_get_ar_def mediumElem_raw_ar.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma medium_get_stream_as_single_out_as_id[simp]: "medium_get_stream_as\<cdot>(mediumOut_as port_as) = \<up>port_as"
  apply(simp add: medium_get_stream_as_def mediumOut_as_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: mediumDom_def mediumElemOut_as_def)
  apply(cases port_as)
  apply(auto simp add: mediumElem_as.simps)
  unfolding mediumElem_get_as_def mediumElem_raw_as.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma medium_stream_ar_conc:
  "medium_stream_ar\<cdot>(\<up>elem \<bullet> s) = ubConc (medium_ar elem)\<cdot>(medium_stream_ar\<cdot>s)"
  apply (rule medium_get_stream_ar_eq)
  by simp_all

lemma medium_stream_as_conc:
  "medium_stream_as\<cdot>(\<up>elem \<bullet> s) = ubConc (medium_as elem)\<cdot>(medium_stream_as\<cdot>s)"
  apply (rule medium_get_stream_as_eq)
  by simp_all


end