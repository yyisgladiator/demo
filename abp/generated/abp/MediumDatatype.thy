(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:32 PM by isartransformer 2.0.0
 *)
theory MediumDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) mediumMessage = DoNotUse_621ccf_MediumE "'e"

instance mediumMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation mediumMessage :: (countable) message
begin
  fun ctype_mediumMessage :: "channel \<Rightarrow> ('e::countable) mediumMessage set" where
  "ctype_mediumMessage c = (
    if c = \<C> ''DoNotUse_621ccf_i'' then range DoNotUse_621ccf_MediumE else
    if c = \<C> ''DoNotUse_621ccf_o'' then range DoNotUse_621ccf_MediumE else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition mediumDom :: "channel set" where
"mediumDom = {\<C> ''DoNotUse_621ccf_i''}"

definition mediumRan :: "channel set" where
"mediumRan = {\<C> ''DoNotUse_621ccf_o''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use mediumElemIn_i instead *)
lift_definition mediumElem_raw_i :: "'e \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_621ccf_i'' \<mapsto> Msg (DoNotUse_621ccf_MediumE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use mediumElemOut_o instead *)
lift_definition mediumElem_raw_o :: "'e \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_621ccf_o'' \<mapsto> Msg (DoNotUse_621ccf_MediumE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use mediumElemIn_i instead *)
fun mediumElem_i :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElem_i (Msg port_i) = mediumElem_raw_i port_i" |
"mediumElem_i null = sbeNull {\<C> ''DoNotUse_621ccf_i''}"

(* Do not use this, use mediumElemOut_o instead *)
fun mediumElem_o :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElem_o (Msg port_o) = mediumElem_raw_o port_o" |
"mediumElem_o null = sbeNull {\<C> ''DoNotUse_621ccf_o''}"

declare mediumElem_i.simps[simp del]

declare mediumElem_o.simps[simp del]

(* Do not use this, use mediumIn_i instead *)
definition medium_i :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_i port_i = sbe2SB (mediumElem_i port_i)"

(* Do not use this, use mediumOut_o instead *)
definition medium_o :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_o port_o = sbe2SB (mediumElem_o port_o)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition mediumElemIn_i :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElemIn_i port_i = (mediumElem_i port_i)"

(* Create one sbElem for all output channels *)
definition mediumElemOut_o :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn sbElem" where
"mediumElemOut_o port_o = (mediumElem_o port_o)"

(* Create one SB for all input channels *)
definition mediumIn_i :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_i port_i = (sbe2SB (mediumElemIn_i port_i))"

(* Create one SB for all output channels *)
definition mediumOut_o :: "'e tsyn \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_o port_o = (sbe2SB (mediumElemOut_o port_o))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use mediumIn_list_i instead *)
fun medium_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_list_i (x#xs) = ubConcEq (medium_i x)\<cdot>(medium_list_i xs)" |
"medium_list_i []     = ubLeast {\<C> ''DoNotUse_621ccf_i''}"

declare medium_list_i.simps[simp del]

(* Do not use this, use mediumOut_list_o instead *)
fun medium_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"medium_list_o (x#xs) = ubConcEq (medium_o x)\<cdot>(medium_list_o xs)" |
"medium_list_o []     = ubLeast {\<C> ''DoNotUse_621ccf_o''}"

declare medium_list_o.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun mediumIn_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_list_i ((port_i)#xs) = ubConcEq (mediumIn_i port_i)\<cdot>(mediumIn_list_i xs)" |
"mediumIn_list_i [] = ubLeast mediumDom"

(* Create one SB for all output channels *)
fun mediumOut_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_list_o ((port_o)#xs) = ubConcEq (mediumOut_o port_o)\<cdot>(mediumOut_list_o xs)" |
"mediumOut_list_o [] = ubLeast mediumRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_621ccf_medium_stream_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_621ccf_i'') \<mapsto> (tsynMap (DoNotUse_621ccf_MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use mediumIn_stream_i instead *)
lift_definition medium_stream_i :: "('e) tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"DoNotUse_621ccf_medium_stream_i_h"
  apply(auto simp add: cfun_def DoNotUse_621ccf_medium_stream_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_621ccf_medium_stream_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_621ccf_medium_stream_o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_621ccf_o'') \<mapsto> (tsynMap (DoNotUse_621ccf_MediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use mediumOut_stream_o instead *)
lift_definition medium_stream_o :: "('e) tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"DoNotUse_621ccf_medium_stream_o_h"
  apply(auto simp add: cfun_def DoNotUse_621ccf_medium_stream_o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_621ccf_medium_stream_o_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition mediumIn_stream_i :: "'e tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumIn_stream_i = (\<Lambda>  port_i. (medium_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition mediumOut_stream_o :: "'e tsyn stream \<rightarrow> ('e::countable) mediumMessage tsyn SB" where
"mediumOut_stream_o = (\<Lambda>  port_o. (medium_stream_o\<cdot>port_o))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition mediumElem_get_i :: "('e::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_i sbe = tsynApplyElem (inv DoNotUse_621ccf_MediumE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_621ccf_i''))"

definition mediumElem_get_o :: "('e::countable) mediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"mediumElem_get_o sbe = tsynApplyElem (inv DoNotUse_621ccf_MediumE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_621ccf_o''))"


subsection \<open>SB to stream\<close>

lift_definition medium_get_stream_i :: "('e::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_621ccf_MediumE)\<cdot>(sb . (\<C> ''DoNotUse_621ccf_i''))"
  by(simp add: cfun_def)

lift_definition medium_get_stream_o :: "('e::countable) mediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_621ccf_MediumE)\<cdot>(sb . (\<C> ''DoNotUse_621ccf_o''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma mediumelem_i_dom[simp]: "sbeDom (mediumElem_i x) = {\<C> ''DoNotUse_621ccf_i''}"
  apply(cases x)
  apply(simp add: mediumElem_i.simps sbeDom_def mediumElem_raw_i.rep_eq)
  by(simp add: mediumElem_i.simps)

lemma mediumelem_o_dom[simp]: "sbeDom (mediumElem_o x) = {\<C> ''DoNotUse_621ccf_o''}"
  apply(cases x)
  apply(simp add: mediumElem_o.simps sbeDom_def mediumElem_raw_o.rep_eq)
  by(simp add: mediumElem_o.simps)

lemma medium_i_dom[simp]: "ubDom\<cdot>(medium_i x) = {\<C> ''DoNotUse_621ccf_i''}"
  by(simp add: medium_i_def)

lemma medium_i_len[simp]: "ubLen (medium_i x) = 1"
  by(simp add: medium_i_def)

lemma medium_o_dom[simp]: "ubDom\<cdot>(medium_o x) = {\<C> ''DoNotUse_621ccf_o''}"
  by(simp add: medium_o_def)

lemma medium_o_len[simp]: "ubLen (medium_o x) = 1"
  by(simp add: medium_o_def)


subsubsection \<open>In/Out\<close>

lemma mediumelemin_i_dom[simp]: "sbeDom (mediumElemIn_i port_i) = mediumDom"
  by(auto simp add: mediumElemIn_i_def mediumDom_def)

lemma mediumelemout_o_dom[simp]: "sbeDom (mediumElemOut_o port_o) = mediumRan"
  by(auto simp add: mediumElemOut_o_def mediumRan_def)

lemma mediumin_i_dom[simp]: "ubDom\<cdot>(mediumIn_i port_i) = mediumDom"
  by(simp add: mediumIn_i_def)

lemma mediumin_i_len[simp]: "ubLen (mediumIn_i port_i) = 1"
  by(simp add: mediumIn_i_def mediumDom_def)

lemma mediumout_o_dom[simp]: "ubDom\<cdot>(mediumOut_o port_o) = mediumRan"
  by(simp add: mediumOut_o_def)

lemma mediumout_o_len[simp]: "ubLen (mediumOut_o port_o) = 1"
  by(simp add: mediumOut_o_def mediumRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma medium_stream_i_dom[simp]: "ubDom\<cdot>(medium_stream_i\<cdot>x) = {\<C> ''DoNotUse_621ccf_i''}"
  by(simp add: medium_stream_i.rep_eq ubdom_insert DoNotUse_621ccf_medium_stream_i_h.rep_eq)

lemma medium_stream_i_len[simp]: "ubLen (medium_stream_i\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: medium_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_621ccf_medium_stream_i_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma medium_stream_i_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_621ccf_i''} "
    shows "medium_stream_i\<cdot>(medium_get_stream_i\<cdot>ub) = ub"
  apply(simp add: medium_stream_i.rep_eq medium_get_stream_i.rep_eq)
  apply(simp add: DoNotUse_621ccf_medium_stream_i_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma medium_stream_o_dom[simp]: "ubDom\<cdot>(medium_stream_o\<cdot>x) = {\<C> ''DoNotUse_621ccf_o''}"
  by(simp add: medium_stream_o.rep_eq ubdom_insert DoNotUse_621ccf_medium_stream_o_h.rep_eq)

lemma medium_stream_o_len[simp]: "ubLen (medium_stream_o\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: medium_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_621ccf_medium_stream_o_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma medium_stream_o_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_621ccf_o''} "
    shows "medium_stream_o\<cdot>(medium_get_stream_o\<cdot>ub) = ub"
  apply(simp add: medium_stream_o.rep_eq medium_get_stream_o.rep_eq)
  apply(simp add: DoNotUse_621ccf_medium_stream_o_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma mediumin_stream_i_dom[simp]: "ubDom\<cdot>(mediumIn_stream_i\<cdot>port_i) = mediumDom"
  apply(simp add: mediumIn_stream_i_def ubclUnion_ubundle_def)
  by(auto simp add: mediumDom_def)

lemma mediumout_stream_o_dom[simp]: "ubDom\<cdot>(mediumOut_stream_o\<cdot>port_o) = mediumRan"
  apply(simp add: mediumOut_stream_o_def ubclUnion_ubundle_def)
  by(auto simp add: mediumRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma mediumelem_get_i_id[simp]: "mediumElem_get_i (mediumElem_i x) = x"
  apply(cases x)
  apply(auto simp add: mediumElem_i.simps)
  unfolding mediumElem_get_i_def mediumElem_raw_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI mediumMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma mediumelem_get_o_id[simp]: "mediumElem_get_o (mediumElem_o x) = x"
  apply(cases x)
  apply(auto simp add: mediumElem_o.simps)
  unfolding mediumElem_get_o_def mediumElem_raw_o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI mediumMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma mediumelem_get_i_in_i_id[simp]: "mediumElem_get_i (mediumElemIn_i port_i) = port_i"
  apply(simp add: mediumElemIn_i_def mediumElem_get_i_def)
  by(metis mediumElem_get_i_def mediumelem_get_i_id)

lemma mediumelem_get_o_out_o_id[simp]: "mediumElem_get_o (mediumElemOut_o port_o) = port_o"
  apply(simp add: mediumElemOut_o_def mediumElem_get_o_def)
  by(metis mediumElem_get_o_def mediumelem_get_o_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma medium_get_stream_i_id[simp]: "medium_get_stream_i\<cdot>(medium_stream_i\<cdot>x) = x"
  apply(simp add: medium_get_stream_i.rep_eq medium_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_621ccf_medium_stream_i_h.rep_eq)
  by (simp add: inj_def)

lemma medium_get_stream_i_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_621ccf_i''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_621ccf_i''}"
      and "medium_get_stream_i\<cdot>ub1 = medium_get_stream_i\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) medium_stream_i_id by metis

lemma medium_get_stream_i_conc[simp]:
  assumes "\<C> ''DoNotUse_621ccf_i'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_621ccf_i'' \<in> ubDom\<cdot>ub2"
    shows "medium_get_stream_i\<cdot>(ubConc ub1\<cdot>ub2) = (medium_get_stream_i\<cdot>ub1) \<bullet> (medium_get_stream_i\<cdot>ub2)"
  apply(simp add: medium_get_stream_i.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma medium_get_stream_o_id[simp]: "medium_get_stream_o\<cdot>(medium_stream_o\<cdot>x) = x"
  apply(simp add: medium_get_stream_o.rep_eq medium_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_621ccf_medium_stream_o_h.rep_eq)
  by (simp add: inj_def)

lemma medium_get_stream_o_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_621ccf_o''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_621ccf_o''}"
      and "medium_get_stream_o\<cdot>ub1 = medium_get_stream_o\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) medium_stream_o_id by metis

lemma medium_get_stream_o_conc[simp]:
  assumes "\<C> ''DoNotUse_621ccf_o'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_621ccf_o'' \<in> ubDom\<cdot>ub2"
    shows "medium_get_stream_o\<cdot>(ubConc ub1\<cdot>ub2) = (medium_get_stream_o\<cdot>ub1) \<bullet> (medium_get_stream_o\<cdot>ub2)"
  apply(simp add: medium_get_stream_o.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma medium_get_stream_i_in_i_id[simp]: "medium_get_stream_i\<cdot>(mediumIn_stream_i\<cdot>port_i) = port_i"
  apply(auto simp add: medium_get_stream_i.rep_eq mediumIn_stream_i_def ubclUnion_ubundle_def)
  by (metis medium_get_stream_i.rep_eq medium_get_stream_i_id)

lemma medium_get_stream_o_out_o_id[simp]: "medium_get_stream_o\<cdot>(mediumOut_stream_o\<cdot>port_o) = port_o"
  apply(auto simp add: medium_get_stream_o.rep_eq mediumOut_stream_o_def ubclUnion_ubundle_def)
  by (metis medium_get_stream_o.rep_eq medium_get_stream_o_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma medium_get_stream_i_single[simp]: "medium_get_stream_i\<cdot>(medium_i x) = \<up>x"
  apply(simp add: medium_get_stream_i.rep_eq medium_i_def)
  by (metis mediumElem_get_i_def mediumelem_get_i_id)

lemma medium_get_stream_o_single[simp]: "medium_get_stream_o\<cdot>(medium_o x) = \<up>x"
  apply(simp add: medium_get_stream_o.rep_eq medium_o_def)
  by (metis mediumElem_get_o_def mediumelem_get_o_id)


subsubsection \<open>In/Out\<close>

lemma medium_get_stream_i_single_in_i_id[simp]: "medium_get_stream_i\<cdot>(mediumIn_i port_i) = \<up>port_i"
  apply(simp add: medium_get_stream_i_def mediumIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: mediumDom_def mediumElemIn_i_def)
  apply(cases port_i)
  apply(auto simp add: mediumElem_i.simps)
  unfolding mediumElem_get_i_def mediumElem_raw_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma medium_get_stream_o_single_out_o_id[simp]: "medium_get_stream_o\<cdot>(mediumOut_o port_o) = \<up>port_o"
  apply(simp add: medium_get_stream_o_def mediumOut_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: mediumDom_def mediumElemOut_o_def)
  apply(cases port_o)
  apply(auto simp add: mediumElem_o.simps)
  unfolding mediumElem_get_o_def mediumElem_raw_o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma medium_stream_i_conc:
  "medium_stream_i\<cdot>(\<up>elem \<bullet> s) = ubConc (medium_i elem)\<cdot>(medium_stream_i\<cdot>s)"
  apply (rule medium_get_stream_i_eq)
  by simp_all

lemma medium_stream_o_conc:
  "medium_stream_o\<cdot>(\<up>elem \<bullet> s) = ubConc (medium_o elem)\<cdot>(medium_stream_o\<cdot>s)"
  apply (rule medium_get_stream_o_eq)
  by simp_all


end