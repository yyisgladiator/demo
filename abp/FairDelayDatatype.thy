(*
 * DO NOT MODIFY!
 * This file was generated from FairDelay.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory FairDelayDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) fairDelayMessage = DoNotUse_b696c7_FairDelayE "'e"

instance fairDelayMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation fairDelayMessage :: (countable) message
begin
  fun ctype_fairDelayMessage :: "channel \<Rightarrow> ('e::countable) fairDelayMessage set" where
  "ctype_fairDelayMessage c = (
    if c = \<C> ''DoNotUse_b696c7_i'' then range DoNotUse_b696c7_FairDelayE else
    if c = \<C> ''DoNotUse_b696c7_o'' then range DoNotUse_b696c7_FairDelayE else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition fairDelayDom :: "channel set" where
"fairDelayDom = {\<C> ''DoNotUse_b696c7_i''}"

definition fairDelayRan :: "channel set" where
"fairDelayRan = {\<C> ''DoNotUse_b696c7_o''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use fairDelayElemIn_i instead *)
lift_definition fairDelayElem_raw_i :: "'e \<Rightarrow> ('e::countable) fairDelayMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_b696c7_i'' \<mapsto> Msg (DoNotUse_b696c7_FairDelayE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use fairDelayElemOut_o instead *)
lift_definition fairDelayElem_raw_o :: "'e \<Rightarrow> ('e::countable) fairDelayMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_b696c7_o'' \<mapsto> Msg (DoNotUse_b696c7_FairDelayE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use fairDelayElemIn_i instead *)
fun fairDelayElem_i :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn sbElem" where
"fairDelayElem_i (Msg port_i) = fairDelayElem_raw_i port_i" |
"fairDelayElem_i null = sbeNull {\<C> ''DoNotUse_b696c7_i''}"

(* Do not use this, use fairDelayElemOut_o instead *)
fun fairDelayElem_o :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn sbElem" where
"fairDelayElem_o (Msg port_o) = fairDelayElem_raw_o port_o" |
"fairDelayElem_o null = sbeNull {\<C> ''DoNotUse_b696c7_o''}"

declare fairDelayElem_i.simps[simp del]

declare fairDelayElem_o.simps[simp del]

(* Do not use this, use fairDelayIn_i instead *)
definition fairDelay_i :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelay_i port_i = sbe2SB (fairDelayElem_i port_i)"

(* Do not use this, use fairDelayOut_o instead *)
definition fairDelay_o :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelay_o port_o = sbe2SB (fairDelayElem_o port_o)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition fairDelayElemIn_i :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn sbElem" where
"fairDelayElemIn_i port_i = (fairDelayElem_i port_i)"

(* Create one sbElem for all output channels *)
definition fairDelayElemOut_o :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn sbElem" where
"fairDelayElemOut_o port_o = (fairDelayElem_o port_o)"

(* Create one SB for all input channels *)
definition fairDelayIn_i :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelayIn_i port_i = (sbe2SB (fairDelayElemIn_i port_i))"

(* Create one SB for all output channels *)
definition fairDelayOut_o :: "'e tsyn \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelayOut_o port_o = (sbe2SB (fairDelayElemOut_o port_o))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use fairDelayIn_list_i instead *)
fun fairDelay_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelay_list_i (x#xs) = ubConcEq (fairDelay_i x)\<cdot>(fairDelay_list_i xs)" |
"fairDelay_list_i []     = ubLeast {\<C> ''DoNotUse_b696c7_i''}"

declare fairDelay_list_i.simps[simp del]

(* Do not use this, use fairDelayOut_list_o instead *)
fun fairDelay_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelay_list_o (x#xs) = ubConcEq (fairDelay_o x)\<cdot>(fairDelay_list_o xs)" |
"fairDelay_list_o []     = ubLeast {\<C> ''DoNotUse_b696c7_o''}"

declare fairDelay_list_o.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun fairDelayIn_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelayIn_list_i ((port_i)#xs) = ubConcEq (fairDelayIn_i port_i)\<cdot>(fairDelayIn_list_i xs)" |
"fairDelayIn_list_i [] = ubLeast fairDelayDom"

(* Create one SB for all output channels *)
fun fairDelayOut_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelayOut_list_o ((port_o)#xs) = ubConcEq (fairDelayOut_o port_o)\<cdot>(fairDelayOut_list_o xs)" |
"fairDelayOut_list_o [] = ubLeast fairDelayRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_b696c7_fairDelay_stream_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_b696c7_i'') \<mapsto> (tsynMap (DoNotUse_b696c7_FairDelayE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use fairDelayIn_stream_i instead *)
lift_definition fairDelay_stream_i :: "('e) tsyn stream \<rightarrow> ('e::countable) fairDelayMessage tsyn SB" is
"DoNotUse_b696c7_fairDelay_stream_i_h"
  apply(auto simp add: cfun_def DoNotUse_b696c7_fairDelay_stream_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_b696c7_fairDelay_stream_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_b696c7_fairDelay_stream_o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) fairDelayMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_b696c7_o'') \<mapsto> (tsynMap (DoNotUse_b696c7_FairDelayE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use fairDelayOut_stream_o instead *)
lift_definition fairDelay_stream_o :: "('e) tsyn stream \<rightarrow> ('e::countable) fairDelayMessage tsyn SB" is
"DoNotUse_b696c7_fairDelay_stream_o_h"
  apply(auto simp add: cfun_def DoNotUse_b696c7_fairDelay_stream_o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_b696c7_fairDelay_stream_o_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition fairDelayIn_stream_i :: "'e tsyn stream \<rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelayIn_stream_i = (\<Lambda>  port_i. (fairDelay_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition fairDelayOut_stream_o :: "'e tsyn stream \<rightarrow> ('e::countable) fairDelayMessage tsyn SB" where
"fairDelayOut_stream_o = (\<Lambda>  port_o. (fairDelay_stream_o\<cdot>port_o))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition fairDelayElem_get_i :: "('e::countable) fairDelayMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"fairDelayElem_get_i sbe = tsynApplyElem (inv DoNotUse_b696c7_FairDelayE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_b696c7_i''))"

definition fairDelayElem_get_o :: "('e::countable) fairDelayMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"fairDelayElem_get_o sbe = tsynApplyElem (inv DoNotUse_b696c7_FairDelayE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_b696c7_o''))"


subsection \<open>SB to stream\<close>

lift_definition fairDelay_get_stream_i :: "('e::countable) fairDelayMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_b696c7_FairDelayE)\<cdot>(sb . (\<C> ''DoNotUse_b696c7_i''))"
  by(simp add: cfun_def)

lift_definition fairDelay_get_stream_o :: "('e::countable) fairDelayMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_b696c7_FairDelayE)\<cdot>(sb . (\<C> ''DoNotUse_b696c7_o''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma fairdelayelem_i_dom[simp]: "sbeDom (fairDelayElem_i x) = {\<C> ''DoNotUse_b696c7_i''}"
  apply(cases x)
  apply(simp add: fairDelayElem_i.simps sbeDom_def fairDelayElem_raw_i.rep_eq)
  by(simp add: fairDelayElem_i.simps)

lemma fairdelayelem_o_dom[simp]: "sbeDom (fairDelayElem_o x) = {\<C> ''DoNotUse_b696c7_o''}"
  apply(cases x)
  apply(simp add: fairDelayElem_o.simps sbeDom_def fairDelayElem_raw_o.rep_eq)
  by(simp add: fairDelayElem_o.simps)

lemma fairdelay_i_dom[simp]: "ubDom\<cdot>(fairDelay_i x) = {\<C> ''DoNotUse_b696c7_i''}"
  by(simp add: fairDelay_i_def)

lemma fairdelay_i_len[simp]: "ubLen (fairDelay_i x) = 1"
  by(simp add: fairDelay_i_def)

lemma fairdelay_o_dom[simp]: "ubDom\<cdot>(fairDelay_o x) = {\<C> ''DoNotUse_b696c7_o''}"
  by(simp add: fairDelay_o_def)

lemma fairdelay_o_len[simp]: "ubLen (fairDelay_o x) = 1"
  by(simp add: fairDelay_o_def)


subsubsection \<open>In/Out\<close>

lemma fairdelayelemin_i_dom[simp]: "sbeDom (fairDelayElemIn_i port_i) = fairDelayDom"
  by(auto simp add: fairDelayElemIn_i_def fairDelayDom_def)

lemma fairdelayelemout_o_dom[simp]: "sbeDom (fairDelayElemOut_o port_o) = fairDelayRan"
  by(auto simp add: fairDelayElemOut_o_def fairDelayRan_def)

lemma fairdelayin_i_dom[simp]: "ubDom\<cdot>(fairDelayIn_i port_i) = fairDelayDom"
  by(simp add: fairDelayIn_i_def)

lemma fairdelayin_i_len[simp]: "ubLen (fairDelayIn_i port_i) = 1"
  by(simp add: fairDelayIn_i_def fairDelayDom_def)

lemma fairdelayout_o_dom[simp]: "ubDom\<cdot>(fairDelayOut_o port_o) = fairDelayRan"
  by(simp add: fairDelayOut_o_def)

lemma fairdelayout_o_len[simp]: "ubLen (fairDelayOut_o port_o) = 1"
  by(simp add: fairDelayOut_o_def fairDelayRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma fairdelay_stream_i_dom[simp]: "ubDom\<cdot>(fairDelay_stream_i\<cdot>x) = {\<C> ''DoNotUse_b696c7_i''}"
  by(simp add: fairDelay_stream_i.rep_eq ubdom_insert DoNotUse_b696c7_fairDelay_stream_i_h.rep_eq)

lemma fairdelay_stream_i_len[simp]: "ubLen (fairDelay_stream_i\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: fairDelay_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_b696c7_fairDelay_stream_i_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma fairdelay_stream_i_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_b696c7_i''} "
    shows "fairDelay_stream_i\<cdot>(fairDelay_get_stream_i\<cdot>ub) = ub"
  apply(simp add: fairDelay_stream_i.rep_eq fairDelay_get_stream_i.rep_eq)
  apply(simp add: DoNotUse_b696c7_fairDelay_stream_i_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma fairdelay_stream_o_dom[simp]: "ubDom\<cdot>(fairDelay_stream_o\<cdot>x) = {\<C> ''DoNotUse_b696c7_o''}"
  by(simp add: fairDelay_stream_o.rep_eq ubdom_insert DoNotUse_b696c7_fairDelay_stream_o_h.rep_eq)

lemma fairdelay_stream_o_len[simp]: "ubLen (fairDelay_stream_o\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: fairDelay_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_b696c7_fairDelay_stream_o_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma fairdelay_stream_o_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_b696c7_o''} "
    shows "fairDelay_stream_o\<cdot>(fairDelay_get_stream_o\<cdot>ub) = ub"
  apply(simp add: fairDelay_stream_o.rep_eq fairDelay_get_stream_o.rep_eq)
  apply(simp add: DoNotUse_b696c7_fairDelay_stream_o_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma fairdelayin_stream_i_dom[simp]: "ubDom\<cdot>(fairDelayIn_stream_i\<cdot>port_i) = fairDelayDom"
  apply(simp add: fairDelayIn_stream_i_def ubclUnion_ubundle_def)
  by(auto simp add: fairDelayDom_def)

lemma fairdelayout_stream_o_dom[simp]: "ubDom\<cdot>(fairDelayOut_stream_o\<cdot>port_o) = fairDelayRan"
  apply(simp add: fairDelayOut_stream_o_def ubclUnion_ubundle_def)
  by(auto simp add: fairDelayRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma fairdelayelem_get_i_id[simp]: "fairDelayElem_get_i (fairDelayElem_i x) = x"
  apply(cases x)
  apply(auto simp add: fairDelayElem_i.simps)
  unfolding fairDelayElem_get_i_def fairDelayElem_raw_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI fairDelayMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma fairdelayelem_get_o_id[simp]: "fairDelayElem_get_o (fairDelayElem_o x) = x"
  apply(cases x)
  apply(auto simp add: fairDelayElem_o.simps)
  unfolding fairDelayElem_get_o_def fairDelayElem_raw_o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI fairDelayMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma fairdelayelem_get_i_in_i_id[simp]: "fairDelayElem_get_i (fairDelayElemIn_i port_i) = port_i"
  apply(simp add: fairDelayElemIn_i_def fairDelayElem_get_i_def)
  by(metis fairDelayElem_get_i_def fairdelayelem_get_i_id)

lemma fairdelayelem_get_o_out_o_id[simp]: "fairDelayElem_get_o (fairDelayElemOut_o port_o) = port_o"
  apply(simp add: fairDelayElemOut_o_def fairDelayElem_get_o_def)
  by(metis fairDelayElem_get_o_def fairdelayelem_get_o_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma fairdelay_get_stream_i_id[simp]: "fairDelay_get_stream_i\<cdot>(fairDelay_stream_i\<cdot>x) = x"
  apply(simp add: fairDelay_get_stream_i.rep_eq fairDelay_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_b696c7_fairDelay_stream_i_h.rep_eq)
  by (simp add: inj_def)

lemma fairdelay_get_stream_i_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_b696c7_i''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_b696c7_i''}"
      and "fairDelay_get_stream_i\<cdot>ub1 = fairDelay_get_stream_i\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) fairdelay_stream_i_id by metis

lemma fairdelay_get_stream_i_conc[simp]:
  assumes "\<C> ''DoNotUse_b696c7_i'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_b696c7_i'' \<in> ubDom\<cdot>ub2"
    shows "fairDelay_get_stream_i\<cdot>(ubConc ub1\<cdot>ub2) = (fairDelay_get_stream_i\<cdot>ub1) \<bullet> (fairDelay_get_stream_i\<cdot>ub2)"
  apply(simp add: fairDelay_get_stream_i.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma fairdelay_get_stream_o_id[simp]: "fairDelay_get_stream_o\<cdot>(fairDelay_stream_o\<cdot>x) = x"
  apply(simp add: fairDelay_get_stream_o.rep_eq fairDelay_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_b696c7_fairDelay_stream_o_h.rep_eq)
  by (simp add: inj_def)

lemma fairdelay_get_stream_o_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_b696c7_o''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_b696c7_o''}"
      and "fairDelay_get_stream_o\<cdot>ub1 = fairDelay_get_stream_o\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) fairdelay_stream_o_id by metis

lemma fairdelay_get_stream_o_conc[simp]:
  assumes "\<C> ''DoNotUse_b696c7_o'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_b696c7_o'' \<in> ubDom\<cdot>ub2"
    shows "fairDelay_get_stream_o\<cdot>(ubConc ub1\<cdot>ub2) = (fairDelay_get_stream_o\<cdot>ub1) \<bullet> (fairDelay_get_stream_o\<cdot>ub2)"
  apply(simp add: fairDelay_get_stream_o.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma fairdelay_get_stream_i_in_i_id[simp]: "fairDelay_get_stream_i\<cdot>(fairDelayIn_stream_i\<cdot>port_i) = port_i"
  apply(auto simp add: fairDelay_get_stream_i.rep_eq fairDelayIn_stream_i_def ubclUnion_ubundle_def)
  by (metis fairDelay_get_stream_i.rep_eq fairdelay_get_stream_i_id)

lemma fairdelay_get_stream_o_out_o_id[simp]: "fairDelay_get_stream_o\<cdot>(fairDelayOut_stream_o\<cdot>port_o) = port_o"
  apply(auto simp add: fairDelay_get_stream_o.rep_eq fairDelayOut_stream_o_def ubclUnion_ubundle_def)
  by (metis fairDelay_get_stream_o.rep_eq fairdelay_get_stream_o_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma fairdelay_get_stream_i_single[simp]: "fairDelay_get_stream_i\<cdot>(fairDelay_i x) = \<up>x"
  apply(simp add: fairDelay_get_stream_i.rep_eq fairDelay_i_def)
  by (metis fairDelayElem_get_i_def fairdelayelem_get_i_id)

lemma fairdelay_get_stream_o_single[simp]: "fairDelay_get_stream_o\<cdot>(fairDelay_o x) = \<up>x"
  apply(simp add: fairDelay_get_stream_o.rep_eq fairDelay_o_def)
  by (metis fairDelayElem_get_o_def fairdelayelem_get_o_id)


subsubsection \<open>In/Out\<close>

lemma fairdelay_get_stream_i_single_in_i_id[simp]: "fairDelay_get_stream_i\<cdot>(fairDelayIn_i port_i) = \<up>port_i"
  apply(simp add: fairDelay_get_stream_i_def fairDelayIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: fairDelayDom_def fairDelayElemIn_i_def)
  apply(cases port_i)
  apply(auto simp add: fairDelayElem_i.simps)
  unfolding fairDelayElem_get_i_def fairDelayElem_raw_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma fairdelay_get_stream_o_single_out_o_id[simp]: "fairDelay_get_stream_o\<cdot>(fairDelayOut_o port_o) = \<up>port_o"
  apply(simp add: fairDelay_get_stream_o_def fairDelayOut_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: fairDelayDom_def fairDelayElemOut_o_def)
  apply(cases port_o)
  apply(auto simp add: fairDelayElem_o.simps)
  unfolding fairDelayElem_get_o_def fairDelayElem_raw_o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma fairdelay_stream_i_conc:
  "fairDelay_stream_i\<cdot>(\<up>elem \<bullet> s) = ubConc (fairDelay_i elem)\<cdot>(fairDelay_stream_i\<cdot>s)"
  apply (rule fairdelay_get_stream_i_eq)
  by simp_all

lemma fairdelay_stream_o_conc:
  "fairDelay_stream_o\<cdot>(\<up>elem \<bullet> s) = ubConc (fairDelay_o elem)\<cdot>(fairDelay_stream_o\<cdot>s)"
  apply (rule fairdelay_get_stream_o_eq)
  by simp_all


end