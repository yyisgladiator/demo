(*
 * DO NOT MODIFY!
 * This file was generated from UnfairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory UnfairMediumDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) unfairMediumMessage = UnfairMediumE "'e"

instance unfairMediumMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation unfairMediumMessage :: (countable) message
begin
  fun ctype_unfairMediumMessage :: "channel \<Rightarrow> ('e::countable) unfairMediumMessage set" where
  "ctype_unfairMediumMessage c = (
    if c = \<C> ''i'' then range UnfairMediumE else
    if c = \<C> ''o'' then range UnfairMediumE else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition unfairMediumDom :: "channel set" where
"unfairMediumDom = {\<C> ''i''}"

definition unfairMediumRan :: "channel set" where
"unfairMediumRan = {\<C> ''o''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use unfairMediumElemIn_i instead *)
lift_definition unfairMediumElem_raw_i :: "'e \<Rightarrow> ('e::countable) unfairMediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''i'' \<mapsto> Msg (UnfairMediumE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use unfairMediumElemOut_o instead *)
lift_definition unfairMediumElem_raw_o :: "'e \<Rightarrow> ('e::countable) unfairMediumMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''o'' \<mapsto> Msg (UnfairMediumE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use unfairMediumElemIn_i instead *)
fun unfairMediumElem_i :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn sbElem" where
"unfairMediumElem_i (Msg port_i) = unfairMediumElem_raw_i port_i" |
"unfairMediumElem_i null = sbeNull {\<C> ''i''}"

(* Do not use this, use unfairMediumElemOut_o instead *)
fun unfairMediumElem_o :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn sbElem" where
"unfairMediumElem_o (Msg port_o) = unfairMediumElem_raw_o port_o" |
"unfairMediumElem_o null = sbeNull {\<C> ''o''}"

declare unfairMediumElem_i.simps[simp del]

declare unfairMediumElem_o.simps[simp del]

(* Do not use this, use unfairMediumIn_i instead *)
definition unfairMedium_i :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMedium_i port_i = sbe2SB (unfairMediumElem_i port_i)"

(* Do not use this, use unfairMediumOut_o instead *)
definition unfairMedium_o :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMedium_o port_o = sbe2SB (unfairMediumElem_o port_o)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition unfairMediumElemIn_i :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn sbElem" where
"unfairMediumElemIn_i port_i = (unfairMediumElem_i port_i)"

(* Create one sbElem for all output channels *)
definition unfairMediumElemOut_o :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn sbElem" where
"unfairMediumElemOut_o port_o = (unfairMediumElem_o port_o)"

(* Create one SB for all input channels *)
definition unfairMediumIn_i :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMediumIn_i port_i = (sbe2SB (unfairMediumElemIn_i port_i))"

(* Create one SB for all output channels *)
definition unfairMediumOut_o :: "'e tsyn \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMediumOut_o port_o = (sbe2SB (unfairMediumElemOut_o port_o))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use unfairMediumIn_list_i instead *)
fun unfairMedium_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMedium_list_i (x#xs) = ubConcEq (unfairMedium_i x)\<cdot>(unfairMedium_list_i xs)" |
"unfairMedium_list_i []     = ubLeast {\<C> ''i''}"

declare unfairMedium_list_i.simps[simp del]

(* Do not use this, use unfairMediumOut_list_o instead *)
fun unfairMedium_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMedium_list_o (x#xs) = ubConcEq (unfairMedium_o x)\<cdot>(unfairMedium_list_o xs)" |
"unfairMedium_list_o []     = ubLeast {\<C> ''o''}"

declare unfairMedium_list_o.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun unfairMediumIn_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMediumIn_list_i ((port_i)#xs) = ubConcEq (unfairMediumIn_i port_i)\<cdot>(unfairMediumIn_list_i xs)" |
"unfairMediumIn_list_i [] = ubLeast unfairMediumDom"

(* Create one SB for all output channels *)
fun unfairMediumOut_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMediumOut_list_o ((port_o)#xs) = ubConcEq (unfairMediumOut_o port_o)\<cdot>(unfairMediumOut_list_o xs)" |
"unfairMediumOut_list_o [] = ubLeast unfairMediumRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition unfairMedium_stream_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''i'') \<mapsto> (tsynMap (UnfairMediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use unfairMediumIn_stream_i instead *)
lift_definition unfairMedium_stream_i :: "('e) tsyn stream \<rightarrow> ('e::countable) unfairMediumMessage tsyn SB" is
"unfairMedium_stream_i_h"
  apply(auto simp add: cfun_def unfairMedium_stream_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis unfairMedium_stream_i_h.rep_eq ubrep_well)

lift_definition unfairMedium_stream_o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SB" is
"\<lambda> s. [(\<C> ''o'') \<mapsto> (tsynMap (UnfairMediumE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use unfairMediumOut_stream_o instead *)
lift_definition unfairMedium_stream_o :: "('e) tsyn stream \<rightarrow> ('e::countable) unfairMediumMessage tsyn SB" is
"unfairMedium_stream_o_h"
  apply(auto simp add: cfun_def unfairMedium_stream_o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis unfairMedium_stream_o_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition unfairMediumIn_stream_i :: "'e tsyn stream \<rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMediumIn_stream_i = (\<Lambda>  port_i. (unfairMedium_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition unfairMediumOut_stream_o :: "'e tsyn stream \<rightarrow> ('e::countable) unfairMediumMessage tsyn SB" where
"unfairMediumOut_stream_o = (\<Lambda>  port_o. (unfairMedium_stream_o\<cdot>port_o))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition unfairMediumElem_get_i :: "('e::countable) unfairMediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"unfairMediumElem_get_i sbe = tsynApplyElem (inv UnfairMediumE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''i''))"

definition unfairMediumElem_get_o :: "('e::countable) unfairMediumMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"unfairMediumElem_get_o sbe = tsynApplyElem (inv UnfairMediumE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''o''))"


subsection \<open>SB to stream\<close>

lift_definition unfairMedium_get_stream_i :: "('e::countable) unfairMediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv UnfairMediumE)\<cdot>(sb . (\<C> ''i''))"
  by(simp add: cfun_def)

lift_definition unfairMedium_get_stream_o :: "('e::countable) unfairMediumMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv UnfairMediumE)\<cdot>(sb . (\<C> ''o''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma unfairmediumelem_i_dom[simp]: "sbeDom (unfairMediumElem_i x) = {\<C> ''i''}"
  apply(cases x)
  apply(simp add: unfairMediumElem_i.simps sbeDom_def unfairMediumElem_raw_i.rep_eq)
  by(simp add: unfairMediumElem_i.simps)

lemma unfairmediumelem_o_dom[simp]: "sbeDom (unfairMediumElem_o x) = {\<C> ''o''}"
  apply(cases x)
  apply(simp add: unfairMediumElem_o.simps sbeDom_def unfairMediumElem_raw_o.rep_eq)
  by(simp add: unfairMediumElem_o.simps)

lemma unfairmedium_i_dom[simp]: "ubDom\<cdot>(unfairMedium_i x) = {\<C> ''i''}"
  by(simp add: unfairMedium_i_def)

lemma unfairmedium_i_len[simp]: "ubLen (unfairMedium_i x) = 1"
  by(simp add: unfairMedium_i_def)

lemma unfairmedium_o_dom[simp]: "ubDom\<cdot>(unfairMedium_o x) = {\<C> ''o''}"
  by(simp add: unfairMedium_o_def)

lemma unfairmedium_o_len[simp]: "ubLen (unfairMedium_o x) = 1"
  by(simp add: unfairMedium_o_def)


subsubsection \<open>In/Out\<close>

lemma unfairmediumelemin_i_dom[simp]: "sbeDom (unfairMediumElemIn_i port_i) = unfairMediumDom"
  by(auto simp add: unfairMediumElemIn_i_def unfairMediumDom_def)

lemma unfairmediumelemout_o_dom[simp]: "sbeDom (unfairMediumElemOut_o port_o) = unfairMediumRan"
  by(auto simp add: unfairMediumElemOut_o_def unfairMediumRan_def)

lemma unfairmediumin_i_dom[simp]: "ubDom\<cdot>(unfairMediumIn_i port_i) = unfairMediumDom"
  by(simp add: unfairMediumIn_i_def)

lemma unfairmediumin_i_len[simp]: "ubLen (unfairMediumIn_i port_i) = 1"
  by(simp add: unfairMediumIn_i_def unfairMediumDom_def)

lemma unfairmediumout_o_dom[simp]: "ubDom\<cdot>(unfairMediumOut_o port_o) = unfairMediumRan"
  by(simp add: unfairMediumOut_o_def)

lemma unfairmediumout_o_len[simp]: "ubLen (unfairMediumOut_o port_o) = 1"
  by(simp add: unfairMediumOut_o_def unfairMediumRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma unfairmedium_stream_i_dom[simp]: "ubDom\<cdot>(unfairMedium_stream_i\<cdot>x) = {\<C> ''i''}"
  by(simp add: unfairMedium_stream_i.rep_eq ubdom_insert unfairMedium_stream_i_h.rep_eq)

lemma unfairmedium_stream_i_len[simp]: "ubLen (unfairMedium_stream_i\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: unfairMedium_stream_i.rep_eq)
  apply(simp add: ubGetCh_def unfairMedium_stream_i_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma unfairmedium_stream_i_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''i''} "
    shows "unfairMedium_stream_i\<cdot>(unfairMedium_get_stream_i\<cdot>ub) = ub"
  apply(simp add: unfairMedium_stream_i.rep_eq unfairMedium_get_stream_i.rep_eq)
  apply(simp add: unfairMedium_stream_i_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma unfairmedium_stream_o_dom[simp]: "ubDom\<cdot>(unfairMedium_stream_o\<cdot>x) = {\<C> ''o''}"
  by(simp add: unfairMedium_stream_o.rep_eq ubdom_insert unfairMedium_stream_o_h.rep_eq)

lemma unfairmedium_stream_o_len[simp]: "ubLen (unfairMedium_stream_o\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: unfairMedium_stream_o.rep_eq)
  apply(simp add: ubGetCh_def unfairMedium_stream_o_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma unfairmedium_stream_o_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''o''} "
    shows "unfairMedium_stream_o\<cdot>(unfairMedium_get_stream_o\<cdot>ub) = ub"
  apply(simp add: unfairMedium_stream_o.rep_eq unfairMedium_get_stream_o.rep_eq)
  apply(simp add: unfairMedium_stream_o_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma unfairmediumin_stream_i_dom[simp]: "ubDom\<cdot>(unfairMediumIn_stream_i\<cdot>port_i) = unfairMediumDom"
  apply(simp add: unfairMediumIn_stream_i_def ubclUnion_ubundle_def)
  by(auto simp add: unfairMediumDom_def)

lemma unfairmediumout_stream_o_dom[simp]: "ubDom\<cdot>(unfairMediumOut_stream_o\<cdot>port_o) = unfairMediumRan"
  apply(simp add: unfairMediumOut_stream_o_def ubclUnion_ubundle_def)
  by(auto simp add: unfairMediumRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma unfairmediumelem_get_i_id[simp]: "unfairMediumElem_get_i (unfairMediumElem_i x) = x"
  apply(cases x)
  apply(auto simp add: unfairMediumElem_i.simps)
  unfolding unfairMediumElem_get_i_def unfairMediumElem_raw_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI unfairMediumMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma unfairmediumelem_get_o_id[simp]: "unfairMediumElem_get_o (unfairMediumElem_o x) = x"
  apply(cases x)
  apply(auto simp add: unfairMediumElem_o.simps)
  unfolding unfairMediumElem_get_o_def unfairMediumElem_raw_o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI unfairMediumMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma unfairmediumelem_get_i_in_i_id[simp]: "unfairMediumElem_get_i (unfairMediumElemIn_i port_i) = port_i"
  apply(simp add: unfairMediumElemIn_i_def unfairMediumElem_get_i_def)
  by(metis unfairMediumElem_get_i_def unfairmediumelem_get_i_id)

lemma unfairmediumelem_get_o_out_o_id[simp]: "unfairMediumElem_get_o (unfairMediumElemOut_o port_o) = port_o"
  apply(simp add: unfairMediumElemOut_o_def unfairMediumElem_get_o_def)
  by(metis unfairMediumElem_get_o_def unfairmediumelem_get_o_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma unfairmedium_get_stream_i_id[simp]: "unfairMedium_get_stream_i\<cdot>(unfairMedium_stream_i\<cdot>x) = x"
  apply(simp add: unfairMedium_get_stream_i.rep_eq unfairMedium_stream_i.rep_eq)
  apply(simp add: ubGetCh_def unfairMedium_stream_i_h.rep_eq)
  by (simp add: inj_def)

lemma unfairmedium_get_stream_i_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''i''}"
      and "ubDom\<cdot>ub2 = {\<C> ''i''}"
      and "unfairMedium_get_stream_i\<cdot>ub1 = unfairMedium_get_stream_i\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) unfairmedium_stream_i_id by metis

lemma unfairmedium_get_stream_i_conc[simp]:
  assumes "\<C> ''i'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''i'' \<in> ubDom\<cdot>ub2"
    shows "unfairMedium_get_stream_i\<cdot>(ubConc ub1\<cdot>ub2) = (unfairMedium_get_stream_i\<cdot>ub1) \<bullet> (unfairMedium_get_stream_i\<cdot>ub2)"
  apply(simp add: unfairMedium_get_stream_i.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma unfairmedium_get_stream_o_id[simp]: "unfairMedium_get_stream_o\<cdot>(unfairMedium_stream_o\<cdot>x) = x"
  apply(simp add: unfairMedium_get_stream_o.rep_eq unfairMedium_stream_o.rep_eq)
  apply(simp add: ubGetCh_def unfairMedium_stream_o_h.rep_eq)
  by (simp add: inj_def)

lemma unfairmedium_get_stream_o_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''o''}"
      and "ubDom\<cdot>ub2 = {\<C> ''o''}"
      and "unfairMedium_get_stream_o\<cdot>ub1 = unfairMedium_get_stream_o\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) unfairmedium_stream_o_id by metis

lemma unfairmedium_get_stream_o_conc[simp]:
  assumes "\<C> ''o'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''o'' \<in> ubDom\<cdot>ub2"
    shows "unfairMedium_get_stream_o\<cdot>(ubConc ub1\<cdot>ub2) = (unfairMedium_get_stream_o\<cdot>ub1) \<bullet> (unfairMedium_get_stream_o\<cdot>ub2)"
  apply(simp add: unfairMedium_get_stream_o.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma unfairmedium_get_stream_i_in_i_id[simp]: "unfairMedium_get_stream_i\<cdot>(unfairMediumIn_stream_i\<cdot>port_i) = port_i"
  apply(auto simp add: unfairMedium_get_stream_i.rep_eq unfairMediumIn_stream_i_def ubclUnion_ubundle_def)
  by (metis unfairMedium_get_stream_i.rep_eq unfairmedium_get_stream_i_id)

lemma unfairmedium_get_stream_o_out_o_id[simp]: "unfairMedium_get_stream_o\<cdot>(unfairMediumOut_stream_o\<cdot>port_o) = port_o"
  apply(auto simp add: unfairMedium_get_stream_o.rep_eq unfairMediumOut_stream_o_def ubclUnion_ubundle_def)
  by (metis unfairMedium_get_stream_o.rep_eq unfairmedium_get_stream_o_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma unfairmedium_get_stream_i_single[simp]: "unfairMedium_get_stream_i\<cdot>(unfairMedium_i x) = \<up>x"
  apply(simp add: unfairMedium_get_stream_i.rep_eq unfairMedium_i_def)
  by (metis unfairMediumElem_get_i_def unfairmediumelem_get_i_id)

lemma unfairmedium_get_stream_o_single[simp]: "unfairMedium_get_stream_o\<cdot>(unfairMedium_o x) = \<up>x"
  apply(simp add: unfairMedium_get_stream_o.rep_eq unfairMedium_o_def)
  by (metis unfairMediumElem_get_o_def unfairmediumelem_get_o_id)


subsubsection \<open>In/Out\<close>

lemma unfairmedium_get_stream_i_single_in_i_id[simp]: "unfairMedium_get_stream_i\<cdot>(unfairMediumIn_i port_i) = \<up>port_i"
  apply(simp add: unfairMedium_get_stream_i_def unfairMediumIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: unfairMediumDom_def unfairMediumElemIn_i_def)
  apply(cases port_i)
  apply(auto simp add: unfairMediumElem_i.simps)
  unfolding unfairMediumElem_get_i_def unfairMediumElem_raw_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma unfairmedium_get_stream_o_single_out_o_id[simp]: "unfairMedium_get_stream_o\<cdot>(unfairMediumOut_o port_o) = \<up>port_o"
  apply(simp add: unfairMedium_get_stream_o_def unfairMediumOut_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: unfairMediumDom_def unfairMediumElemOut_o_def)
  apply(cases port_o)
  apply(auto simp add: unfairMediumElem_o.simps)
  unfolding unfairMediumElem_get_o_def unfairMediumElem_raw_o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma unfairmedium_stream_i_conc:
  "unfairMedium_stream_i\<cdot>(\<up>elem \<bullet> s) = ubConc (unfairMedium_i elem)\<cdot>(unfairMedium_stream_i\<cdot>s)"
  apply (rule unfairmedium_get_stream_i_eq)
  by simp_all

lemma unfairmedium_stream_o_conc:
  "unfairMedium_stream_o\<cdot>(\<up>elem \<bullet> s) = ubConc (unfairMedium_o elem)\<cdot>(unfairMedium_stream_o\<cdot>s)"
  apply (rule unfairmedium_get_stream_o_eq)
  by simp_all


end