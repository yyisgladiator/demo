(*
 * DO NOT MODIFY!
 * This file was generated from Password.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 18, 2018 7:47:14 PM by isartransformer 3.1.0
 *)
theory PasswordDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype passwordMessage = DoNotUse_8c5e53_PasswordString "string"

instance passwordMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation passwordMessage :: message
begin
  fun ctype_passwordMessage :: "channel \<Rightarrow> passwordMessage set" where
  "ctype_passwordMessage c = (
    if c = \<C> ''DoNotUse_8c5e53_i'' then range DoNotUse_8c5e53_PasswordString else
    if c = \<C> ''DoNotUse_8c5e53_o'' then range DoNotUse_8c5e53_PasswordString else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition passwordDom :: "channel set" where
"passwordDom = {\<C> ''DoNotUse_8c5e53_i''}"

definition passwordRan :: "channel set" where
"passwordRan = {\<C> ''DoNotUse_8c5e53_o''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use passwordElemIn_i instead *)
lift_definition passwordElem_raw_i :: "string \<Rightarrow> passwordMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_8c5e53_i'' \<mapsto> Msg (DoNotUse_8c5e53_PasswordString x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use passwordElemOut_o instead *)
lift_definition passwordElem_raw_o :: "string \<Rightarrow> passwordMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_8c5e53_o'' \<mapsto> Msg (DoNotUse_8c5e53_PasswordString x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use passwordElemIn_i instead *)
fun passwordElem_i :: "string tsyn \<Rightarrow> passwordMessage tsyn sbElem" where
"passwordElem_i (Msg port_i) = passwordElem_raw_i port_i" |
"passwordElem_i null = sbeNull {\<C> ''DoNotUse_8c5e53_i''}"

(* Do not use this, use passwordElemOut_o instead *)
fun passwordElem_o :: "string tsyn \<Rightarrow> passwordMessage tsyn sbElem" where
"passwordElem_o (Msg port_o) = passwordElem_raw_o port_o" |
"passwordElem_o null = sbeNull {\<C> ''DoNotUse_8c5e53_o''}"

declare passwordElem_i.simps[simp del]

declare passwordElem_o.simps[simp del]

(* Do not use this, use passwordIn_i instead *)
definition password_i :: "string tsyn \<Rightarrow> passwordMessage tsyn SB" where
"password_i port_i = sbe2SB (passwordElem_i port_i)"

(* Do not use this, use passwordOut_o instead *)
definition password_o :: "string tsyn \<Rightarrow> passwordMessage tsyn SB" where
"password_o port_o = sbe2SB (passwordElem_o port_o)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition passwordElemIn_i :: "string tsyn \<Rightarrow> passwordMessage tsyn sbElem" where
"passwordElemIn_i port_i = (passwordElem_i port_i)"

(* Create one sbElem for all output channels *)
definition passwordElemOut_o :: "string tsyn \<Rightarrow> passwordMessage tsyn sbElem" where
"passwordElemOut_o port_o = (passwordElem_o port_o)"

(* Create one SB for all input channels *)
definition passwordIn_i :: "string tsyn \<Rightarrow> passwordMessage tsyn SB" where
"passwordIn_i port_i = (sbe2SB (passwordElemIn_i port_i))"

(* Create one SB for all output channels *)
definition passwordOut_o :: "string tsyn \<Rightarrow> passwordMessage tsyn SB" where
"passwordOut_o port_o = (sbe2SB (passwordElemOut_o port_o))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use passwordIn_list_i instead *)
fun password_list_i :: "(string tsyn) list \<Rightarrow> passwordMessage tsyn SB" where
"password_list_i (x#xs) = ubConcEq (password_i x)\<cdot>(password_list_i xs)" |
"password_list_i []     = ubLeast {\<C> ''DoNotUse_8c5e53_i''}"

declare password_list_i.simps[simp del]

(* Do not use this, use passwordOut_list_o instead *)
fun password_list_o :: "(string tsyn) list \<Rightarrow> passwordMessage tsyn SB" where
"password_list_o (x#xs) = ubConcEq (password_o x)\<cdot>(password_list_o xs)" |
"password_list_o []     = ubLeast {\<C> ''DoNotUse_8c5e53_o''}"

declare password_list_o.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun passwordIn_list_i :: "(string tsyn) list \<Rightarrow> passwordMessage tsyn SB" where
"passwordIn_list_i ((port_i)#xs) = ubConcEq (passwordIn_i port_i)\<cdot>(passwordIn_list_i xs)" |
"passwordIn_list_i [] = ubLeast passwordDom"

(* Create one SB for all output channels *)
fun passwordOut_list_o :: "(string tsyn) list \<Rightarrow> passwordMessage tsyn SB" where
"passwordOut_list_o ((port_o)#xs) = ubConcEq (passwordOut_o port_o)\<cdot>(passwordOut_list_o xs)" |
"passwordOut_list_o [] = ubLeast passwordRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_8c5e53_password_stream_i_h :: "string tsyn stream \<Rightarrow> passwordMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_8c5e53_i'') \<mapsto> (tsynMap (DoNotUse_8c5e53_PasswordString)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use passwordIn_stream_i instead *)
lift_definition password_stream_i :: "(string) tsyn stream \<rightarrow> passwordMessage tsyn SB" is
"DoNotUse_8c5e53_password_stream_i_h"
  apply(auto simp add: cfun_def DoNotUse_8c5e53_password_stream_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_8c5e53_password_stream_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_8c5e53_password_stream_o_h :: "string tsyn stream \<Rightarrow> passwordMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_8c5e53_o'') \<mapsto> (tsynMap (DoNotUse_8c5e53_PasswordString)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use passwordOut_stream_o instead *)
lift_definition password_stream_o :: "(string) tsyn stream \<rightarrow> passwordMessage tsyn SB" is
"DoNotUse_8c5e53_password_stream_o_h"
  apply(auto simp add: cfun_def DoNotUse_8c5e53_password_stream_o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_8c5e53_password_stream_o_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition passwordIn_stream_i :: "string tsyn stream \<rightarrow> passwordMessage tsyn SB" where
"passwordIn_stream_i = (\<Lambda>  port_i. (password_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition passwordOut_stream_o :: "string tsyn stream \<rightarrow> passwordMessage tsyn SB" where
"passwordOut_stream_o = (\<Lambda>  port_o. (password_stream_o\<cdot>port_o))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition passwordElem_get_i :: "passwordMessage tsyn sbElem \<Rightarrow> (string) tsyn" where
"passwordElem_get_i sbe = tsynApplyElem (inv DoNotUse_8c5e53_PasswordString) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_8c5e53_i''))"

definition passwordElem_get_o :: "passwordMessage tsyn sbElem \<Rightarrow> (string) tsyn" where
"passwordElem_get_o sbe = tsynApplyElem (inv DoNotUse_8c5e53_PasswordString) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_8c5e53_o''))"


subsection \<open>SB to stream\<close>

lift_definition password_get_stream_i :: "passwordMessage tsyn SB \<rightarrow> string tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_8c5e53_PasswordString)\<cdot>(sb . (\<C> ''DoNotUse_8c5e53_i''))"
  by(simp add: cfun_def)

lift_definition password_get_stream_o :: "passwordMessage tsyn SB \<rightarrow> string tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_8c5e53_PasswordString)\<cdot>(sb . (\<C> ''DoNotUse_8c5e53_o''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma passwordelem_i_dom[simp]: "sbeDom (passwordElem_i x) = {\<C> ''DoNotUse_8c5e53_i''}"
  apply(cases x)
  apply(simp add: passwordElem_i.simps sbeDom_def passwordElem_raw_i.rep_eq)
  by(simp add: passwordElem_i.simps)

lemma passwordelem_o_dom[simp]: "sbeDom (passwordElem_o x) = {\<C> ''DoNotUse_8c5e53_o''}"
  apply(cases x)
  apply(simp add: passwordElem_o.simps sbeDom_def passwordElem_raw_o.rep_eq)
  by(simp add: passwordElem_o.simps)

lemma password_i_dom[simp]: "ubDom\<cdot>(password_i x) = {\<C> ''DoNotUse_8c5e53_i''}"
  by(simp add: password_i_def)

lemma password_i_len[simp]: "ubLen (password_i x) = 1"
  by(simp add: password_i_def)

lemma password_o_dom[simp]: "ubDom\<cdot>(password_o x) = {\<C> ''DoNotUse_8c5e53_o''}"
  by(simp add: password_o_def)

lemma password_o_len[simp]: "ubLen (password_o x) = 1"
  by(simp add: password_o_def)


subsubsection \<open>In/Out\<close>

lemma passwordelemin_i_dom[simp]: "sbeDom (passwordElemIn_i port_i) = passwordDom"
  by(auto simp add: passwordElemIn_i_def passwordDom_def)

lemma passwordelemout_o_dom[simp]: "sbeDom (passwordElemOut_o port_o) = passwordRan"
  by(auto simp add: passwordElemOut_o_def passwordRan_def)

lemma passwordin_i_dom[simp]: "ubDom\<cdot>(passwordIn_i port_i) = passwordDom"
  by(simp add: passwordIn_i_def)

lemma passwordin_i_len[simp]: "ubLen (passwordIn_i port_i) = 1"
  by(simp add: passwordIn_i_def passwordDom_def)

lemma passwordout_o_dom[simp]: "ubDom\<cdot>(passwordOut_o port_o) = passwordRan"
  by(simp add: passwordOut_o_def)

lemma passwordout_o_len[simp]: "ubLen (passwordOut_o port_o) = 1"
  by(simp add: passwordOut_o_def passwordRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma password_stream_i_dom[simp]: "ubDom\<cdot>(password_stream_i\<cdot>x) = {\<C> ''DoNotUse_8c5e53_i''}"
  by(simp add: password_stream_i.rep_eq ubdom_insert DoNotUse_8c5e53_password_stream_i_h.rep_eq)

lemma password_stream_i_len[simp]: "ubLen (password_stream_i\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: password_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8c5e53_password_stream_i_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma password_stream_i_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_8c5e53_i''} "
    shows "password_stream_i\<cdot>(password_get_stream_i\<cdot>ub) = ub"
  apply(simp add: password_stream_i.rep_eq password_get_stream_i.rep_eq)
  apply(simp add: DoNotUse_8c5e53_password_stream_i_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma password_stream_o_dom[simp]: "ubDom\<cdot>(password_stream_o\<cdot>x) = {\<C> ''DoNotUse_8c5e53_o''}"
  by(simp add: password_stream_o.rep_eq ubdom_insert DoNotUse_8c5e53_password_stream_o_h.rep_eq)

lemma password_stream_o_len[simp]: "ubLen (password_stream_o\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: password_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8c5e53_password_stream_o_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma password_stream_o_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_8c5e53_o''} "
    shows "password_stream_o\<cdot>(password_get_stream_o\<cdot>ub) = ub"
  apply(simp add: password_stream_o.rep_eq password_get_stream_o.rep_eq)
  apply(simp add: DoNotUse_8c5e53_password_stream_o_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma passwordin_stream_i_dom[simp]: "ubDom\<cdot>(passwordIn_stream_i\<cdot>port_i) = passwordDom"
  apply(simp add: passwordIn_stream_i_def ubclUnion_ubundle_def)
  by(auto simp add: passwordDom_def)

lemma passwordout_stream_o_dom[simp]: "ubDom\<cdot>(passwordOut_stream_o\<cdot>port_o) = passwordRan"
  apply(simp add: passwordOut_stream_o_def ubclUnion_ubundle_def)
  by(auto simp add: passwordRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma passwordelem_get_i_id[simp]: "passwordElem_get_i (passwordElem_i x) = x"
  apply(cases x)
  apply(auto simp add: passwordElem_i.simps)
  unfolding passwordElem_get_i_def passwordElem_raw_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI passwordMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma passwordelem_get_o_id[simp]: "passwordElem_get_o (passwordElem_o x) = x"
  apply(cases x)
  apply(auto simp add: passwordElem_o.simps)
  unfolding passwordElem_get_o_def passwordElem_raw_o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI passwordMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma passwordelem_get_i_in_i_id[simp]: "passwordElem_get_i (passwordElemIn_i port_i) = port_i"
  apply(simp add: passwordElemIn_i_def passwordElem_get_i_def)
  by(metis passwordElem_get_i_def passwordelem_get_i_id)

lemma passwordelem_get_o_out_o_id[simp]: "passwordElem_get_o (passwordElemOut_o port_o) = port_o"
  apply(simp add: passwordElemOut_o_def passwordElem_get_o_def)
  by(metis passwordElem_get_o_def passwordelem_get_o_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma password_get_stream_i_id[simp]: "password_get_stream_i\<cdot>(password_stream_i\<cdot>x) = x"
  apply(simp add: password_get_stream_i.rep_eq password_stream_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8c5e53_password_stream_i_h.rep_eq)
  by (simp add: inj_def)

lemma password_get_stream_i_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_8c5e53_i''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_8c5e53_i''}"
      and "password_get_stream_i\<cdot>ub1 = password_get_stream_i\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) password_stream_i_id by metis

lemma password_get_stream_i_conc[simp]:
  assumes "\<C> ''DoNotUse_8c5e53_i'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_8c5e53_i'' \<in> ubDom\<cdot>ub2"
    shows "password_get_stream_i\<cdot>(ubConc ub1\<cdot>ub2) = (password_get_stream_i\<cdot>ub1) \<bullet> (password_get_stream_i\<cdot>ub2)"
  apply(simp add: password_get_stream_i.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma password_get_stream_o_id[simp]: "password_get_stream_o\<cdot>(password_stream_o\<cdot>x) = x"
  apply(simp add: password_get_stream_o.rep_eq password_stream_o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_8c5e53_password_stream_o_h.rep_eq)
  by (simp add: inj_def)

lemma password_get_stream_o_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_8c5e53_o''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_8c5e53_o''}"
      and "password_get_stream_o\<cdot>ub1 = password_get_stream_o\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) password_stream_o_id by metis

lemma password_get_stream_o_conc[simp]:
  assumes "\<C> ''DoNotUse_8c5e53_o'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_8c5e53_o'' \<in> ubDom\<cdot>ub2"
    shows "password_get_stream_o\<cdot>(ubConc ub1\<cdot>ub2) = (password_get_stream_o\<cdot>ub1) \<bullet> (password_get_stream_o\<cdot>ub2)"
  apply(simp add: password_get_stream_o.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma password_get_stream_i_in_i_id[simp]: "password_get_stream_i\<cdot>(passwordIn_stream_i\<cdot>port_i) = port_i"
  apply(auto simp add: password_get_stream_i.rep_eq passwordIn_stream_i_def ubclUnion_ubundle_def)
  by (metis password_get_stream_i.rep_eq password_get_stream_i_id)

lemma password_get_stream_o_out_o_id[simp]: "password_get_stream_o\<cdot>(passwordOut_stream_o\<cdot>port_o) = port_o"
  apply(auto simp add: password_get_stream_o.rep_eq passwordOut_stream_o_def ubclUnion_ubundle_def)
  by (metis password_get_stream_o.rep_eq password_get_stream_o_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma password_get_stream_i_single[simp]: "password_get_stream_i\<cdot>(password_i x) = \<up>x"
  apply(simp add: password_get_stream_i.rep_eq password_i_def)
  by (metis passwordElem_get_i_def passwordelem_get_i_id)

lemma password_get_stream_o_single[simp]: "password_get_stream_o\<cdot>(password_o x) = \<up>x"
  apply(simp add: password_get_stream_o.rep_eq password_o_def)
  by (metis passwordElem_get_o_def passwordelem_get_o_id)


subsubsection \<open>In/Out\<close>

lemma password_get_stream_i_single_in_i_id[simp]: "password_get_stream_i\<cdot>(passwordIn_i port_i) = \<up>port_i"
  apply(simp add: password_get_stream_i_def passwordIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: passwordDom_def passwordElemIn_i_def)
  apply(cases port_i)
  apply(auto simp add: passwordElem_i.simps)
  unfolding passwordElem_get_i_def passwordElem_raw_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma password_get_stream_o_single_out_o_id[simp]: "password_get_stream_o\<cdot>(passwordOut_o port_o) = \<up>port_o"
  apply(simp add: password_get_stream_o_def passwordOut_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: passwordDom_def passwordElemOut_o_def)
  apply(cases port_o)
  apply(auto simp add: passwordElem_o.simps)
  unfolding passwordElem_get_o_def passwordElem_raw_o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma password_stream_i_conc:
  "password_stream_i\<cdot>(\<up>elem \<bullet> s) = ubConc (password_i elem)\<cdot>(password_stream_i\<cdot>s)"
  apply (rule password_get_stream_i_eq)
  by simp_all

lemma password_stream_o_conc:
  "password_stream_o\<cdot>(\<up>elem \<bullet> s) = ubConc (password_o elem)\<cdot>(password_stream_o\<cdot>s)"
  apply (rule password_get_stream_o_eq)
  by simp_all


end