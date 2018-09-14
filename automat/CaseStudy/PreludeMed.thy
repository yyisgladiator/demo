theory PreludeMed

imports HOLCF automat.ndAutomaton bundle.tsynBundle

begin

default_sort countable


section \<open>State Datatype\<close>


(* The state is a counter *)
type_synonym medState = nat





section \<open>Message Datatype\<close>


datatype 'a::countable medMessage = medData 'a 

instance medMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation medMessage :: (countable) message
begin
  fun ctype_medMessage :: "channel  \<Rightarrow> 'a medMessage set" where
  "ctype_medMessage c = (
    if c = \<C> ''in'' then range medData else            
    if c = \<C> ''out'' then range medData else
    {})"

  instance
    by(intro_classes)
end




fun medMessageTransform :: "'a medMessage tsyn \<Rightarrow> 'a tsyn" where
"medMessageTransform          -        =   -  " |
"medMessageTransform (Msg (medData a)) = Msg a"



section \<open>MedIn\<close>

  subsection\<open>Definitions\<close>


definition medInDom :: "channel set" where
"medInDom = { \<C> ''in'' }"


lift_definition medInMsgElem :: "'a \<Rightarrow> 'a medMessage tsyn sbElem" is
"\<lambda>x. [ (\<C> ''in'') \<mapsto> (Msg (medData x))]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

fun medInElem ::"'a tsyn \<Rightarrow> 'a medMessage tsyn sbElem" where
"medInElem (Msg m) = medInMsgElem m" |
"medInElem   -     = sbeNull medInDom"
declare medInElem.simps[simp del]

definition medIn ::"'a tsyn \<Rightarrow> 'a medMessage tsyn SB" where
"medIn m = sbe2SB(medInElem m)"


lift_definition medInGetStream :: "'a medMessage tsyn SB \<rightarrow> 'a tsyn stream" is
"\<lambda>sb. tsynMap (inv medData)\<cdot>(sb . (\<C> ''in''))"
  by(simp add: cfun_def)

lift_definition medInSetStream_h :: "'a tsyn stream \<Rightarrow> 'a medMessage tsyn SB" is 
"\<lambda> s. [(\<C> ''in'') \<mapsto> (tsynMap (medData)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  by (metis imageI medMessageTransform.cases range_eqI)

lift_definition medInSetStream :: "'a tsyn stream \<rightarrow> 'a medMessage tsyn SB" is
"medInSetStream_h"
  apply(auto simp add: cfun_def medInSetStream_h_def map_fun_def comp_def )
  apply(rule cont_Abs_UB)
  defer
   apply (metis medInSetStream_h.rep_eq ubrep_well)
  apply(rule contI2, rule monofunI)
   apply (simp add: monofun_cfun_arg part_below)
  oops (* Das sollte nicht so kopmliziert sein... *)

  subsection\<open>Lemma\<close>

lemma medinmsgelem_dom[simp]: "sbeDom (medInMsgElem a) = medInDom"
  by(simp add: sbeDom_def medInMsgElem.rep_eq medInDom_def)

lemma medinelem_dom[simp]: "sbeDom (medInElem a) = medInDom"
  apply(cases a)
  by (auto simp add: medInElem.simps)

lemma medin_dom[simp]: "ubDom\<cdot>(medIn a) = medInDom"
  by (simp add: medIn_def)







section \<open>MedOut\<close>

  subsection\<open>Definitions\<close>


definition medOutDom :: "channel set" where
"medOutDom = { \<C> ''out'' }"

lift_definition medOutMsgElem :: "'a \<Rightarrow> 'a medMessage tsyn sbElem" is
"\<lambda>x. [ (\<C> ''out'') \<mapsto> (Msg (medData x))]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

fun medOutElem ::"'a tsyn \<Rightarrow> 'a medMessage tsyn sbElem" where
"medOutElem (Msg m) = medOutMsgElem m" |
"medOutElem   -     = sbeNull medOutDom"
declare medOutElem.simps[simp del]

definition medOut ::"'a tsyn \<Rightarrow> 'a medMessage tsyn SB" where
"medOut m = sbe2SB(medOutElem m)"

lift_definition medOutGetStream :: "'a medMessage tsyn SB \<rightarrow> 'a tsyn stream" is
"\<lambda>sb. tsynMap (inv medData)\<cdot>(sb . (\<C> ''out''))"
  by(simp add: cfun_def)

lift_definition medOutSetStream_h :: "'a tsyn stream \<Rightarrow> 'a medMessage tsyn SB" is 
"\<lambda> s. [(\<C> ''out'') \<mapsto> (tsynMap (medData)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  by (metis imageI medMessageTransform.cases range_eqI)

lift_definition medOutSetStream :: "'a tsyn stream \<rightarrow> 'a medMessage tsyn SB" is
"medOutSetStream_h"
  apply(auto simp add: cfun_def medOutSetStream_h_def map_fun_def comp_def )
  apply(rule cont_Abs_UB)
  defer
   apply (metis medOutSetStream_h.rep_eq ubrep_well)
  apply(rule contI2, rule monofunI)
   apply (simp add: monofun_cfun_arg part_below)
  sorry (* Das sollte nicht so kopmliziert sein... *)


  subsection\<open>Lemma\<close>

lemma medoutmsgelem_dom[simp]: "sbeDom (medOutMsgElem a) = medOutDom"
  by(simp add: sbeDom_def medOutMsgElem.rep_eq medOutDom_def)

lemma medoutelem_dom[simp]: "sbeDom (medOutElem a) = medOutDom"
  apply(cases a)
  by (auto simp add: medOutElem.simps)

lemma medout_dom[simp]: "ubDom\<cdot>(medOut a) = medOutDom"
  by (simp add: medOut_def)

  subsection\<open>Additional Lemma\<close>

(* kopiert, nach Merge löschen. *)
lemma tsynmap_tsynmap: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (\<lambda> x. f (g x))\<cdot>s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_null)

lemma tsynmap_id: "tsynMap (\<lambda>x. x)\<cdot>s = s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_null)
(**)

lemma tsynmap_medData: "Abs_cfun (map_fun id Abs_ubundle (\<lambda>s::'a tsyn stream. 
    [\<C> ''out'' \<mapsto> tsynMap medData\<cdot>s]))\<cdot>ts  .  \<C> ''out'' = tsynMap medData\<cdot>ts"
  by (metis (no_types) fun_upd_same medOutSetStream.abs_eq medOutSetStream.rep_eq 
    medOutSetStream_h.rep_eq medOutSetStream_h_def option.sel ubgetch_insert)

lemma medoutgetstream_medoutsetstream: "medOutGetStream\<cdot>(medOutSetStream\<cdot>ts) = ts"
  apply (simp add: medOutGetStream_def medOutSetStream_def medOutSetStream_h_def tsynmap_medData 
    tsynmap_tsynmap)
  proof -
    have "\<forall>a. inv medData (medData (a::'a)) = a"
  by (meson f_inv_into_f medMessage.inject rangeI)
    then show "tsynMap (\<lambda>a. inv medData (medData a))\<cdot>ts = ts"
      using tsynmap_id by auto
  qed

lemma medin_null: "medIn - . \<C> ''in'' = \<up>-"
  by (simp add: medIn_def medInElem.simps(2) medInDom_def sbe2sb_getch sbeNull.rep_eq)

lemma medin_msg: "medIn (Msg m) . \<C> ''in'' = \<up>(Msg(medData m))"
  by (simp add: medIn_def medInDom_def sbe2sb_getch medInElem.simps(1) medInMsgElem.rep_eq)

lemma medout_null: "medOut - . \<C> ''out'' = \<up>-"
  by (simp add: medOut_def medOutElem.simps(2) medOutDom_def sbe2sb_getch sbeNull.rep_eq)

lemma medout_msg: "medOut (Msg m) . \<C> ''out'' = \<up>(Msg(medData m))"
  by (simp add: medOut_def medOutDom_def sbe2sb_getch medOutElem.simps(1) medOutMsgElem.rep_eq)

lemma medingetstream_ubconc_null: assumes "ubDom\<cdot>ub = medInDom"
  shows "medInGetStream\<cdot>(ubConc (medIn -)\<cdot>ub) = \<up>- \<bullet> (medInGetStream\<cdot>ub)"
  apply (simp add: medInGetStream_def)
  apply (subst ubConc_usclConc_eq)
  apply (simp add: medInDom_def assms)+
  apply (simp add: usclConc_stream_def tsynmap_sconc)
  proof -
    have tsynmap_medin_null: "tsynMap (inv medData)\<cdot>(medIn -  .  \<C> ''in'') = \<up>-"
      by (simp add: medin_null tsynmap_singleton_null)
    then show "tsynMap (inv medData)\<cdot>(medIn -  .  \<C> ''in'') \<bullet> tsynMap (inv medData)\<cdot>(ub  .  \<C> ''in'') 
      = \<up>- \<bullet> tsynMap (inv medData)\<cdot>(ub  .  \<C> ''in'')"
    by (simp add: tsynmap_medin_null)
  qed

lemma medingetstream_ubconc_msg: assumes "ubDom\<cdot>ub = medInDom"
  shows "medInGetStream\<cdot>(ubConc (medIn (Msg m))\<cdot>ub) = \<up>(Msg m) \<bullet> (medInGetStream\<cdot>ub)"
  apply (simp add: medInGetStream_def)
  apply (subst ubConc_usclConc_eq)
  apply (simp add: medInDom_def assms)+
  apply (simp add: usclConc_stream_def tsynmap_sconc)
  proof -
    have tsynmap_medin_msg: "tsynMap (inv medData)\<cdot>(medIn (Msg m)  .  \<C> ''in'') = \<up>(Msg m)"
      apply (simp add: medin_msg tsynmap_singleton_msg)
      by (meson f_inv_into_f medMessage.inject rangeI)
    then show "tsynMap (inv medData)\<cdot>(medIn (Msg m)  .  \<C> ''in'') \<bullet> tsynMap (inv medData)\<cdot>(ub  .  \<C> ''in'') 
      = \<up>(Msg m) \<bullet> tsynMap (inv medData)\<cdot>(ub  .  \<C> ''in'')"
    by (simp add: tsynmap_medin_msg)
  qed

end