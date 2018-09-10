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




section\<open>General\<close>
(* Move this somewhere else... *)
lift_definition tsynNullElem :: "channel set \<Rightarrow> 'a::message tsyn sbElem" is
"\<lambda>cs. (\<lambda>c. (c\<in>cs) \<leadsto> -)"
 unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition sbElem2SB::"'a::message sbElem \<Rightarrow> 'a SB" is
"\<lambda> elem. (\<lambda>c. (c\<in>dom (Rep_sbElem elem)) \<leadsto> \<up>(Rep_sbElem elem)\<rightharpoonup>c)"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  apply simp
  using sbElemWellI Rep_sbElem by blast

section \<open>MedIn\<close>

  subsection\<open>Definitions\<close>


definition medInDom :: "channel set" where
"medInDom = { \<C> ''in'' }"

lift_definition medInMsg :: "'a \<Rightarrow> 'a medMessage tsyn SB" is
"\<lambda>x. [ \<C> ''in'' \<mapsto> \<up>(Msg (medData x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

fun medIn ::"'a tsyn \<Rightarrow> 'a medMessage tsyn SB" where
"medIn (Msg m) = medInMsg m" |
"medIn   -     = tsynbNull  (\<C> ''in'')"


  subsection\<open>Lemma\<close>

lemma medinmsg_dom[simp]: "ubDom\<cdot>(medInMsg a) = medInDom"
  by(simp add: ubdom_insert medInMsg.rep_eq medInDom_def)

lemma medin_dom[simp]: "ubDom\<cdot>(medIn a) = medInDom"
  by(cases a, simp_all add: medInDom_def)







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
"medOutElem   -     = tsynNullElem medOutDom"



lift_definition medOutMsg :: "'a \<Rightarrow> 'a medMessage tsyn SB" is
"\<lambda>x. [ \<C> ''out'' \<mapsto> \<up>(Msg (medData x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

fun medOut ::"'a tsyn \<Rightarrow> 'a medMessage tsyn SB" where
"medOut (Msg m) = medOutMsg m" |
"medOut   -     = tsynbNull  (\<C> ''out'')"



  subsection\<open>Lemma\<close>

lemma medoutmsg_dom[simp]: "ubDom\<cdot>(medOutMsg a) = medOutDom"
  by(simp add: ubdom_insert medOutMsg.rep_eq medOutDom_def)

lemma medout_dom[simp]: "ubDom\<cdot>(medOut a) = medOutDom"
  by(cases a, simp_all add: medOutDom_def)


end
