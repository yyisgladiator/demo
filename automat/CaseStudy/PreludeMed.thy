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

fun medIn ::"'a tsyn \<Rightarrow> 'a medMessage tsyn SB" where
"medIn m = sbe2SB(medInElem m)"

  subsection\<open>Lemma\<close>

lemma medinmsgelem_dom[simp]: "sbeDom (medInMsgElem a) = medInDom"
  by(simp add: sbeDom_def medInMsgElem.rep_eq medInDom_def)

lemma medinelem_dom[simp]: "sbeDom (medInElem a) = medInDom"
  apply(cases a)
  by (auto simp add: medInElem.simps)

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
"medOutElem   -     = sbeNull medOutDom"
declare medOutElem.simps[simp del]

fun medOut ::"'a tsyn \<Rightarrow> 'a medMessage tsyn SB" where
"medOut m = sbe2SB(medOutElem m)"

  subsection\<open>Lemma\<close>

lemma medoutmsgelem_dom[simp]: "sbeDom (medOutMsgElem a) = medOutDom"
  by(simp add: sbeDom_def medOutMsgElem.rep_eq medOutDom_def)

lemma medoutelem_dom[simp]: "sbeDom (medOutElem a) = medOutDom"
  apply(cases a)
  by (auto simp add: medOutElem.simps)

lemma medout_dom[simp]: "ubDom\<cdot>(medOut a) = medOutDom"
  by(cases a, simp_all add: medInDom_def)


end