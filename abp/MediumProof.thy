theory MediumProof

imports MediumAutomaton
          spec.SPS spec.USpec_UFunComp

begin

default_sort countable



section \<open>Med \<otimes> Med = Med\<close>



lift_definition medOut2In :: "('e) mediumMessage tsyn SB \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda>sb. mediumIn_stream_ar \<cdot> (medium_get_stream_as\<cdot>sb)"
  by (simp add: cfun_def)

(* Channel-Converter, from "as" to "ar" *)
definition medOut2InSPF :: "('e::countable) mediumMessage tsyn SB \<Rrightarrow> 'e mediumMessage tsyn SB" where
"medOut2InSPF = ufLift mediumRan medOut2In"


(* Med x Med = Med *)
(* Da die componenten stark-Causal sind hat die rechte Seite noch einen tick in der initalen Ausgabe *)
lemma "mediumSPS \<circle> (uspecConst medOut2InSPF) \<circle> mediumSPS = spsConcOut (mediumOut_as null) mediumSPS"
  apply(rule uspec_eqI)
  oops




  section \<open>Med \<otimes> map = map \<otimes> Med\<close>
(* Should be used for the receiver *)


(* Apply the function to the input SB *)
definition medMapIn :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mediumMessage tsyn SB  \<rightarrow> 'b mediumMessage tsyn SB" where
"medMapIn f \<equiv> \<Lambda> sb. mediumIn_stream_ar\<cdot>(tsynMap f\<cdot>(medium_get_stream_ar\<cdot>sb))"

definition medMapInSPS:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a mediumMessage tsyn SB  \<Rrightarrow> 'b mediumMessage tsyn SB) uspec" where
"medMapInSPS f = uspecConst (ufLift mediumDom (medMapIn f))"


(* Apply the function to the output SB *)
definition medMapOut :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mediumMessage tsyn SB  \<rightarrow> 'b mediumMessage tsyn SB" where
"medMapOut f \<equiv> \<Lambda> sb. mediumOut_stream_as\<cdot>(tsynMap f\<cdot>(medium_get_stream_as\<cdot>sb))"

definition medMapOutSPS:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a mediumMessage tsyn SB  \<Rrightarrow> 'b mediumMessage tsyn SB) uspec" where
"medMapOutSPS f = uspecConst (ufLift mediumRan (medMapOut f))"


(* Med \<otimes> map = map \<otimes> Med *)
lemma "mediumSPS \<circle> medMapOutSPS f = ((medMapInSPS f) \<circle> mediumSPS)"
  oops

end