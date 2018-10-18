theory MediumProof

imports medUnfairAut
          spec.SPS spec.USpec_UFunComp

begin

default_sort countable



section \<open>Med \<otimes> Med = Med\<close>



lift_definition medOut2In :: "('e) mediumMessage tsyn SB \<rightarrow> ('e::countable) mediumMessage tsyn SB" is
"\<lambda>sb. mediumIn_stream_i \<cdot> (medium_get_stream_o\<cdot>sb)"
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
"medMapIn f \<equiv> \<Lambda> sb. mediumIn_stream_i\<cdot>(tsynMap f\<cdot>(medium_get_stream_i\<cdot>sb))"

definition medMapInSPS:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a mediumMessage tsyn SB  \<Rrightarrow> 'b mediumMessage tsyn SB) uspec" where
"medMapInSPS f = uspecConst (ufLift mediumDom (medMapIn f))"


(* Apply the function to the output SB *)
definition medMapOut :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mediumMessage tsyn SB  \<rightarrow> 'b mediumMessage tsyn SB" where
"medMapOut f \<equiv> \<Lambda> sb. mediumOut_stream_o\<cdot>(tsynMap f\<cdot>(medium_get_stream_o\<cdot>sb))"

definition medMapOutSPS:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a mediumMessage tsyn SB  \<Rrightarrow> 'b mediumMessage tsyn SB) uspec" where
"medMapOutSPS f = uspecConst (ufLift mediumRan (medMapOut f))"


(* Med \<otimes> map = map \<otimes> Med *)
(* Version 1 *)
lemma "mediumSPS \<circle> medMapOutSPS f = ((medMapInSPS f) \<circle> mediumSPS)"
  oops

(* Med \<otimes> map = map \<otimes> Med *)
(* Version 2 *)
lemma assumes "spf\<in>uspecSet mediumSPS"
  shows "spfConcIn (mediumIn_stream_i\<cdot>(tsynMap f\<cdot>s))\<cdot>spf = spfConcOut(mediumOut_stream_o\<cdot>(tsynMap f\<cdot>(medium_get_stream_o\<cdot>sb)))\<cdot>spf"
  oops




  section \<open>inf in = inf out\<close>

lemma assumes "spf\<in>uspecSet mediumSPS"
      and "# (tsynAbs\<cdot>s) = \<infinity>"
    shows "#(tsynAbs\<cdot>(medium_get_stream_o\<cdot>(spf \<rightleftharpoons>  (mediumIn_stream_i\<cdot>s)))) = \<infinity> "
  oops


end