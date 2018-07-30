(*  Title:        Components.thy
    Author:       Dennis Slotboom, Annika Savelsberg
    E-Mail:       dennis.slotboom@rwth-aachen.de, annika.savelsberg@rwth-aachen.de

    Description:  Theory for ABP Component Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for ABP Component Lemmata on Time-synchronous Streams *}

theory Components
imports "../AutomatonPrelude"

begin

(* ----------------------------------------------------------------------- *)
  section {* Datatype Conversion *}
(* ----------------------------------------------------------------------- *)

text {* Inverse of a Pair. *}
fun invPair :: "abpMessage \<Rightarrow> (nat \<times> bool)" where
  "invPair (Pair_nat_bool (n,b)) = (n,b)" |
  "invPair n = undefined"

text {* Conversion of a pair (nat,bool) stream into an equivalent receiver stream. *}
definition natbool2abp :: "(nat \<times> bool) tsyn stream \<rightarrow> abpMessage tsyn stream" where
  "natbool2abp \<equiv> tsynMap Pair_nat_bool"

text {* Conversion of a receiver stream into an equivalent pair (nat,bool) stream. *}
definition abp2natbool :: "abpMessage tsyn stream \<rightarrow> (nat \<times> bool) tsyn stream" where
  "abp2natbool \<equiv> tsynMap invPair"

text {* Inverse of a Bool. *}
fun invBool :: "abpMessage \<Rightarrow> bool" where
  "invBool (Bool x) = x" |
  "invBool x = undefined"

text {* Conversion of a bool stream into an equivalent receiver stream. *}
definition bool2abp :: "bool tsyn stream \<rightarrow> abpMessage tsyn stream" where
  "bool2abp \<equiv> tsynMap Bool"

text {* Conversion of a receiver stream into an equivalent bool stream. *}
definition abp2bool :: "abpMessage tsyn stream \<rightarrow> bool tsyn stream" where
  "abp2bool \<equiv> tsynMap invBool"

text {* Inverse of a Nat. *}
fun invNat :: "abpMessage \<Rightarrow> nat" where
  "invNat (Nat x) = x" |
  "invNat x = undefined"

text {* Conversion of a nat stream into an equivalent receiver stream. *}
definition nat2abp :: "nat tsyn stream \<rightarrow> abpMessage tsyn stream" where
  "nat2abp \<equiv> tsynMap Nat"

text {* Conversion of a receiver stream into an equivalent nat stream. *}
definition abp2nat :: "abpMessage tsyn stream \<rightarrow> nat tsyn stream" where
  "abp2nat \<equiv> tsynMap invNat"

(* ----------------------------------------------------------------------- *)
  section {* Datatype Conversion Lemmata *}
(* ----------------------------------------------------------------------- *)

lemma test1: "invPair (Pair_nat_bool n) = n"
  by (metis invPair.simps(1) old.prod.exhaust)

lemma test2: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (\<lambda> x. f (g x))\<cdot>s"
  apply (simp add: tsynmap_insert)
  sorry

lemma natbool2abp2natbool: "abp2natbool\<cdot>(natbool2abp\<cdot>s) = s"
  apply (simp add: abp2natbool_def natbool2abp_def)
  apply (simp add: test2)
  apply (simp add: tsynmap_insert)
  sorry

lemma abp2natbool2abp: "natbool2abp\<cdot>(abp2natbool\<cdot>s) = s"
  sorry

lemma bool2abp2bool: "abp2bool\<cdot>(bool2abp\<cdot>s) = s"
  sorry

lemma abp2bool2abp: "bool2abp\<cdot>(abp2bool\<cdot>s) = s"
  sorry

lemma nat2abp2nat: "abp2nat\<cdot>(nat2abp\<cdot>s) = s"
  sorry

lemma abp2nat2abp: "nat2abp\<cdot>(abp2nat\<cdot>s) = s"
  sorry  



end