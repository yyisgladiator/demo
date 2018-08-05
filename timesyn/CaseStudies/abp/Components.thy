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

lemma tsynMaps2tsynMap: "tsynMap f\<cdot>(tsynMap g\<cdot>tsyns) = tsynMap (\<lambda> x. f (g x))\<cdot>tsyns"
  proof (cases "tsyns = \<epsilon>")
    case True
    then show ?thesis
      by simp
  next
    case False
    (*have every_ele: "Fin n < #s \<Longrightarrow> snth n (smap (tsynApplyElem f)\<cdot>(smap (tsynApplyElem g)\<cdot>tsyns)) = (tsynApplyElem (\<lambda>x. f (g x)))\<cdot>(snth n tsyns)"
    have every_ele: "Fin n < #s \<Longrightarrow> snth n (smap f\<cdot>s) = f (snth n s)"*)
    have thesis_l: "smap (tsynApplyElem f)\<cdot>(smap (tsynApplyElem g)\<cdot>tsyns) = smap (tsynApplyElem (\<lambda>x::'c. f (g x)))\<cdot>tsyns"
      sorry
    then show ?thesis
      using tsynmap_insert
      by (simp add: tsynmap_insert)
  qed

lemma tsynMap_id: "tsynMap (\<lambda>x. x)\<cdot>tsyns = tsyns"
  proof -
    have smap_id: "smap (\<lambda>x :: 'a tsyn. x)\<cdot> tsyns = tsyns"
      by (simp add: smap_snth_lemma snths_eq)
    have tsyn_id: "(tsynApplyElem (\<lambda>x :: 'a. x)) = (\<lambda>x :: 'a tsyn. x)"
      by (metis tsynApplyElem.elims)
    have smap_tsyn_id: "smap (tsynApplyElem (\<lambda>x :: 'a. x))\<cdot> tsyns = tsyns"
      by (simp add: local.smap_id tsyn_id)
    show ?thesis
      by (simp add: smap_tsyn_id tsynMap_def)
  qed

(* ----------------------------------------------------------------------- *)
  subsection {* Pair_nat_bool *}
(* ----------------------------------------------------------------------- *)

lemma pair_nat_bool_inver: "(\<lambda>x::nat \<times> bool. invPair (Pair_nat_bool x)) nb = nb"
  by (metis invPair.simps(1) surj_pair)                    

lemma natbool2abp2natbool: "abp2natbool\<cdot>(natbool2abp\<cdot>tsyns) = tsyns"
  apply (simp add: abp2natbool_def natbool2abp_def)
  apply (simp add: tsynMaps2tsynMap)
  apply (simp add: pair_nat_bool_inver)
  by (simp add: tsynMap_id)

(*lemma invpair_inver: "(\<lambda>x::abpMessage. Pair_nat_bool (invPair x)) n = n"
  sorry*)

(*lemma abp2natbool2abp: assumes "tsynDom\<cdot>tsyns \<subseteq> {null} \<union> (Msg ` range (Pair_nat_bool))"
  shows "natbool2abp\<cdot>(abp2natbool\<cdot>tsyns) = tsyns"
  sorry*)

(* ----------------------------------------------------------------------- *)
  subsection {* Bool *}
(* ----------------------------------------------------------------------- *)

lemma bool2abp2bool: "abp2bool\<cdot>(bool2abp\<cdot>tsyns) = tsyns"
  apply (simp add: abp2bool_def bool2abp_def)
  apply (simp add: tsynMaps2tsynMap)
  by (simp add: tsynMap_id)

lemma invbool_inver: assumes "(m::abpMessage) = Bool b" 
  shows "Bool (invBool m) = m"
  using assms invBool.simps(1) by blast

(*lemma abp2bool2abp: assumes "tsynDom\<cdot>tsyns \<subseteq> {null} \<union> (Msg Bool)"
  shows "bool2abp\<cdot>(abp2bool\<cdot>tsyns) = tsyns"
  apply (simp add: abp2bool_def bool2abp_def)
  apply (simp add: tsynMaps2tsynMap)
  sorry*)

(* ----------------------------------------------------------------------- *)
  subsection {* Nat *}
(* ----------------------------------------------------------------------- *)

lemma nat2abp2nat: "abp2nat\<cdot>(nat2abp\<cdot>tsyns) = tsyns"
  apply (simp add: abp2nat_def nat2abp_def)
  apply (simp add: tsynMaps2tsynMap)
  by (simp add: tsynMap_id)

lemma abp2nat2abp: "nat2abp\<cdot>(abp2nat\<cdot>tsyns) = tsyns"
  sorry  



end