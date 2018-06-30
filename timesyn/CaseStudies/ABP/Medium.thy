(*  Title:        Medium.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for Medium Lemmata.
*)

chapter {* Theory for Medium Lemmata *}

theory Medium
imports "../../tsynStream" 

begin

(* ----------------------------------------------------------------------- *)
  section {* Medium SPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text{* Time synchronous medium, that loses messages. *}
definition tsynMed :: "'a tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" where
  "tsynMed \<equiv> \<Lambda> msg ora. tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

lemma oracases [case_names bottom true false]:
  assumes bottom: "ts=\<bottom> \<Longrightarrow> P ts"
    and true: "\<And>as. ts= (\<up>True \<bullet> as) \<Longrightarrow> P ts"
    and false: "\<And>as. ts=(\<up>False \<bullet> as) \<Longrightarrow> P ts"
  shows "P ts"
  by (metis (full_types) bottom false scases true)

text{* "Lossy" medium that gets messages and an oracle and will transmit the k-th message if
       the k-th element in the oracle is True, otherwise the message will be discarded. *}
lemma tsynmed_insert: "tsynMed\<cdot>msg\<cdot>ora = tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsynMed_def)

end