theory SPS

imports fun.SPF USpec_Comp

begin

default_sort message

type_synonym ('m,'n) SPS = "('m,'n) SPF uspec"

section \<open>Definition\<close>

definition uspecConstOut:: "channel set \<Rightarrow> 'n::message SB  \<Rightarrow> ('m,'n) SPF uspec" where
"uspecConstOut \<equiv> \<lambda> In sb. uspecConst (ufConst In\<cdot>sb)"

definition spsConcOut:: "'n SB \<Rightarrow> ('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsConcOut sb = (uspecImageC (spfConcOut sb))"

definition spsConcIn:: "'m SB \<Rightarrow> ('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsConcIn sb = uspecImageC (spfConcIn sb)"

definition spsRtIn:: "('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsRtIn = uspecImageC spfRtIn"


section \<open>Lemma\<close>

(* ----------------------------------------------------------------------- *)
subsection \<open>uspecConstOut\<close>
(* ----------------------------------------------------------------------- *)
lemma uspecconstout_insert: "uspecConstOut In sb = uspecConst (ufConst In\<cdot>sb)"
  by (simp add: uspecConstOut_def)

lemma uspecconstout_dom[simp]: "uspecDom\<cdot>(uspecConstOut In sb) = In"
  apply (simp add: uspecconstout_insert)
  by (simp add: ufclDom_ufun_def uspecconst_dom)

lemma uspecconstout_ran[simp]: "uspecRan\<cdot>(uspecConstOut In sb) = ubclDom\<cdot>sb"
  apply (simp add: uspecconstout_insert)
  by (simp add: ufclRan_ufun_def uspecconst_ran)


(* ----------------------------------------------------------------------- *)
subsection \<open>spsConcOut\<close>
(* ----------------------------------------------------------------------- *)

lemma spsconcout_mono: "monofun (uspecImage (Rep_cfun (spfConcOut sb)))"
  apply (rule uspecimage_mono)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)


lemma spsconcout_dom [simp]: 
  "uspecDom\<cdot>(spsConcOut sb\<cdot>sps) = uspecDom\<cdot>sps"
  apply (simp add: spsConcOut_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def uspecimagec_insert)

lemma spsconcout_ran [simp]: 
  "uspecRan\<cdot>(spsConcOut sb\<cdot>sps) = uspecRan\<cdot>sps"
  apply (simp add: spsConcOut_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def uspecimagec_insert)

lemma spsconcout_obtain: assumes "g \<in> uspecSet\<cdot>(spsConcOut sb\<cdot>sps)"
  shows "\<exists> f. f\<in>(uspecSet\<cdot>sps) \<and> g = spfConcOut sb\<cdot>f"
  by (metis (no_types, lifting) assms image_iff spsConcOut_def uspecimagec_set)

lemma spsconcout_const[simp]: "spsConcOut sb\<cdot>(uspecConst f) = uspecConst (spfConcOut sb\<cdot>f)"
  by(simp add: spsConcOut_def)

lemma spsconcout_consistentI: assumes "uspecIsConsistent S" 
  shows "uspecIsConsistent (spsConcOut sb\<cdot>S)"
  by (simp add: assms spsConcOut_def)

(* ----------------------------------------------------------------------- *)
subsection \<open>spsConcIn\<close>
(* ----------------------------------------------------------------------- *)

lemma spsconcin_dom[simp]: "uspecDom\<cdot>(spsConcIn sb\<cdot>sps) = uspecDom\<cdot>sps"
  by (simp add: spfconcin_uspec_iamge_well spsConcIn_def ufuncldom_least_dom uspecimagec_dom)

lemma spsconcin_ran[simp]:  "uspecRan\<cdot>(spsConcIn sb\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: spfconcin_uspec_iamge_well spsConcIn_def ufclRan_ufun_def uspecimagec_insert)

lemma spsconcin_const[simp]: "spsConcIn sb\<cdot>(uspecConst f) = uspecConst (spfConcIn sb\<cdot>f)"
  by(simp add: spsConcIn_def)

(* ----------------------------------------------------------------------- *)
subsection \<open>spsRtIn\<close>
(* ----------------------------------------------------------------------- *)

lemma spsrtin_dom [simp]: "uspecDom\<cdot>(spsRtIn\<cdot>sps) = uspecDom\<cdot>sps"
  by (metis spfRtIn_dom spsRtIn_def ufclDom_ufun_def ufuncldom_least_dom uspecimagec_dom)

lemma spsrtin_ran [simp]: "uspecRan\<cdot>(spsRtIn\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: spsRtIn_def ufclDom_ufun_def ufclRan_ufun_def uspecimagec_insert)

end