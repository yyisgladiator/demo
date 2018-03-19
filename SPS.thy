(* SPS *)

theory SPS
imports SPF
begin


(* Well-typedness: All SPF in the set have the same In- and Output channels *)
definition sps_well :: "'m SPF set \<Rightarrow> bool" where
"sps_well S \<equiv> \<exists>In Out. \<forall> f\<in>S . (spfDom\<cdot>f = In \<and> spfRan\<cdot>f=Out) "

(* Rule to show well-typedness *)
lemma sps_wellI: assumes "\<And>f. f\<in>S \<Longrightarrow> spfDom\<cdot>f = In" and "\<And>f. f\<in>S \<Longrightarrow> spfRan\<cdot>f = Out"
  shows "sps_well S"
by (simp add: assms(1) assms(2) sps_well_def)

(* The SPFs in a Well-typed set all have the same domain *)
lemma sps_dom_eq: assumes "a1\<in>A" and "a2\<in>A" and "sps_well A"
  shows "spfDom\<cdot>a1 = spfDom\<cdot>a2"
by (metis assms(1) assms(2) assms(3) sps_well_def)

(* ... and the same range*)
lemma sps_ran_eq: assumes "a1\<in>A" and "a2\<in>A" and "sps_well A"
  shows "spfRan\<cdot>a1 = spfRan\<cdot>a2"
by (metis assms(1) assms(2) assms(3) sps_well_def)

(* In a chain of well-typed SPF-sets, all SPFs of all chain elements have the same domain and range *)
lemma tsps_well_adm1: assumes "chain Y" and "Y 0 \<noteq> {}" and "\<And>i. sps_well (Y i)"
  shows "sps_well (\<Union>i. Y i)"
proof(rule sps_wellI)
  fix f
  assume as_f: "f\<in>(\<Union>i. Y i)"
  obtain i where i_def: "f\<in>Y i" using as_f by blast
  thus "spfDom\<cdot>f = spfDom\<cdot>(SOME a. a\<in>(Y 0))"
    by (metis assms(1) assms(2) assms(3) contra_subsetD le0 po_class.chain_mono set_cpo_simps(1) some_in_eq sps_dom_eq)
  thus "spfRan\<cdot>f = spfRan\<cdot>(SOME a. a\<in>(Y 0))"
    by (metis i_def assms(1) assms(2) assms(3) contra_subsetD le0 po_class.chain_mono set_cpo_simps(1) some_in_eq sps_ran_eq)
qed


(* sps_well is admissible (compare to TSPS defininition, was already proven there) *)
lemma sps_well_adm[simp]: "adm sps_well"
proof(rule admI)
  fix Y :: "nat \<Rightarrow> 'a SPF set"
  assume as1: "chain Y" and as2: "\<forall>i. sps_well (Y i)"
  hence "sps_well (\<Union>i. Y i)"  
  proof (cases "(\<Union>i. Y i) = {}")
    case True thus ?thesis
      using as2 by auto
  next
    case False
    obtain k where k_def: "Y k\<noteq>{}" using False by auto
    hence chain_d: "chain (\<lambda>i. Y (i + k))" (is "chain ?D") by (simp add: as1 po_class.chainE po_class.chainI)
    have "\<And>i. ?D i \<noteq> {}"
      by (metis as1 empty_subsetI k_def le_add2 po_class.chain_mono set_cpo_simps(1) subset_antisym)
    hence "sps_well (\<Union>i. ?D i)" using as2 chain_d tsps_well_adm1 by blast
    thus ?thesis by (metis as1 lub_range_shift set_cpo_simps(2)) 
  qed
  thus "sps_well (\<Squnion>i. Y i)" by (metis set_cpo_simps(2)) 
qed

(* SPS definition: a set of SPF's with the same In/Out channels *)
pcpodef 'm SPS = "{S :: 'm SPF set. sps_well S }"
   apply (simp add: UU_eq_empty sps_well_def)
  by simp

setup_lifting type_definition_SPS

(* Composite operator on SPS: Composing every f1 in S1 with every f2 in S2 *)
definition spsComp :: "'m SPS \<Rightarrow>'m  SPS \<Rightarrow> 'm SPS" (infixl "\<Otimes>" 50) where
"spsComp S1 S2 \<equiv> Abs_SPS {f1 \<otimes> f2 | f1 f2. f1\<in>(Rep_SPS S1) \<and> f2\<in>(Rep_SPS S2)}"

(* The domain of the SPS is the domain of any of the SPFs inside *)
definition spsDom :: "'m SPS \<Rightarrow> channel set" where
"spsDom S = spfDom\<cdot>(SOME f. f\<in> Rep_SPS S)"

(* The range of the SPS is the range of any of the SPFs inside *)
definition spsRan :: "'m SPS \<Rightarrow> channel set" where
"spsRan S = spfRan\<cdot>(SOME f. f\<in> Rep_SPS S)"



subsection \<open>helpfull lemmas\<close>

(* An SPS with only one SPF is always well-typed *)
lemma sps_well_SingleSet[simp]: "sps_well {f :: 'a SPF}"
  by(simp add: sps_well_def)

(* Rep(Abs) is the identity, if the SPS S is well-typed *)
lemma sps_repAbs[simp]: assumes "sps_well S" shows "Rep_SPS (Abs_SPS S) = S"
  using Abs_SPS_inverse assms by auto

(* Subsets of well-typed SPS' are also well-typed *)
lemma spsWell_subset: assumes "sps_well A" and "a \<subseteq> B" shows "sps_well B"
  sorry
    
end
