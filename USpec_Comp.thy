theory USpec_Comp
  imports USpec
begin


(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp

definition uspec_comp_well :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_comp_well S1 S2 \<equiv> \<forall> f1 f2. f1 \<in> (Rep_rev_uspec S1) \<and> f2 \<in> (Rep_rev_uspec S2) \<and> ufunclCompWell f1 f2"

  (* composite operator on SPS *)
(* THIS IS JUST A DEMO! there should be many changes *)
definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> Abs_uspec (Rev {ufunclComp\<cdot>f1\<cdot>f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)})"


definition uspec_sercomp_well :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_sercomp_well S1 S2 \<equiv> \<forall> f1 f2. f1 \<in> (Rep_rev_uspec S1) \<and> f2 \<in> (Rep_rev_uspec S2) \<and> ufunclSerCompWell f1 f2"

definition uspecSerComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv> Abs_rev_uspec {ufunclSerComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

definition uspec_parcomp_well :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_parcomp_well S1 S2 \<equiv> \<forall> f1 f2. f1 \<in> (Rep_rev_uspec S1) \<and> f2 \<in> (Rep_rev_uspec S2) \<and> ufunclParCompWell f1 f2"
  

definition uspecParComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv> Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"


definition uspecFeedbackComp :: "'m uspec \<Rightarrow> 'm uspec" where
"uspecFeedbackComp S1 \<equiv> Abs_rev_uspec {ufunclFeedbackComp\<cdot>f1 | f1.  f1\<in>(Rep_rev_uspec S1)}"



(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

lemma uspec_comp_well_commu: "uspec_comp_well S1 S2 =  uspec_comp_well S2 S1"
  using uspec_comp_well_def by blast

lemma rev_eqI: assumes "x = y"
  shows "Rev x = Rev y"
  by (simp add: assms)

lemma abs_uspec_eqI: assumes "x = y"
  shows "Abs_uspec x = Abs_uspec y"
  by (simp add: assms)

lemma rev_abs_uspec_eqI: assumes "x = y"
  shows "Abs_rev_uspec x = Abs_rev_uspec y"
  by (simp add: assms)

lemma uspecCompCommu: assumes "uspec_comp_well S1 S2"
  shows "(S1 \<Otimes> S2) =  (S2 \<Otimes> S1)" (is "?L = ?R")
proof -
  have f1: " {ufunclComp\<cdot>f1\<cdot>f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} =
     {ufunclComp\<cdot>f2\<cdot>f1 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2}" (is "?L1 = ?R1")
  proof rule
    show "?L1 \<subseteq> ?R1"
    proof auto
      fix f1 f2 assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
      have "(ufunclComp\<cdot>f1\<cdot>f2) = (ufunclComp\<cdot>f2\<cdot>f1)"
        using assms ufunclcomp_commute uspec_comp_well_def by blast
      then show " \<exists>(f1a::'a) f2a::'a. ufunclComp\<cdot>f1\<cdot>f2 = ufunclComp\<cdot>f2a\<cdot>f1a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec S2"
        using f1_def f2_def by auto
    qed
  next
    show "?R1 \<subseteq> ?L1"
    proof auto
      fix f1 f2 assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
      have "(ufunclComp\<cdot>f2\<cdot>f1) = (ufunclComp\<cdot>f1\<cdot>f2)"
        using assms ufunclcomp_commute uspec_comp_well_def by blast
      then show "\<exists>(f1a::'a) f2a::'a. ufunclComp\<cdot>f2\<cdot>f1 = ufunclComp\<cdot>f1a\<cdot>f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec S2"
        using f1_def f2_def by auto
    qed
  qed
  have "Abs_rev_uspec {ufunclComp\<cdot>f1\<cdot>f2|(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} =
    Abs_rev_uspec {ufunclComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}"
  proof -
    have "{ufunclComp\<cdot>a\<cdot>aa |a aa. a \<in> Rep_rev_uspec S2 \<and> aa \<in> Rep_rev_uspec S1} = {ufunclComp\<cdot>aa\<cdot>a |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2}"
      by blast
    then show ?thesis
      by (simp add: f1)
  qed
  then  show ?thesis
    by (simp add: uspecComp_def)
qed



lemma uspecParCompCommu: assumes "uspec_parcomp_well S1 S2"
  shows "(S1 \<parallel> S2) =  (S2 \<parallel> S1)" (is "?L = ?R")
proof -
  have "{ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} =
    {ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L1 = ?R1")
  proof rule
    show "?L1 \<subseteq> ?R1"
    proof auto
      fix f1 f2 assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
      have "(ufunclParComp\<cdot>f1\<cdot>f2) = (ufunclParComp\<cdot>f2\<cdot>f1)"
        using assms ufunclparcomp_commute uspec_parcomp_well_def by blast
      then show "\<exists>(f1a::'a) f2a::'a. ufunclParComp\<cdot>f1\<cdot>f2 = ufunclParComp\<cdot>f1a\<cdot>f2a \<and> f1a \<in> Rep_rev_uspec S2 \<and> f2a \<in> Rep_rev_uspec S1"
        using f1_def f2_def by auto
    qed
  next
    show "?R1 \<subseteq> ?L1"
    proof auto
      fix f1 f2 assume f1_def: "f1 \<in> Rep_rev_uspec S2" and f2_def: "f2 \<in> Rep_rev_uspec S1"
      have "(ufunclParComp\<cdot>f1\<cdot>f2) = (ufunclParComp\<cdot>f2\<cdot>f1)"
        using assms ufunclparcomp_commute uspec_parcomp_well_def by blast
      then show "\<exists>(f1a::'a) f2a::'a. ufunclParComp\<cdot>f1\<cdot>f2 = ufunclParComp\<cdot>f1a\<cdot>f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec S2"
        using f1_def f2_def by auto
    qed
  qed
  then have "Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} =
    Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}"
    by simp
  then show ?thesis
    by (simp add: uspecParComp_def)
qed


lemma uspecParCompWell: assumes "uspec_parcomp_well S1 S2"
  shows "uspecWell {ufunclParComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"
    apply (simp add: uspecWell_def)
    apply (rule_tac x="uspecDom S1 \<union> uspecDom S2" in exI)
    apply (rule_tac x="uspecRan S1 \<union> uspecRan S2" in exI)
    by (metis (no_types, hide_lams) assms sup_idem uspec_dom_eq uspec_parcomp_well_def uspec_ran_eq)


lemma inv_rev_rev: "inv Rev (Rev S) = S"
  by (simp add: inv_def)

lemma uspecParCompAsso: assumes "uspec_parcomp_well S1 S2" and "uspec_parcomp_well S1 S3" and "uspec_parcomp_well S2 S3"
  shows "((S1 \<parallel> S2) \<parallel> S3) =  (S1 \<parallel> (S2 \<parallel> S3))" (is "?L = ?R")
proof -
  have "{ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
    {ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}" (is "?L1 = ?R1")
  proof rule
    show "?L1 \<subseteq> ?R1"
    proof auto
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<parallel> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_f4_def: "f3 \<in> Rep_rev_uspec S1 \<and> f4 \<in> Rep_rev_uspec S2 \<and> f1 = ufunclParComp\<cdot>f3\<cdot>f4"
        by (smt UNIV_I f1_def assms(1) f_inv_into_f image_eqI mem_Collect_eq rep_abs_uspec rev.inject uspecParCompWell uspecParComp_def)
      have f1: "ufunclParComp\<cdot>f1\<cdot>f2 = ufunclParComp\<cdot>(ufunclParComp\<cdot>f3\<cdot>f4)\<cdot>f2"
        by (simp add: f3_f4_def)
      have f2: "ufunclParComp\<cdot>(ufunclParComp\<cdot>f3\<cdot>f4)\<cdot>f2 = ufunclParComp\<cdot>f3\<cdot>(ufunclParComp\<cdot>f4\<cdot>f2)"
        using assms(3) ufunclparcomp_asso uspec_parcomp_well_def by blast
      have f3: "(ufunclParComp\<cdot>f4\<cdot>f2) \<in> Rep_rev_uspec (S2 \<parallel> S3)"
        apply (simp add: uspecParComp_def)
        apply (subst rep_abs_uspec)
         apply (simp add: assms(3) uspecParCompWell)
        apply (simp add: inv_rev_rev)
        using f2_def f3_f4_def by auto
      show "\<exists>(f1a::'a) f2a::'a. ufunclParComp\<cdot>f1\<cdot>f2 = ufunclParComp\<cdot>f1a\<cdot>f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
        using f2 f3 f3_f4_def by auto
    qed
  next
    show "?R1 \<subseteq> ?L1"
    proof auto
      fix f2::'a and f1::'a
      assume f2_def: "f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)" and f1_def: "f1 \<in> Rep_rev_uspec S1"
      obtain f3 f4 where f3_f4_def: "f3 \<in> Rep_rev_uspec S2 \<and> f4 \<in> Rep_rev_uspec S3 \<and> f2 = ufunclParComp\<cdot>f3\<cdot>f4"
        by (smt assms(3) f2_def inv_rev_rev mem_Collect_eq rep_abs_uspec uspecParCompWell uspecParComp_def)
      have f1: "ufunclParComp\<cdot>f1\<cdot>f2 = ufunclParComp\<cdot>f1\<cdot>(ufunclParComp\<cdot>f3\<cdot>f4)"
        by (simp add: f3_f4_def)
      have f2: "ufunclParComp\<cdot>f1\<cdot>(ufunclParComp\<cdot>f3\<cdot>f4) = ufunclParComp\<cdot>(ufunclParComp\<cdot>f1\<cdot>f3)\<cdot>f4"
        by (metis assms(1) ufunclparcomp_asso uspec_parcomp_well_def)
      have f3: "(ufunclParComp\<cdot>f1\<cdot>f3) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
        apply (simp add: uspecParComp_def)
        apply (subst rep_abs_uspec)
         apply (simp add: assms uspecParCompWell)
        apply (simp add: inv_rev_rev)
        using f1_def f3_f4_def by auto
      show "\<exists>(f1a::'a) f2a::'a. ufunclParComp\<cdot>f1\<cdot>f2 = ufunclParComp\<cdot>f1a\<cdot>f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        using f2 f3 f3_f4_def by auto
    qed
  qed
  then have "Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
              Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
    by simp
  then show ?thesis
    by (simp add: uspecParComp_def)
qed


end
