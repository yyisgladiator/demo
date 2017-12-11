theory USpec_Comp
  imports USpec
begin

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp

definition uspec_comp_well :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_comp_well S1 S2 \<equiv> uspecRan S1 \<inter> uspecRan S2 = {}"

  (* composite operator on SPS *)
(* THIS IS JUST A DEMO! there should be many changes *)
definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> Abs_uspec (Rev {ufunclComp\<cdot>f1\<cdot>f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)})"


definition uspec_sercomp_well :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_sercomp_well S1 S2 \<equiv> (uspecRan S1 = uspecDom S2) 
                        \<and> (uspecDom S1 \<inter> uspecRan S1 = {})
                        \<and> (uspecDom S2 \<inter> uspecRan S2 = {})
                        \<and> (uspecDom S1 \<inter> uspecRan S2 = {})"

definition uspecSerComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv> Abs_rev_uspec {ufunclSerComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

definition uspec_parcomp_well :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_parcomp_well S1 S2 \<equiv> ((uspecDom S1 \<union> uspecDom S2) \<inter> (uspecRan S1 \<union> uspecRan S2) = {}) \<and> (uspecRan S1 \<inter> uspecRan S2 = {})"
  

definition uspecParComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv> Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"


definition uspecFeedbackComp :: "'m uspec \<Rightarrow> 'm uspec" where
"uspecFeedbackComp S1 \<equiv> Abs_rev_uspec {ufunclFeedbackComp\<cdot>f1 | f1.  f1\<in>(Rep_rev_uspec S1)}"



(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

lemma uspec_comp_well_commu: "uspec_comp_well S1 S2 =  uspec_comp_well S2 S1"
  by (simp add: inf_commute uspec_comp_well_def)

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
        sorry
      then show " \<exists>(f1a::'a) f2a::'a. ufunclComp\<cdot>f1\<cdot>f2 = ufunclComp\<cdot>f2a\<cdot>f1a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec S2"
        using f1_def f2_def by auto
    qed
  next
    show "?R1 \<subseteq> ?L1"
    proof auto
      fix f1 f2 assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
      have "(ufunclComp\<cdot>f2\<cdot>f1) = (ufunclComp\<cdot>f1\<cdot>f2)"
        sorry
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


lemma uspecParComp_well: assumes "uspec_parcomp_well S1 S2" shows "uspecWell {ufunclParComp\<cdot>f1\<cdot>f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2}" 
proof(cases "Rep_rev_uspec S1 = {} \<or> Rep_rev_uspec S2 = {}")
case True
  then show ?thesis
    using uspecWell_def by auto
next
case False
  have f0: "\<forall> f1 \<in> Rep_rev_uspec S1. ufDom\<cdot>f1 = uspecDom S1 \<and> ufRan\<cdot>f1 = uspecRan S1"
    by (simp add: uspec_dom_eq uspec_ran_eq)
  have f1: "\<forall> f2 \<in> Rep_rev_uspec S2. ufDom\<cdot>f2 = uspecDom S2 \<and> ufRan\<cdot>f2 = uspecRan S2"
    by (simp add: uspec_dom_eq uspec_ran_eq)
  show ?thesis 
    apply (simp add: uspecWell_def)
    apply (rule_tac x="uspecDom S1 \<union> uspecDom S2" in exI)
    apply (rule_tac x="uspecRan S1 \<union> uspecRan S2" in exI)
    apply (rule allI)
    apply (rule impI)
  proof -
    fix f::'a
    assume assm1: "\<exists>(f1::'a) f2::'a. f = ufunclParComp\<cdot>f1\<cdot>f2 \<and> f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2"
    obtain f1 f2 where f1_f2_def: "f = ufunclParComp\<cdot>f1\<cdot>f2 \<and> f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2"
      using assm1 by auto
    show " ufDom\<cdot>f = uspecDom S1 \<union> uspecDom S2 \<and> ufRan\<cdot>f = uspecRan S1 \<union> uspecRan S2"
      
      sorry
qed


end
