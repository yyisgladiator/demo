theory USpec_Comp
  imports USpec
begin

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp

(* General Composition  *)
definition uspec_compwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_compwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclCompWell f1 f2"

definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> Abs_uspec (Rev {f1 \<otimes> f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)})"

(* Serial Composition *)
definition uspec_sercompwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_sercompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclSerCompWell f1 f2"

definition uspecSerComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv> Abs_rev_uspec {f1 \<circ> f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

(* Parallel Composition *)
definition uspec_parcompwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_parcompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclParCompWell f1 f2"  

definition uspecParComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv> Abs_rev_uspec {f1 \<parallel> f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

(* Feedback Composition *)
definition uspecFeedbackComp :: "'m uspec \<Rightarrow> 'm uspec" where
"uspecFeedbackComp S1 \<equiv> Abs_rev_uspec {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)}"



(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

subsection \<open>UspecComp\<close>

(*   *)
lemma uspec_compwell_commu: "uspec_compwell S1 S2 =  uspec_compwell S2 S1"
  using ufunclCompWell_commute uspec_compwell_def by blast

lemma uspec_comp_well[simp]: assumes "uspec_compwell S1 S2"
  shows "uspecWell {f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2}"

(*fallunterscheidung s1 oder s2 leer*)
proof (cases "Rep_rev_uspec S1 = {} \<or> Rep_rev_uspec S2 = {}")
  case True
  then show ?thesis
    by auto
next
  case False
  then show ?thesis
    apply (simp add: uspecWell_def)
    apply (rule_tac x="(uspecDom S1 \<union> uspecDom S2) - (uspecRan S1 \<union> uspecRan S2)" in exI)
    apply (rule_tac x="uspecRan S1 \<union> uspecRan S2" in exI)
    by (metis assms ufuncl_comp_dom ufuncl_comp_ran uspec_compwell_def uspec_dom_eq uspec_ran_eq)
qed

(*   *)
lemma uspec_comp_commu: assumes "uspec_compwell S1 S2"
  shows "(S1 \<Otimes> S2) = (S2 \<Otimes> S1)"
proof - 
  have "{f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} = 
             {f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L = ?R")
    apply auto
    using  assms comp_commute uspec_compwell_def by metis +
  then show ?thesis
    by (simp add: uspecComp_def)
qed

lemma uspec_comp_rep[simp]: assumes "uspec_compwell S1 S2"
shows "{f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<Otimes> S2)"
  apply (simp add: uspecComp_def)
  using assms(1) rep_abs_rev_simp uspec_comp_well by blast

lemma uspec_comp_ele_ex: assumes "uspec_compwell S1 S2"
and "uspecIsConsistent (S1 \<Otimes> S2)"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<Otimes> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = f1 \<otimes> f2"
  using assms uspec_comp_rep by fastforce

lemma uspec_comp_not_empty:  assumes "uspec_compwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<otimes> f2) \<in> Rep_rev_uspec (S1 \<Otimes> S2)"
  by (metis (mono_tags, lifting) assms(1) assms(2) f2_def mem_Collect_eq rep_abs_rev_simp uspecComp_def uspec_comp_well)

lemma uspec_comp_consistent2: assumes "uspecIsConsistent (S1 \<Otimes> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
proof (rule)
  have f1: "uspecIsConsistent (Abs_rev_uspec {a \<otimes> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2})"
    by (metis (no_types) assms(1) uspecComp_def)
  then have f2: "\<not> uspecWell {a \<otimes> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<or> {a \<otimes> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    by (metis (lifting) rep_abs_rev_simp uspecIsConsistent_def)
  then have f3: "{a \<otimes> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    by (metis empty_uspecwell)
  then show "uspecIsConsistent S1"
    using uspecIsConsistent_def by force
  show "uspecIsConsistent S2"
    using f3 uspecIsConsistent_def by auto
qed

lemma uspec_comp_dom: assumes "uspec_compwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecDom (S1 \<Otimes> S2) = (uspecDom S1 \<union> uspecDom S2) - (uspecRan S1 \<union> uspecRan S2)" (*UFun_Comp \<rightarrow> dom*)
proof -
  obtain f1 and f2 where f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
    by (meson all_not_in_conv assms(2) assms(3) uspecIsConsistent_def)
  have "(f1 \<otimes> f2) \<in> Rep_rev_uspec (S1 \<Otimes> S2)"
    by (metis (mono_tags, lifting) assms(1) f1_def f2_def mem_Collect_eq rep_abs_rev_simp uspecComp_def uspec_comp_well)
  then show ?thesis
    apply (simp add: uspecDom_def)   
    by (metis uspec_ran_eq assms(1) f1_def f2_def ufuncl_comp_dom uspecDom_def uspec_dom_eq uspec_compwell_def ufuncl_comp_dom)
qed

lemma uspec_comp_h2: assumes "uspec_compwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclCompWell f1 f2"
  using assms uspec_compwell_def by blast



subsection \<open>UspecParComp\<close>

(*   *)
lemma uspec_parcompwell_commu: "uspec_parcompwell S1 S2 = uspec_parcompwell S2 S1"
  using ufunclParCompWell_commute uspec_parcompwell_def by blast

(*   *)
lemma uspec_parcomp_well[simp]: assumes "uspec_parcompwell S1 S2"
  shows "uspecWell {f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2}"
  apply (simp add: uspecWell_def)
  apply (rule_tac x="uspecDom S1 \<union> uspecDom S2" in exI)
  apply (rule_tac x="uspecRan S1 \<union> uspecRan S2" in exI)
  by (metis assms ufuncl_parcomp_dom ufuncl_parcomp_ran uspec_dom_eq uspec_parcompwell_def uspec_ran_eq)

(*   *)
lemma uspec_parcomp_abs[simp]: assumes "uspec_parcompwell S1 S2"
shows "Abs_rev_uspec {f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = (S1 \<parallel> S2)"
  by (simp add: uspecParComp_def)

(*   *)
lemma uspec_parcomp_rep[simp]: assumes "uspec_parcompwell S1 S2"
shows "{f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<parallel> S2)"
  apply (simp add: uspecParComp_def)
  using assms(1) rep_abs_rev_simp uspec_parcomp_well by blast

(*   *)
lemma uspec_parcomp_not_empty:  assumes "uspec_parcompwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<parallel> f2) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
  by (metis (mono_tags, lifting) assms(1) assms(2) f2_def mem_Collect_eq rep_abs_rev_simp 
      uspecParComp_def uspec_parcomp_well)

(*   *)
lemma uspec_parcomp_consistent: assumes "uspec_parcompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecIsConsistent (S1 \<parallel> S2)"
  by (metis assms(1) assms(2) assms(3) emptyE some_in_eq uspecIsConsistent_def uspec_parcomp_not_empty)

(*   *)
lemma uspec_parcomp_consistent2: assumes "uspec_parcompwell S1 S2" and "uspecIsConsistent (S1 \<parallel> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
proof (rule)
  have f1: "{a \<parallel> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    using assms(1) assms(2) uspecIsConsistent_def by auto
  then have "Rep_rev_uspec S1 \<noteq> {}"
    by blast
  then show "uspecIsConsistent S1"
    by (meson uspecIsConsistent_def)
  have "Rep_rev_uspec S2 \<noteq> {}"
    using f1 by blast
  then show "uspecIsConsistent S2"
    by (meson uspecIsConsistent_def)
qed

(*   *)
lemma uspec_parcomp_dom: assumes "uspec_parcompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecDom (S1 \<parallel> S2) = uspecDom S1 \<union> uspecDom S2"
proof -
  obtain f1 and f2 where f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
    by (meson all_not_in_conv assms(2) assms(3) uspecIsConsistent_def)
  have "(f1 \<parallel> f2) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
    by (metis (mono_tags, lifting) assms(1) f1_def f2_def mem_Collect_eq rep_abs_rev_simp uspecParComp_def uspec_parcomp_well)
  then show ?thesis
    apply (simp add: uspecDom_def)
    using assms(1) f1_def f2_def ufuncl_parcomp_dom uspecDom_def uspec_dom_eq uspec_parcompwell_def by blast
qed

(*   *)
lemma uspec_parcomp_ran: assumes "uspec_parcompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecRan (S1 \<parallel> S2) = uspecRan S1 \<union> uspecRan S2"
proof -
  obtain f1 and f2 where f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
    by (meson all_not_in_conv assms(2) assms(3) uspecIsConsistent_def)
  have "(f1 \<parallel> f2) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
    by (metis (mono_tags, lifting) assms(1) f1_def f2_def mem_Collect_eq rep_abs_rev_simp uspecParComp_def uspec_parcomp_well)
  then show ?thesis
    using assms(1) f1_def f2_def ufuncl_parcomp_ran uspec_parcompwell_def uspec_ran_eq by blast
qed

lemma uspec_parcomp_h1: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. f1 \<parallel> f2 \<in> Rep_rev_uspec (S1 \<parallel> S2)"
  by (simp add: assms uspec_parcomp_not_empty)

lemma uspec_parcomp_h2: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclParCompWell f1 f2"
  using assms uspec_parcompwell_def by auto

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_parcomp_ele_ex: assumes "uspec_parcompwell S1 S2"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<parallel> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = f1 \<parallel> f2"
  using assms(1) uspec_parcomp_rep by fastforce

(* uspec parcomp is commutative  *)
lemma uspec_parcomp_commu: assumes "uspec_parcompwell S1 S2"
  shows "(uspecParComp S1 S2) = (uspecParComp S2 S1)"
proof -
  have f1: "{f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} = 
                {f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L = ?R")
    apply auto
    using assms parcomp_commute uspec_parcompwell_def by metis +
  show ?thesis
    apply (simp add: uspecParComp_def)
    using f1 by auto
qed

(* uspec parcomp is associative  *)
lemma uspec_parcomp_asso: assumes "uspec_parcompwell S1 S2"
and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3"
shows "uspecParComp (uspecParComp S1 S2) S3 = uspecParComp S1 (uspecParComp S2 S3)"
proof -
  have f10: "{f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
               {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
  proof (auto)
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<Longrightarrow> f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<parallel> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" and f1_eq_f3_f4: "f1 = f3 \<parallel> f4"
        by (metis assms(1) empty_iff f1_def uspecIsConsistent_def uspec_parcomp_ele_ex)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
        by (metis (no_types, lifting) assms(1) assms(2) assms(3) f2_def parcomp_asso uspec_parcomp_not_empty uspec_parcompwell_def)
    qed
  next
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<Longrightarrow> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3) \<Longrightarrow> 
              \<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" and f2_eq_f3_f4: "f2 = f3 \<parallel> f4"
        by (metis assms(3) empty_iff f2_def uspecIsConsistent_def uspec_parcomp_ele_ex)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        by (meson assms(1) assms(2) assms(3) f1_def parcomp_asso uspec_parcomp_not_empty uspec_parcompwell_def)
    qed
  qed
  then show ?thesis
    by (simp add: uspecParComp_def)
qed

(*   *)
lemma uspec_parcompwell_asso_h: assumes "uspec_parcompwell S1 S2" and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3" shows "uspec_parcompwell S1 (S2 \<parallel> S3)"
  apply (simp add: uspec_parcompwell_def, auto)
  by (metis assms(1) assms(2) assms(3) empty_iff parcompwell_asso 
      uspecIsConsistent_def uspec_parcomp_ele_ex uspec_parcompwell_def)

(* the new component is uspecwell  *) 
lemma uspec_parcompwell_asso: assumes "uspec_parcompwell S1 S2" and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3" 
shows "uspecWell  {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
  by (simp add: assms(1) assms(2) assms(3) uspec_parcompwell_asso_h)

subsection \<open>UspecSerComp\<close>

(*   *)
lemma uspec_sercomp_well[simp]: assumes "uspec_sercompwell S1 S2"
  shows "uspecWell {f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2}"
  apply (simp add: uspecWell_def)
  apply (rule_tac x="uspecDom S1" in exI)
  apply (rule_tac x="uspecRan S2" in exI)
  using assms ufuncl_sercomp_dom ufuncl_sercomp_ran uspec_dom_eq uspec_ran_eq uspec_sercompwell_def by blast

(*   *)
lemma uspec_sercomp_abs[simp]: assumes "uspec_sercompwell S1 S2"
shows "Abs_rev_uspec {f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = (S1 \<circle> S2)"
  by (simp add: uspecSerComp_def)

(*   *)
lemma uspec_sercomp_rep[simp]: assumes "uspec_sercompwell S1 S2"
shows "{f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<circle> S2)"
  apply (simp add: uspecSerComp_def)
  using assms(1) rep_abs_rev_simp uspec_sercomp_well by blast

(*   *)
lemma uspec_sercomp_not_empty:  assumes "uspec_sercompwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<circ> f2) \<in> Rep_rev_uspec (S1 \<circle> S2)"
  by (metis (mono_tags, lifting) assms(1) assms(2) f2_def mem_Collect_eq rep_abs_rev_simp uspecSerComp_def uspec_sercomp_well)

(*   *)
lemma uspec_sercomp_consistent: assumes "uspec_sercompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecIsConsistent (S1 \<circle> S2)"
  by (metis assms(1) assms(2) assms(3) ex_in_conv uspecIsConsistent_def uspec_sercomp_not_empty)

(*   *)
lemma uspec_sercomp_consistent2: assumes "uspecIsConsistent (S1 \<circle> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
proof (rule)
  have f1: "uspecIsConsistent (Abs_rev_uspec {a \<circ> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2})"
    by (metis (no_types) assms(1) uspecSerComp_def)
  then have f2: "\<not> uspecWell {a \<circ> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<or> {a \<circ> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    by (metis (lifting) rep_abs_rev_simp uspecIsConsistent_def)
  then have f3: "{a \<circ> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    by (metis empty_uspecwell)
  then show "uspecIsConsistent S1"
    using uspecIsConsistent_def by force
  show "uspecIsConsistent S2"
    using f3 uspecIsConsistent_def by auto
qed

(*   *)
lemma uspec_sercomp_dom: assumes "uspec_sercompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecDom (S1 \<circle> S2) = uspecDom S1"
proof -
  obtain f1 and f2 where f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
    and  "(f1 \<circ> f2) \<in> Rep_rev_uspec (S1 \<circle> S2)"
    by (meson assms(1) assms(2) assms(3) some_in_eq uspecIsConsistent_def uspec_sercomp_not_empty)
  then show ?thesis
    using assms(1) f1_def f2_def ufuncl_sercomp_dom uspec_dom_eq uspec_sercompwell_def by blast
qed

(*   *)
lemma uspec_sercomp_ran: assumes "uspec_sercompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecRan (S1 \<circle> S2) = uspecRan S2"
proof -
  obtain f1 and f2 where f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
    and  "(f1 \<circ> f2) \<in> Rep_rev_uspec (S1 \<circle> S2)"
    by (meson assms(1) assms(2) assms(3) some_in_eq uspecIsConsistent_def uspec_sercomp_not_empty)
  then show ?thesis
    using assms(1) ufuncl_sercomp_ran uspec_ran_eq uspec_sercompwell_def by blast
qed

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_sercomp_ele_ex: assumes "uspec_sercompwell S1 S2"
and "uspecIsConsistent (S1 \<circle> S2)"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<circle> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = f1 \<circ> f2"
  using assms(1) uspec_sercomp_rep by fastforce

lemma uspec_sercomp_h1: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. f1 \<circ> f2 \<in> Rep_rev_uspec (S1 \<circle> S2)"
  by (simp add: assms uspec_sercomp_not_empty)

lemma uspec_sercomp_h2: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclSerCompWell f1 f2"
  using assms uspec_sercompwell_def by blast

(* sercomp of uspec is associative  *)
lemma uspec_sercomp_asso: assumes "uspec_sercompwell S1 S2" and "uspec_sercompwell S2 S3"
and "uspecDom S1 \<inter> uspecRan S3 = {}"
shows "((S1 \<circle> S2) \<circle> S3) = (S1 \<circle> (S2 \<circle> S3))"
proof -
  have f10: "{f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
              {f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<circle> S3)}"
    apply (rule subset_antisym)
     apply (rule subsetI)
  proof auto
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<Longrightarrow> f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<circle> S3)"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<circle> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" 
        and f1_eq_f3_f4: "f1 = f3 \<circ> f4"
        by (metis assms(1) empty_iff f1_def uspecIsConsistent_def uspec_sercomp_ele_ex)
      have f1: " f1 \<circ> f2 = f3 \<circ> (f4 \<circ> f2)"
        apply (subst f1_eq_f3_f4)
        by (metis assms(1) assms(2) assms(3) f2_def f3_def f4_def sercomp_asso uspec_dom_eq uspec_ran_eq uspec_sercompwell_def)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<circle> S3)"
        using assms(2) f2_def f3_def f4_def uspec_sercomp_h1 by blast
    qed
  next
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<Longrightarrow> f2 \<in> Rep_rev_uspec (S2 \<circle> S3) \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2a \<in> Rep_rev_uspec S3"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec (S2 \<circle> S3)"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" 
                    and f2_eq_f3_f4: "f2 = f3 \<circ> f4"
        using assms(2) f2_def uspec_sercomp_rep by blast
      have f1: "f1 \<circ> f2 = (f1 \<circ> f3) \<circ> f4"
        apply (subst f2_eq_f3_f4)
        by (metis assms(1) assms(2) assms(3) f1_def f3_def f4_def sercomp_asso uspec_dom_eq uspec_ran_eq uspec_sercompwell_def)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        using assms(1) f1_def f3_def f4_def uspec_sercomp_not_empty by blast
    qed
  qed
  then show ?thesis
    by (simp add: uspecSerComp_def)
qed

subsection \<open>UspecFeedbackComp\<close>

lemma uspec_feedbackcomp_well: "uspecWell {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)}"
  apply (simp add: uspecWell_def)
  apply (rule_tac x="uspecDom S1 - uspecRan S1" in exI)
  apply (rule_tac x="uspecRan S1" in exI)
  apply (rule, rule)
  by (metis ufuncl_feedbackcomp_dom ufuncl_feedbackcomp_ran uspec_dom_eq uspec_ran_eq)

lemma uspec_feedbackcomp_insert: "uspecFeedbackComp S = Abs_rev_uspec {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S)}"
  by (simp add: uspecFeedbackComp_def)

lemma uspec_feedbackcomp_consistent_iff: "uspecIsConsistent (uspecFeedbackComp S) = uspecIsConsistent S"
  apply (simp add: uspecIsConsistent_def uspecFeedbackComp_def)
  apply (subst rep_abs_rev_simp)
   apply (simp add: uspec_feedbackcomp_well)
  apply rule
  by simp+

lemma uspec_feecbackcomp_dom: assumes "uspecIsConsistent S"
  shows "uspecDom (uspecFeedbackComp S) = uspecDom S - uspecRan S"
proof -
  obtain f where f_def: "f \<in> {(\<mu>) a |a. a \<in> Rep_rev_uspec S}"
    using assms uspecIsConsistent_def by fastforce
  have f1: "\<exists>a. f = (\<mu>) a \<and> a \<in> Rep_rev_uspec S"
    using f_def by auto
  obtain a where a_def: "f = (\<mu>) a \<and> a \<in> Rep_rev_uspec S"
    using f1 by auto
  have f2: "ufclDom\<cdot>f = ufclDom\<cdot>a - ufclRan\<cdot>a"
    by (simp add: a_def ufuncl_feedbackcomp_dom)
  show ?thesis
    by (metis (mono_tags, lifting) a_def f2 f_def rep_abs_rev_simp uspecFeedbackComp_def uspec_dom_eq uspec_feedbackcomp_well uspec_ran_eq)
qed


lemma uspec_feecbackcomp_ran: assumes "uspecIsConsistent S"
  shows "uspecRan (uspecFeedbackComp S) = uspecRan S"
proof -
  obtain f where f_def: "f \<in> {(\<mu>) a |a. a \<in> Rep_rev_uspec S}"
    using assms uspecIsConsistent_def by fastforce
  have f1: "\<exists>a. f = (\<mu>) a \<and> a \<in> Rep_rev_uspec S"
    using f_def by auto
  obtain a where a_def: "f = (\<mu>) a \<and> a \<in> Rep_rev_uspec S"
    using f1 by auto
  have f2: "ufclRan\<cdot>f = ufclRan\<cdot>a"
    by (simp add: a_def ufuncl_feedbackcomp_ran)
  have f3: "ufclRan\<cdot>a = uspecRan S"
    by (simp add: a_def uspec_ran_eq)
  show ?thesis
    apply (fold f3, fold f2)
    by (metis (no_types) f_def rep_abs_rev_simp uspecFeedbackComp_def uspec_feedbackcomp_well 
        uspec_ran_eq)
qed

lemma uspec_feedbackcomp_f_ex: assumes "f \<in> Rep_rev_uspec (uspecFeedbackComp S)"
  shows "\<exists> f1 \<in> Rep_rev_uspec S. f = ufunclFeedbackComp f1"
proof -
  have "Rep_uspec (Abs_rev_uspec {(\<mu>) a |a. a \<in> Rep_rev_uspec S}) = Rev {(\<mu>) a |a. a \<in> Rep_rev_uspec S}"
using rep_abs_uspec uspec_feedbackcomp_well by auto
  then have "{(\<mu>) a |a. a \<in> Rep_rev_uspec S} = Rep_rev_uspec (uspecFeedbackComp S)"
    by (simp add: inv_rev_rev uspec_feedbackcomp_insert)
  then have "\<exists>a. f = (\<mu>) a \<and> a \<in> Rep_rev_uspec S"
    using assms by blast
  then show ?thesis
    by blast
qed

(* TODO Welche Theory und welche Section? *)

definition uspecLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" where
"uspecLeast cin cout = Abs_uspec (Rev {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout})"

lemma uspecLeast_well: "uspecWell {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout}"
  by(simp add: uspecWell_def)

lemma uspecLeast_contains_ufLeast: "ufunclLeast cin cout \<in> Rep_rev_uspec(uspecLeast cin cout)"
  apply(simp add: uspecLeast_def)
  apply(simp only: uspecLeast_well rep_abs_uspec)
  by (simp add: inv_rev_rev ufuncldom_least_dom ufuncldom_least_ran)

lemma uspecLeast_consistent: "uspecIsConsistent (uspecLeast cin cout)"
  using not_uspec_consisten_empty_eq uspecLeast_contains_ufLeast by auto

lemma uspecLeast_dom: "uspecDom (uspecLeast cin cout) = cin"
  by (metis (mono_tags, lifting) mem_Collect_eq rep_abs_rev_simp uspecLeast_consistent
      uspecLeast_contains_ufLeast uspecLeast_def uspecLeast_well uspec_dom_eq2)

lemma uspecLeast_ran: "uspecRan (uspecLeast cin cout) = cout"
  by (metis (mono_tags, lifting) CollectD rep_abs_rev_simp uspecLeast_contains_ufLeast
      uspecLeast_def uspecLeast_well uspec_ran_eq)

lemma uspecLeast_min: assumes "uspecDom S = In"
                            and "uspecRan S = Out"
                          shows "uspecLeast In Out \<sqsubseteq> S"
  proof -
    have "\<And>f. f \<in> (Rep_rev_uspec S) \<Longrightarrow> ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out"
      by (simp add: assms(1) assms(2) uspec_dom_eq uspec_ran_eq)
    moreover have "\<And>f. ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out \<Longrightarrow> f \<in> Rep_rev_uspec (uspecLeast In Out)"
      by (metis (mono_tags, lifting) CollectI rep_abs_rev_simp uspecLeast_def uspecLeast_well)
    ultimately have "\<And>f. f \<in> (Rep_rev_uspec S) \<Longrightarrow> f \<in> Rep_rev_uspec (uspecLeast In Out)"
      by auto
    then have "Rep_rev_uspec S \<subseteq> Rep_rev_uspec (uspecLeast In Out)"
      by(simp add: subsetI)
    then show ?thesis
      by (simp add: SetPcpo.less_set_def uspec_belowI)
  qed

lemma uspecLeast_min2: "(uspecLeast (uspecDom S) (uspecRan S)) \<sqsubseteq> S"
  using uspecLeast_min by auto

end
