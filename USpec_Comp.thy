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
  sorry

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

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_parcomp_ele_ex: assumes "uspec_parcompwell S1 S2"
and "uspecIsConsistent (S1 \<parallel> S2)"
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


(* helper to prove that new component after composition of 3 components is uspecwell  *)
lemma uspec_sercompwell_asso_h: assumes "uspec_sercompwell S1 S2"
and "uspec_sercompwell S2 S3"
and "uspecDom S1 \<inter> uspecRan S3 = {}"
shows "uspec_sercompwell S1 (S2 \<circle> S3) \<and> uspec_sercompwell (S1 \<circle> S2) S3"
  apply auto
   apply (simp_all add: uspec_sercompwell_def, auto)
   apply (metis (no_types, lifting) assms(1) assms(2) assms(3) empty_iff sercompwell_asso uspecIsConsistent_def uspec_dom_eq uspec_ran_eq uspec_sercomp_ele_ex uspec_sercompwell_def) +
  done

(* the new component is uspecwell  *) 
lemma uspec_sercompwell_asso: assumes "uspec_sercompwell S1 S2"
and "uspec_sercompwell S2 S3"
and "uspecDom S1 \<inter> uspecRan S3 = {}"
shows "uspecWell  {f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<circle> S3)}"
  by (simp add: assms(1) assms(2) assms(3) uspec_sercompwell_asso_h) 


end
