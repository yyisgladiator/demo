theory USpec_Comp
  imports USpec
begin

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp

definition uspec_compwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_compwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclCompWell f1 f2"

definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> Abs_uspec (Rev {f1 \<otimes> f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)})"

definition uspec_sercompwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_sercompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclSerCompWell f1 f2"

definition uspecSerComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv> Abs_rev_uspec {f1 \<circ> f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

definition uspec_parcompwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_parcompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclParCompWell f1 f2"  

definition uspecParComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv> Abs_rev_uspec {f1 \<parallel> f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

definition uspecFeedbackComp :: "'m uspec \<Rightarrow> 'm uspec" where
"uspecFeedbackComp S1 \<equiv> Abs_rev_uspec {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)}"



(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

lemma uspec_compwell_commu: "uspec_compwell S1 S2 =  uspec_compwell S2 S1"
  using ufunclCompWell_commute uspec_compwell_def by blast

lemma uspec_parcompwell_commu: "uspec_parcompwell S1 S2 = uspec_parcompwell S2 S1"
  using ufunclParCompWell_commute uspec_parcompwell_def by blast


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

end
