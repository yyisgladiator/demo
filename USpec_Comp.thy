theory USpec_Comp
  imports USpec
begin


(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp

  (* composite operator on SPS *)
(* THIS IS JUST A DEMO! there should be many changes *)
definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> Abs_uspec (Rev {ufunclComp\<cdot>f1\<cdot>f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)})"

definition uspecSerComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv> Abs_rev_uspec {ufunclSerComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

definition uspecParComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv> Abs_rev_uspec {ufunclParComp\<cdot>f1\<cdot>f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)}"

definition uspecFeedbackComp :: "'m uspec \<Rightarrow> 'm uspec" where
"uspecFeedbackComp S1 \<equiv> Abs_rev_uspec {ufunclFeedbackComp\<cdot>f1 | f1.  f1\<in>(Rep_rev_uspec S1)}"



(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   



end
