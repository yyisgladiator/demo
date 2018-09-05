chapter {* Set and bool as a pointed cpo. *}

theory SetPcpo
imports HOLCF Reversed LNat
begin

text {*PCPO on sets and bools. The @{text "\<sqsubseteq>"} operator of the order is defined as the @{text "\<subseteq>"} operator on sets
  and as @{text "\<longrightarrow>"} on booleans.
*}

(* ----------------------------------------------------------------------- *)
section {* Order on sets. *}
(* ----------------------------------------------------------------------- *)

text {* {text "\<sqsubseteq>"} operator as the @{text "\<subseteq>"} operator on sets -> partial order. *}
instantiation set :: (type) po
begin
  definition less_set_def: "(\<sqsubseteq>) = (\<subseteq>)"
instance
apply intro_classes
apply (simp add: less_set_def)
apply (simp add: less_set_def)
apply (simp add: less_set_def)
done
end

text {* The least upper bound on sets corresponds to the @{text "Union"} operator. *}
lemma Union_is_lub: "A <<| \<Union>A"
apply (simp add: is_lub_def)
apply (simp add: is_ub_def)
apply (simp add: less_set_def Union_upper)
apply (simp add: Sup_least)
done

text {* Another needed variant of the fact that lub on sets corresponds to union. *}
lemma lub_eq_Union: "lub = Union"
apply (rule ext)
apply (rule lub_eqI [OF Union_is_lub])
done

text {* The partial order on sets is complete. *}
instance set :: (type) cpo
apply intro_classes
using Union_is_lub 
apply auto
done

text {* Sets are also pcpo`s, pointed with @{text "{}"} as minimal element. *}
instance set :: (type) pcpo
apply intro_classes
apply (rule_tac x= "{}" in exI)
apply (simp add: less_set_def)
done

text {* For sets, the minimal element is the empty set.*}
lemma UU_eq_empty: "\<bottom> = {}"
apply (simp add: less_set_def bottomI)
done

text {* We group the following lemmas in order to simplify future proofs. *}
lemmas set_cpo_simps = less_set_def lub_eq_Union UU_eq_empty

(* ----------------------------------------------------------------------- *)
section {* Order on booleans. *}
(* ----------------------------------------------------------------------- *)

text {* If one defines the @{text "\<sqsubseteq>"} operator as the @{text "\<longrightarrow>"} operator on booleans,
  one obtains a partial order. *}
instantiation bool :: po
begin
  definition less_bool_def: "(\<sqsubseteq>) = (\<longrightarrow>)"
instance
apply intro_classes
apply (simp add: less_bool_def)
apply (simp add: less_bool_def)
apply (simp add: less_bool_def)
apply (simp add: less_bool_def)
apply auto
done
end

text {* Chains of bools are always finite. This is needed to prove that bool is a cpo. *}
instance bool :: chfin
proof
  fix S:: "nat \<Rightarrow> bool"
  assume S: "chain S"
  then have "finite (range S)" 
  apply simp
  done
  from S and this 
  have "finite_chain S" 
  apply (rule finite_range_imp_finch)
  done
  thus "\<exists> n. max_in_chain n S" 
  apply (unfold finite_chain_def, simp)
  done
qed

text {* The partial order on bools is complete. *}
instance bool :: cpo ..

text {* Bools are also pointed with @{text "False"} as minimal element. *}
instance bool :: pcpo
proof
  have "\<forall>y::bool. False \<sqsubseteq> y" 
  unfolding less_bool_def 
  apply simp
  done
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed

(* ----------------------------------------------------------------------- *)
section {* Properties *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* Admissibility of set predicates *}
(* ----------------------------------------------------------------------- *)

text {* The predicate "\<lambda>A. \<exists>x. x \<in> A" is admissible. *}
lemma adm_nonempty: "adm (\<lambda>A. \<exists>x. x \<in> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
apply force
done

text {* The predicate "\<lambda>A. x \<in> A" is admissible. *}
lemma adm_in: "adm (\<lambda>A. x \<in> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
done

text {* The predicate "\<lambda>A. x \<notin> A" is admissible. *}
lemma adm_not_in: "adm (\<lambda>A. x \<notin> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
done

text {* If for all x the predicate "\<lambda>A. P A x" is admissible, then so is "\<lambda>A. \<forall>x\<in>A. P A x". *}
lemma adm_Ball: "(\<And>x. adm (\<lambda>A. P A x)) \<Longrightarrow> adm (\<lambda>A. \<forall>x\<in>A. P A x)"
apply (simp add: Ball_def)
apply (simp add: adm_not_in)
done

text {* The predicate "\<lambda>A. Bex A P", which means "\<lambda>A. \<exists>x. x \<in> A \<and> P x" is admissible. *}
lemma adm_Bex: "adm (\<lambda>A. Bex A P)"
apply (rule admI)
apply (simp add: lub_eq_Union)
done

text {* The predicate "\<lambda>A. A \<subseteq> B" is admissible. *}
lemma adm_subset: "adm (\<lambda>A. A \<subseteq> B)"
apply (rule admI)
apply (simp add: lub_eq_Union)
apply auto
done

text {* The predicate "\<lambda>A. B \<subseteq> A" is admissible. *}
lemma adm_superset: "adm (\<lambda>A. B \<subseteq> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
apply auto
done

text {* We group the following lemmas in order to simplify future proofs. *}
lemmas adm_set_lemmas = adm_nonempty adm_in adm_not_in adm_Bex adm_Ball adm_subset adm_superset

(* ----------------------------------------------------------------------- *)
subsection {* Compactness *}
(* ----------------------------------------------------------------------- *)

text {* The bottom element of the set cpo ist compact. *}
lemma compact_empty: "compact {}"
apply (fold UU_eq_empty)
apply simp
done

text {* Induction step for compact sets: 
If a set is compact and we insert an element into it, then the compactness is preserved. *}
lemma compact_insert: "compact A \<Longrightarrow> compact (insert x A)"
apply (simp add: compact_def)
apply (simp add: set_cpo_simps)
apply (simp add: adm_set_lemmas)
done

text {* The compactness of finite sets is proven by induction from the lemma above. *}
lemma finite_imp_compact: "finite A \<Longrightarrow> compact A"
apply (induct A set: finite)
apply (rule compact_empty)
apply (erule compact_insert)
done

lemma union_cont:"cont (\<lambda>S2. union S1 S2)"
  apply(rule contI)
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union 
  by (metis (no_types, lifting) UN_simps(3) Union_is_lub empty_not_UNIV lub_eq lub_eqI)


inductive setSize_helper :: "'a set \<Rightarrow> nat \<Rightarrow> bool"
  where
    "setSize_helper {} 0"
  |  "setSize_helper A X \<and> a \<notin> A \<Longrightarrow> setSize_helper (insert a A) (Suc X)"

definition setSize :: "'a set \<Rightarrow> lnat"
  where
  "setSize X \<equiv> if (finite X) then Fin (THE Y. setSize_helper X Y) else \<infinity>"


lemma setSizeEx: assumes "finite X" shows "\<exists> Y. setSize_helper X Y"
  apply (rule finite_induct)
  apply (simp add: assms)
  using setSize_helper.intros(1) apply auto[1]
  by (metis setSize_helper.simps)

lemma setSize_remove: "y \<in> F \<and> setSize_helper (F - {y}) A \<longrightarrow> setSize_helper F (Suc A)"
  by (metis Diff_insert_absorb Set.set_insert setSize_helper.intros(2))


lemma setSizeBack_helper:  
  assumes "\<forall>(F::'a set) x::'a. (finite F \<and> setSize_helper (insert x F) (Suc A) \<and> x \<notin> F) \<longrightarrow> setSize_helper F A"
  shows "\<forall>(F::'a set) x::'a. (finite F \<and> setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F) \<longrightarrow> setSize_helper F (Suc A)"
proof -
have b0: "\<And>A::nat. \<forall>(F::'a set) x::'a. ((setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F) 
  \<longrightarrow> (\<exists> y. y \<in> (insert x F) \<and> setSize_helper ((insert x F) - {y}) (Suc A)))"
    by (metis Diff_insert_absorb add_diff_cancel_left' insertI1 insert_not_empty plus_1_eq_Suc setSize_helper.simps)
have b1: "\<forall>(F::'a set) (x::'a) y::'a. ((finite F \<and> setSize_helper (insert x (F - {y})) (Suc A) \<and> x \<notin> F)
  \<longrightarrow> setSize_helper (F - {y}) A)"
  using assms by auto
have b2: "\<forall>(F::'a set) x::'a. (setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F) 
  \<longrightarrow> ((\<exists> y. (y\<noteq>x \<and> y \<in> F \<and> setSize_helper (insert x (F - {y})) (Suc A))) \<or> setSize_helper F (Suc A))"
  by (metis Diff_insert_absorb b0 empty_iff insert_Diff_if insert_iff)
have b3: "\<forall>(F::'a set) x::'a. (setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F \<and> finite F) 
  \<longrightarrow> ((\<exists> y. (y\<noteq>x \<and> y \<in> F \<and> setSize_helper (F - {y}) A)) \<or> setSize_helper F (Suc A))"
  by (meson b1 b2)
show "\<forall>(F::'a set) x::'a. (finite F \<and> setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F) \<longrightarrow> setSize_helper F (Suc A)"
  by (meson b3 setSize_remove)
qed


lemma setSizeBack: "\<And> F x. (finite F \<and> setSize_helper (insert x F) (Suc A) \<and> x \<notin> F) \<Longrightarrow> setSize_helper F A"
  apply (induction A)
  apply (metis Suc_inject empty_iff insertI1 insert_eq_iff nat.distinct(1) setSize_helper.simps)
  using setSizeBack_helper by blast


lemma setSizeonlyOne: assumes "finite X" shows "\<exists>! Y. setSize_helper X Y"
  apply (rule finite_induct)
  apply (simp add: assms)
  apply (metis empty_not_insert setSize_helper.simps)
  by (metis insert_not_empty setSizeBack setSize_helper.intros(2) setSize_helper.simps)

lemma setSizeSuc: assumes "finite X" and "z \<notin> X" shows "setSize (insert z X) = lnsuc\<cdot>(setSize X)"
  apply (simp add: setSize_def)
  using assms setSizeonlyOne
  by (metis (mono_tags, lifting) Diff_insert_absorb finite.insertI insertI1 setSize_remove theI_unique)

lemma setSizeEmpty: "setSize {} = Fin 0"
  by (metis finite.emptyI setSize_def setSize_helper.intros(1) setSizeonlyOne theI_unique)

lemma setSizeSingleton: "setSize {x} = lnsuc\<cdot>(Fin 0)"
  by (simp add: setSizeEmpty setSizeSuc)

lemma setsize_union_helper1: 
  assumes "finite F"
      and "x \<notin> F"
      and "x \<notin> X"
    shows "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F \<Longrightarrow>
       setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
proof - 
  assume a0: "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F"
  have b0: "X \<union> insert x F = insert x (X \<union> F)"
    by simp
  have b1: "setSize (X \<union> insert x F) = lnsuc\<cdot>(setSize (X \<union> F))"
    by (metis Un_iff Un_infinite assms(1) assms(2) assms(3) b0 finite_UnI fold_inf setSizeSuc setSize_def sup_commute)
  have b2: "setSize (X \<inter> insert x F) = setSize (X \<inter> F)"
    by (simp add: assms(3)) 
  show "setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
    by (metis (no_types, lifting) a0 ab_semigroup_add_class.add_ac(1) add.commute assms(1) assms(2) 
      b1 b2 lnat_plus_suc setSizeSuc)
qed

lemma setsize_union_helper2: 
  assumes "finite F"
      and "x \<notin> F"
      and "x \<in> X"
    shows "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F \<Longrightarrow>
       setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
proof -
  assume a0: "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F"
  have b0: "setSize (X \<union> insert x F) = setSize (X \<union> F)"
    by (metis Un_Diff_cancel assms(3) insert_Diff1)
  have b1: "setSize (X \<inter> insert x F) =  lnsuc\<cdot>(setSize (X \<inter> F))"
    by (simp add: assms(1) assms(2) assms(3) setSizeSuc)
  show "setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
    by (metis a0 ab_semigroup_add_class.add_ac(1) assms(1) assms(2) b0 b1 lnat_plus_suc setSizeSuc)
qed

lemma setsize_union_helper3: assumes "finite X" and "finite Y"
  shows "setSize (X \<union> Y) + setSize (X \<inter> Y) = setSize X + setSize Y"
  apply (rule finite_induct)
  apply (simp add: assms)
  apply simp
  by (meson setsize_union_helper1 setsize_union_helper2)

lemma setsize_union_helper4: assumes "infinite X \<or> infinite Y"
  shows "setSize (X \<union> Y) + setSize (X \<inter> Y) = setSize X + setSize Y"
proof -
  have b0: "setSize (X \<union> Y) = \<infinity>"
    by (metis (full_types) assms infinite_Un setSize_def)
  have b1: "setSize X = \<infinity> \<or> setSize Y = \<infinity>"
    by (meson assms setSize_def)
  show ?thesis
    using b0 b1 plus_lnatInf_r by auto
qed

lemma setsize_union: "setSize (X \<union> Y) + setSize (X \<inter> Y) = setSize X + setSize Y"
  by (meson setsize_union_helper3 setsize_union_helper4)


end