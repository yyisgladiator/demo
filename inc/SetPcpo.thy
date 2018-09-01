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


inductive setSize_helper :: "'a set \<Rightarrow> lnat \<Rightarrow> bool"
  where
    "setSize_helper {} (Fin 0)"
  |  "setSize_helper A (Fin X) \<and> a \<notin> A \<Longrightarrow> setSize_helper (insert a A) (Fin (Suc X))"

definition setSize :: "'a set \<Rightarrow> lnat"
  where
  "setSize X \<equiv> if (finite X) then (THE Y. setSize_helper X Y) else \<infinity>"
                           
end