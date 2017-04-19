chapter {* Set with \<supseteq> as a pointed cpo. *}

theory SetPcpo2
imports Adm 
begin

text {*PCPO on sets and bools. The @{text "\<sqsubseteq>"} operator of the order is defined as the @{text "\<supseteq>"} operator on sets
  and as @{text "\<longrightarrow>"} on booleans.
*}

(* ----------------------------------------------------------------------- *)
section {* Order on sets. *}
(* ----------------------------------------------------------------------- *)

text {* {text "\<sqsubseteq>"} operator as the @{text "\<supseteq>"} operator on sets -> partial order. *}
instantiation set :: (type) po
begin
  definition less_set_def: "(op \<sqsubseteq>) = (op \<supseteq>)"
instance
apply intro_classes
apply (simp add: less_set_def)
apply (simp add: less_set_def)
apply (simp add: less_set_def)
done
end

text {* The least upper bound on sets corresponds to the @{text "Intersection"} operator. *}
lemma Inter_is_lub: "A <<| \<Inter>A"
apply (simp add: is_lub_def)
apply (simp add: is_ub_def)
apply (simp add: less_set_def Union_upper)
apply (simp add: Inter_greatest Inter_lower)
done

text {* Another needed variant of the fact that lub on sets corresponds to intersection. *}
lemma lub_eq_Inter: "lub = Inter"
apply (rule ext)
apply (rule lub_eqI [OF Inter_is_lub])
done

text {* The partial order on sets is complete. *}
instance set :: (type) cpo
apply intro_classes
using Inter_is_lub 
apply auto
done

text {* Sets are also pcpo`s, pointed with @{text "UNIV"} as minimal element. *}
instance set :: (type) pcpo
apply intro_classes
apply (rule_tac x= "UNIV" in exI)
apply (simp add: less_set_def)
done

text {* For sets, the minimal element is the empty set.*}
lemma UU_eq_empty: "\<bottom> = UNIV"
apply (simp add: less_set_def bottomI)
done

text {* We group the following lemmas in order to simplify future proofs. *}
lemmas set_cpo_simps = less_set_def lub_eq_Inter UU_eq_empty



end
