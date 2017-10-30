(*  Title:  Reversed
    Author: Sebastian Stüber
    e-mail: sebastian.stueber@rwth-aachen.de

    Description: "'a rev" datatype. Takes an cpo an inverts the order.
*)


theory Reversed
  imports HOLCF
    
begin
default_sort type


section \<open>Class Definitions \<close>
(* The new class definitions are later used for the 'rev' type *)


(* upper pointed cpo *)
class upcpo = cpo +
  assumes top: "\<exists>x. \<forall>y. y \<sqsubseteq> x"
begin
  
  definition top :: "'a"  ("\<top>")
    where "top = (THE x. \<forall>y. y \<sqsubseteq> x)"
  
  lemma maximal [iff]: "x\<sqsubseteq>\<top>"
    unfolding top_def
    apply (rule the1I2)
    apply (rule ex_ex1I)
    apply (rule top)
    apply (blast intro: below_antisym)
    apply simp
    done
end


(* double pointed cpo *)
class dpcpo = pcpo + upcpo


section \<open>rev type\<close>

typedef 'a rev = "{a::'a. True}"
  by simp

(* rev simply reverses the order of the original type *)
instantiation rev :: (po) po
begin
  fun below_rev:: "'a rev \<Rightarrow> 'a rev \<Rightarrow> bool" where
  "below_rev b1 b2 = ((Rep_rev b2)\<sqsubseteq>(Rep_rev b1))"

  (* Show that the ordering definition defines a correct partial order. *)
  instance
    apply intro_classes
    apply simp
    using rev_below_trans apply auto[1]
    using Rep_rev_inject below_antisym by auto 
end

declare [[show_types]]
declare [[show_consts]]
class revcpo = po +
  assumes "\<And>S::(nat \<Rightarrow> 'a::po). chain (\<lambda>i. Abs_rev (S i)) \<Longrightarrow> \<exists>x. range (\<lambda>i. Abs_rev (S i)) <<| (Abs_rev x)"
begin
lemma rev_lubex:
  fixes S::"(nat \<Rightarrow> 'a::po)"
  assumes "chain (\<lambda>i. Abs_rev (S i))"
  shows "\<exists>x. range (\<lambda>i. Abs_rev (S i)) <<| (Abs_rev x)"
  sorry

end

instantiation rev :: (revcpo) cpo
begin
lemma rev_bot_top: "x\<sqsubseteq>(Abs_rev \<bottom>)"
  by (simp add: Abs_rev_inverse)

  instance
  proof intro_classes
    fix S :: "nat \<Rightarrow> 'a::revcpo rev"
    assume as: "chain S"
    obtain Y :: "nat \<Rightarrow> 'a::revcpo" where y_def: "\<And>i. Y i = Rep_rev (S i)" by simp
    have "chain (\<lambda>i. Abs_rev (Y i))"
      by (metis Rep_rev_inverse as po_class.chain_def y_def)
    hence "\<exists>x. range (\<lambda>i. Abs_rev (Y i)) <<| (Abs_rev x)"
      using rev_lubex by blast
    thus "\<exists>x. range S <<| x"
      by (metis Rep_rev_inverse image_cong y_def)
  qed
end


(* SWS: I am not 100% sure this is true... *)
(* If not, create a new class so that is works *)
(* Update: 100% sure this does not work. New class is revcpo *)
(*instantiation rev :: (pcpo) cpo
begin
lemma rev_bot_top: "x\<sqsubseteq>(Abs_rev \<bottom>)"
  by (simp add: Abs_rev_inverse)

instance
  apply intro_classes
  
  apply( simp add: is_lub_def)
  apply (rule+)
   apply(rule ccontr)
  unfolding is_ub_def
  apply auto[2]

  sorry
end *)

instance rev :: (pcpo) upcpo
  apply intro_classes
  by (metis Abs_rev_inverse below_rev.elims(3) mem_Collect_eq minimal)

instance rev :: (dpcpo) dpcpo
  apply intro_classes
  by (metis Abs_rev_inverse below_rev.elims(1) maximal mem_Collect_eq)





end