(*  Title:  Reversed
    Author: Sebastian Stüber
    e-mail: sebastian.stueber@rwth-aachen.de

    Description: "'a rev" datatype. Takes an cpo an inverts the order.
*)


theory Reversed
  imports "~~/src/HOL/HOLCF/HOLCF"
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

datatype 'a rev = Rev 'a

(* rev simply reverses the order of the original type *)
instantiation rev :: (po) po
begin
  fun below_rev:: "'a rev \<Rightarrow> 'a rev \<Rightarrow> bool" where
  "below_rev (Rev b1) (Rev b2) = (b2\<sqsubseteq>b1)"

  (* Show that the ordering definition defines a correct partial order. *)
  instance
    apply intro_classes
    using below_rev.elims(3) apply fastforce
    apply (metis Reversed.below_rev.elims(3) below_rev.elims(2) below_trans rev.inject)
    by (metis below_rev.elims(2) po_eq_conv rev.inject)
end

declare [[show_types]]
declare [[show_consts]]
class revcpo = po +
  assumes revlub_ex: "\<And>S::(nat \<Rightarrow> 'a::po). chain (\<lambda>i. Rev (S i)) 
                                        \<Longrightarrow> \<exists>x. range (\<lambda>i. Rev (S i)) <<| (Rev x)"
  (* Yes, naming this assumption is crucial :D *)
begin
end

class uprevcpo = revcpo + upcpo

instantiation rev :: (revcpo) cpo
begin
lemma rev_bot_top: "x\<sqsubseteq>(Rev \<bottom>)"
  using below_rev.elims(3) by blast

instance
  proof intro_classes
    fix S :: "nat \<Rightarrow> 'a::revcpo rev"
    assume as: "chain S"
    have "\<And>i. \<exists>x. (S i) = Rev x"
      by (meson rev.exhaust)
    hence h1: "\<exists>Y . (\<forall> i. Rev (Y i) = (S i))" by metis
    obtain Y :: "nat \<Rightarrow> 'a::revcpo" where y_def: "\<And>i. Rev (Y i) = (S i)" using h1 by blast
    have "chain (\<lambda>i. Rev (Y i))"
      by (metis Rep_rev_inverse as po_class.chain_def y_def)
    hence "\<exists>x. range (\<lambda>i. Rev (Y i)) <<| (Rev x)"
      using revlub_ex by blast
    thus "\<exists>x. range S <<| x"
      by (metis Rep_rev_inverse image_cong y_def)
  qed
end

instance rev :: (uprevcpo) pcpo
  apply(intro_classes)
  by (metis below_rev.simps rev.exhaust top)


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

(*
instance rev :: (pcpo) upcpo
  apply intro_classes
  by (metis Abs_rev_inverse below_rev.elims(3) mem_Collect_eq minimal)

instance rev :: (dpcpo) dpcpo
  apply intro_classes
  by (metis Abs_rev_inverse below_rev.elims(1) maximal mem_Collect_eq)
*)

lemma inv_rev_rev[simp]: "inv Rev (Rev S) = S"
  by (meson f_inv_into_f rangeI rev.inject)
    
lemma rev_inv_rev[simp]: "Rev (inv Rev S) = S"
  by (meson rev.exhaust surj_def surj_f_inv_f)
    
lemma Lub_rev_inv_rev:"(Rev (inv Rev (\<Squnion>i. Y i))) = (\<Squnion>i. (Rev (inv Rev (Y i))))"
  by (metis image_cong rev_inv_rev)
    
lemma rev_chainI:assumes"\<And>i. Y (Suc i)\<sqsubseteq> Y i" shows "chain (\<lambda>i. Rev (Y i))"
  by(simp add: assms chainI)

lemma rev_monoI:"\<lbrakk>\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f y \<sqsubseteq> f x\<rbrakk>\<Longrightarrow> monofun (\<lambda>x. Rev (f x))"
  by(simp add: monofunI)
              
end