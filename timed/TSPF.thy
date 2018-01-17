(*  Title:        TSPFTheorie.thy
    Author:       Sebastian Stüber
    Author:       Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
    e-mail:       jens.buerger@rwth-aachen.de

    Description:
*)



theory TSPF
imports TSB "../UFun" "../UFun_Comp"
begin

default_sort message


(* Concept of causality
(* ----------------------------------------------------------------------- *)
 section \<open>Definition on TSPF\<close>
(* ----------------------------------------------------------------------- *)

subsubsection \<open>causality\<close>
(* tspf_weakCausality defines equality of the input up to time n to imply equality of the output
   up to time n *)
(*offen*)
(*
text {* the weak causality prefix, from FOCUS *}
definition tspf_weakCausality :: "(('m tstream\<^sup>\<Omega> \<rightarrow> 'm tstream\<^sup>\<Omega>) option) \<Rightarrow> bool" where
"tspf_weakCausality f \<equiv> (\<forall> (n ::nat). \<forall> b1 \<in> dom (Rep_cfun f) . \<forall> b2 \<in> dom (Rep_cfun f) . 
                    (((#\<surd>tsb b1) = \<infinity>) \<and> ((#\<surd>tsb b2) = \<infinity>)) \<longrightarrow> 
                    (tsbTTake n\<cdot>b1 = tsbTTake n\<cdot>b2) \<longrightarrow>
                    (tsbTTake n\<cdot>(the (f\<cdot>b1)) = tsbTTake n\<cdot>(the (f\<cdot>b2))) )"


text {* the strong causality prefix, from FOCUS *}
definition tspf_strongCausality :: "(('m tstream\<^sup>\<Omega> \<rightarrow> 'm tstream\<^sup>\<Omega>) option) \<Rightarrow> bool" where
"tspf_strongCausality f \<equiv> (\<forall> (n ::nat). \<forall> b1 \<in> dom (Rep_cfun f) . \<forall> b2 \<in> dom (Rep_cfun f) . 
                          (((#\<surd>tsb b1) = \<infinity>) \<and> ((#\<surd>tsb b2) = \<infinity>)) \<longrightarrow> 
                          (tsbTTake n\<cdot>b1 = tsbTTake n\<cdot>b2) \<longrightarrow>
                          (tsbTTake (Suc n)\<cdot>(the (f\<cdot>b1)) = tsbTTake (Suc n)\<cdot>(the (f\<cdot>b2))) )"
*)
(*
text {* For legacy purposes ONLY use @{thm tspfCompL_def} *}
definition tspfComp_pL :: "(('m tstream\<^sup>\<Omega>, 'm tstream\<^sup>\<Omega>) ufun) \<Rightarrow> (('m tstream\<^sup>\<Omega>, 'm tstream\<^sup>\<Omega>) ufun) \<Rightarrow> channel set" where
"tspfComp_pL f1 f2 \<equiv> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1) \<union> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f1)
                      \<union> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2) \<union> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2)"
*)



(*offen*)(*tick*)
(*
text{* If an TSPF is applied to an input x, the output has more ticks *}
lemma tspf_less_in_than_out_ticks: assumes "x \<in> dom (Rep_cufun f)"
  shows "#\<surd>tsb x \<le> #\<surd>tsb (f \<rightleftharpoons> x)"
  using assms rep_tspf_well tspf_well_def by blast
*)

(*offen*)(*tick in weakCausality*)
(*
  subsection \<open>tspfwell\<close>
  
text {* If f is tspf_well it also is weak causal *}
lemma tspfwell_to_weak: assumes "tspf_well f"
  shows "tspf_weakCausality f"
proof -
  have f1: "monofun (Rep_cfun f)"
    by (simp add: monofun_Rep_cfun2)
  have f2: "\<And> b. (b \<in> dom (Rep_cfun f)) \<longrightarrow> #\<surd>tsb b \<le> (#\<surd>tsb (the ((Rep_cfun f) b)))"
    using assms tspf_well_def by blast
  show ?thesis
    apply (simp add: tspf_weakCausality_def)
    using f1 f2 tspf_is_weak by blast
qed   
*)

(*offen aber comp_pl for legacy only*)
(*
text{* pL channels are a subset of internal channels *}
lemma tspfcomp_pl_subset_L [simp]: "(tspfComp_pL f1 f2) = (tspfCompL f1 f2)"
  using tspfComp_pL_def tspfCompL_def by blast

text{* pL channels are a subset of all channels *}    
lemma tspfcomp_pL_subset_C [simp]: "(tspfComp_pL f1 f2) \<subseteq> (tspfCompC f1 f2)"
  using tspfComp_pL_def tspfCompC_def by blast
*)

(*offen*)(*tick*)
(*
text{* the composition is tspfwell if the tick requirement from tspf_well is fulfilled *}
lemma tspfcomp_wellI [simp]: 
  assumes "\<And>b. tsbDom\<cdot>b = tspfCompI f1 f2 \<Longrightarrow> 
                      #\<surd>tsb b  \<le> #\<surd>tsb tsbFix (tspfCompH f1 f2 b) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"
  shows "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = (tspfCompI f1 f2)) 
                \<leadsto> tsbFix (tspfCompH f1 f2 x) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2))"
  apply (rule tspf_wellI)
     apply (simp_all add: domIff2 tsbfix_dom)
     by (simp add: assms(1))
*)
(*offen*)(*tick*)
(*
text{* if the fixed point has length \<infinity> the tspf is always well *}
lemma tspfcomp_well_empty_in [simp]: 
  assumes "\<And>b. #\<surd>tsb tsbFix (tspfCompH f1 f2 b) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) = \<infinity>"
  shows "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = (tspfCompI f1 f2)) 
                \<leadsto> tsbFix (tspfCompH f1 f2 x) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2))"
  apply (rule tspfcomp_wellI)
  by (simp add: assms(1))
*)
    (*offen*)
(*
section\<open>Empty component\<close>
  
lift_definition tspfEmptyComponent :: "'m TSPF"  is
"(\<Lambda> x. (tsbDom\<cdot>x = {} ) \<leadsto> (empty \<Omega>))"
proof - 
  have f0: "\<forall>tb. tsbDom\<cdot>(tb :: 'm TSB) = {} \<longrightarrow> Rep_TSB tb = empty"
    by (simp add: tsbdom_insert)
  then have f1: "dom (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> (empty \<Omega>)) = {(empty \<Omega>)}"
    apply(simp add: dom_def)
    by (smt Collect_cong bot_empty_eq bot_set_def dom_empty empty_iff insert_Collect tsb_eq tsb_well_exists tsbdom_rep_eq)
  moreover have f2: "{a::'a TSB. tsbDom\<cdot>a = {}} = {empty \<Omega>}"
    by (smt Abs_cfun_inverse2 Collect_cong bot_apply bot_set_def dom_empty insert_Collect insert_not_empty mem_Collect_eq tsbDom_def tsb_eq tsb_well_exists tsbdom_cont tsbdom_rep_eq)
  moreover have f3: "dom (Rep_cfun (\<Lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> (empty \<Omega>))) = {(empty \<Omega>)}"
    apply(simp add: dom_def)
    using f2 by auto
  ultimately show ?thesis  
    apply(simp add: tspf_well_def)
    apply rule
    apply (auto simp add: tspf_type_def domIff2 tsbdom_rep_eq)
    apply(simp add: tsbTickCount_def)
      by blast
qed  
  *)
*)

end