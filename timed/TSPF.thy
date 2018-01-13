(*  Title:        TSPFTheorie.thy
    Author:       Sebastian Stüber
    Author:       Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
    e-mail:       jens.buerger@rwth-aachen.de

    Description:
*)

(*

theory TSPF
imports TSB "../UFun" "../UFun_Comp"
begin

default_sort message


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)


(* normal wellformed definition, similar to SPF *)
(* an 'm TSPF has a fixed input-channel-set and output-set.  *)
(*definition tspf_type:: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_type f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> tsbDom\<cdot>b = In) \<and>
                            (b \<in> dom (Rep_cfun f) \<longrightarrow> tsbDom\<cdot>(the (f\<cdot>b)) = Out)"*)
(*
  (* Proof admissibility on the first part of spf_wellformed *)
  lemma tspf_type_adm1[simp]: "adm (\<lambda>f. \<exists>In. \<forall>b. (b \<in> dom f) = (tsbDom\<cdot>b = In))"
  by (smt adm_upward below_cfun_def part_dom_eq)

    (* Proof admissibility on the second part of spf_wellformed *)
  lemma tspf_type_adm2[simp]: "adm (\<lambda>f. \<exists>Out. \<forall>b. b \<in> dom f \<longrightarrow> tsbDom\<cdot>(f\<rightharpoonup>b) = Out)"
  apply(rule admI)
    by (metis part_the_chain part_the_lub tsbChain_dom_eq2 part_dom_lub)
*)
(*
lemma tspf_type_adm1 [simp]: "adm (\<lambda>f. \<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f)) = (ubDom\<cdot>b = In)) "
  by (smt adm_upward below_cfun_def part_dom_eq)

lemma tspf_type_adm2 [simp]: "adm (\<lambda> f. \<exists>Out. \<forall>b. b \<in> dom (Rep_cfun f) \<longrightarrow> ubDom\<cdot>Rep_cfun f\<rightharpoonup>b = Out)"
  apply (rule admI)
  by (smt below_cfun_def ch2ch_Rep_cfunL contlub_cfun_fun op_the_chain op_the_lub
        part_dom_eq test34 tsbChain_dom_eq2)

lemma tspf_type_adm [simp]: "adm (\<lambda> f. tspf_type f)"
proof -
  have f1: "\<And> f. (tspf_type f = ((\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f)) = (tsbDom\<cdot>b = In))
  \<and> (\<exists>Out. \<forall>b. b \<in> dom (Rep_cfun f) \<longrightarrow> tsbDom\<cdot>(the (f\<cdot>b)) = Out)))"
  by (meson tspf_type_def)
  show ?thesis
    by (simp add: f1)
qed

*)
(*
definition tspf_welloriginal:: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_well f \<equiv> tspf_type f \<and>
              (\<forall>b. (b \<in> dom (Rep_cfun f) \<longrightarrow> #\<surd>tsb b \<le> #\<surd>tsb (the (f\<cdot>b))))"


definition tspf_well:: "(('m tstream\<^sup>\<Omega> \<rightarrow> 'm tstream\<^sup>\<Omega>) option) \<Rightarrow> bool" where
"tspf_well f \<equiv> ufWell f \<and>
              (\<forall>b. ((b \<in> dom (Rep_ufun f)) \<longrightarrow> (#\<surd> b \<le> #\<surd> (the (f\<cdot>b)))))"

*)
(*? ? ? ? ?*
lemma tspf_tick_adm [simp]: "adm (\<lambda> f. \<forall>b. (b \<in> dom (Rep_cfun f) \<longrightarrow> #\<surd>tsb b \<le> #\<surd>tsb (the (f\<cdot>b))) )"
  apply (rule admI)
    (* ISAR Proof generateable via sledgehammer *)
  sledgehammer
  by (smt below_cfun_def below_trans ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg
          contlub_cfun_fun lnle_def op_the_chain op_the_lub part_dom_eq test34)

text {* There is a cfun from TSB to TSB option which is tspf_well *}  
lemma tspf_well_exists: "tspf_well (\<Lambda> tb. (tsbDom\<cdot>tb = {c1}) \<leadsto> tb)"
proof -
  have f1: "cont (\<lambda> tb. (tsbDom\<cdot>tb = {c1}) \<leadsto> tb)"
    apply (rule contI2)
      apply (simp add: below_option_def monofun_def tsbdom_below)
      by (smt cont2contlubE lub_eq po_class.chain_def po_eq_conv some_cont test34 tsbChain_dom_eq2)
  show ?thesis
    apply (simp add: tspf_well_def f1, rule)
     apply (simp add: tspf_type_def f1)
     apply(simp only: domIff2)
     apply(simp add: tsbdom_rep_eq)
     apply auto[1]
     by (simp add: domIff)
qed

text {* tspf_well is admissible *}  
lemma tspf_well_adm [simp]: "adm (\<lambda> f. tspf_well f)"
 by (simp add: tspf_well_def)

cpodef 'm :: message TSPF = "{f :: 'm TSB \<rightarrow> 'm TSB option. tspf_well f}"
  using tspf_well_exists apply blast
  using tspf_well_adm by auto





setup_lifting type_definition_TSPF
*)


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
end
*)