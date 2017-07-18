(*  Title:        TSPFTheorie.thy
    Author:       Sebastian Stüber
    Author:       Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
    e-mail:       jens.buerger@rwth-aachen.de

    Description:
*)



theory TSPF
imports TSB
begin

default_sort message


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)

(* normal wellformed definition, similar to SPF *)
(* an 'm TSPF has a fixed input-channel-set and output-set.  *)
definition tspf_type:: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_type f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> tsbDom\<cdot>b = In) \<and>
                            (b \<in> dom (Rep_cfun f) \<longrightarrow> tsbDom\<cdot>(the (f\<cdot>b)) = Out)"
(*
  (* Proof admissibility on the first part of spf_wellformed *)
  lemma tspf_type_adm1[simp]: "adm (\<lambda>f. \<exists>In. \<forall>b. (b \<in> dom f) = (tsbDom\<cdot>b = In))"
  by (smt adm_upward below_cfun_def part_dom_eq)

    (* Proof admissibility on the second part of spf_wellformed *)
  lemma tspf_type_adm2[simp]: "adm (\<lambda>f. \<exists>Out. \<forall>b. b \<in> dom f \<longrightarrow> tsbDom\<cdot>(f\<rightharpoonup>b) = Out)"
  apply(rule admI)
    by (metis part_the_chain part_the_lub tsbChain_dom_eq2 part_dom_lub)
*)

lemma tspf_type_adm1 [simp]: "adm (\<lambda>f. \<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f)) = (tsbDom\<cdot>b = In)) "
  by (smt adm_upward below_cfun_def part_dom_eq)

lemma tspf_type_adm2 [simp]: "adm (\<lambda> f. \<exists>Out. \<forall>b. b \<in> dom (Rep_cfun f) \<longrightarrow> tsbDom\<cdot>Rep_cfun f\<rightharpoonup>b = Out)"
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



definition tspf_well:: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_well f \<equiv> tspf_type f \<and>
              (\<forall>b. (b \<in> dom (Rep_cfun f) \<longrightarrow> #\<surd>tsb b \<le> #\<surd>tsb (the (f\<cdot>b))))"

lemma tspf_tick_adm [simp]: "adm (\<lambda> f. \<forall>b. (b \<in> dom (Rep_cfun f) \<longrightarrow> #\<surd>tsb b \<le> #\<surd>tsb (the (f\<cdot>b))) )"
  apply (rule admI)
    (* ISAR Proof generateable via sledgehammer *)
  by (smt below_cfun_def below_trans ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg
          contlub_cfun_fun lnle_def op_the_chain op_the_lub part_dom_eq test34)


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


lemma tspf_well_adm [simp]: "adm (\<lambda> f. tspf_well f)"
 by (simp add: tspf_well_def)

cpodef 'm :: message TSPF = "{f :: 'm TSB \<rightarrow> 'm TSB option. tspf_well f}"
  using tspf_well_exists apply blast
  using tspf_well_adm by auto





setup_lifting type_definition_TSPF



(* ----------------------------------------------------------------------- *)
  subsection \<open>Definition on TSPF\<close>
(* ----------------------------------------------------------------------- *)

subsubsection \<open>rep/abs\<close>

(* Shorter version to get to normal functions from 'm SPF's *)
definition Rep_CTSPF:: "'m TSPF \<Rightarrow> ('m TSB \<rightharpoonup> 'm TSB)" where
"Rep_CTSPF F \<equiv>  Rep_cfun (Rep_TSPF F) "

(* Shorter version to get from normal functions to 'm SPF's *)
  (* of course the argument should be "spf_well" and "cont" *)
definition Abs_CTSPF:: "('m TSB \<rightharpoonup> 'm TSB) \<Rightarrow> 'm TSPF" where
"Abs_CTSPF F \<equiv> Abs_TSPF (Abs_cfun F)"


subsubsection \<open>domain/range\<close>

(* Input Channel set of an 'm TSPF-Component *)
definition tspfDom :: "'m TSPF \<rightarrow> channel set" where
"tspfDom \<equiv> \<Lambda> F. tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF F))"

(* Output Channel set of an 'm TSPF-Component *)
definition tspfRan :: "'m TSPF \<rightarrow> channel set" where
"tspfRan \<equiv> \<Lambda> F. tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF F))"

text {* spftype" returns the type of the stream processing function.*}
definition tspfType :: "'m TSPF \<rightarrow> (channel set \<times> channel set)" where
"tspfType \<equiv> \<Lambda> f . (tspfDom\<cdot>f, tspfRan\<cdot>f)"


subsubsection \<open>apply\<close>

(* harpoon and Rep operation all in one for simpler SPF on SB applications *)
  (* bounds weaker than tsbres *)
abbreviation theRep_abbrv :: "'a TSPF \<Rightarrow> 'a TSB \<Rightarrow> 'a TSB " (infix "\<rightleftharpoons>" 62) where
"(f \<rightleftharpoons> s) \<equiv> (the ((Rep_CTSPF f) s))"

(* old 
abbreviation theRep_abbrv :: "'a TSPF \<Rightarrow> 'a TSB \<Rightarrow> 'a TSB " ("_\<rightleftharpoons>_") where
"(f \<rightleftharpoons> s) \<equiv> (the ((Rep_CTSPF f) s))"
*)

subsubsection \<open>fix\<close>

(* this function is not cont, because for 'strange' functions it is not cont *)
(* strange = the domain changes from input to output *)
definition tsbFix :: "('m TSB \<rightarrow> 'm TSB) \<Rightarrow> channel set \<Rightarrow> 'm TSB" where
"tsbFix F cs \<equiv>  (\<Squnion>i. iterate i\<cdot>F\<cdot>(tsbLeast cs))"

(* special case tsbFix for cont of the composition *)
definition tsbFix2 :: "('m TSB \<Rightarrow> 'm TSB \<rightarrow> 'm TSB) \<Rightarrow> 'm TSB \<Rightarrow> channel set \<Rightarrow> 'm TSB" where
"tsbFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(tsbLeast cs))"
  
abbreviation iter_tsbfix2 :: "('m TSB \<Rightarrow> 'm TSB \<rightarrow> 'm TSB) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB" where
"iter_tsbfix2 F i cs \<equiv>  (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(tsbLeast cs))"

abbreviation tsbfun_io_eq :: "('m TSB \<rightarrow> 'm TSB) \<Rightarrow> channel set \<Rightarrow> bool" where
"tsbfun_io_eq f cs \<equiv> tsbDom\<cdot>(f\<cdot>(tsbLeast cs)) = cs"


subsubsection \<open>causality\<close>
(* tspf_weakCausality defines equality of the input up to time n to imply equality of the output
   up to time n *)
definition tspf_weakCausality :: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_weakCausality f \<equiv> (\<forall> (n ::nat). \<forall> b1 \<in> dom (Rep_cfun f) . \<forall> b2 \<in> dom (Rep_cfun f) . 
                    (((#\<surd>tsb b1) = \<infinity>) \<and> ((#\<surd>tsb b2) = \<infinity>)) \<longrightarrow> 
                    (tsbTTake n\<cdot>b1 = tsbTTake n\<cdot>b2) \<longrightarrow>
                    (tsbTTake n\<cdot>(the (f\<cdot>b1)) = tsbTTake n\<cdot>(the (f\<cdot>b2))) )"

  (*
definition tspf_weakCausality :: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_weakCausality f \<equiv> (\<forall> (n :: nat) b1 \<in> dom (Rep_cfun f) . b1\<in> dom f \<longrightarrow> b2 \<in>dom f
    \<longrightarrow> tsbiTTake n\<cdot>b1  = tsbiTTake n\<cdot>b2
    \<longrightarrow> (tsbiTTake n\<cdot>(f \<rightharpoonup> b1) = tsbiTTake n\<cdot>(f \<rightharpoonup> b2)))"
*)
(*
(* A component may only react one time-stamp after it received the input *)
definition tspf_strongCausality :: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_strongCausality f \<equiv> (\<forall> (n :: nat) (b1 :: 'm TSB_inf)  b2. b1\<in> dom f \<longrightarrow> b2 \<in>dom f
    \<longrightarrow> tsbiTTake n\<cdot>b1  = tsbiTTake n\<cdot>b2
    \<longrightarrow> (tsbiTTake (Suc n)\<cdot>(f \<rightharpoonup> b1) = tsbiTTake (Suc n)\<cdot>(f \<rightharpoonup> b2)))"
fixes tb :: "'m TSB_inf"

*)


subsubsection \<open>composition\<close>

(* redefined composition channel sets *)
(* the input channels not fed by f1 or f2 themselves *)
definition tspfCompI :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompI f1 f2 = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) - (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"

(* internal channels *)
definition tspfCompL :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompL f1 f2 = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) \<inter> (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"

(* for legacy purposes *) 
definition tspfComp_pL :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfComp_pL f1 f2 \<equiv> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1)
                      \<union> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2)"

(* the output channels *)
definition tspfCompOc :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompOc f1 f2 = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"

(* all channels *)
definition tspfCompC :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompC f1 f2 = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 \<union> tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2"


(* helper for the composition *)
definition tspfCompH :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB  \<rightarrow> 'm TSB" where
"tspfCompH f1 f2 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f2)))" 

abbreviation iter_tspfCompH :: "'a TSPF \<Rightarrow> 'a TSPF \<Rightarrow> nat \<Rightarrow> 'a TSB  \<Rightarrow> 'a TSB" where
"iter_tspfCompH f1 f2 i \<equiv> (\<lambda> x. iterate i\<cdot>(tspfCompH f1 f2 x)\<cdot>(tsbLeast (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)))"

(* general composition operator for TSPFs *)
 (* NOTE: Does not always deliver an TSPF *)
definition tspfComp :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF" (infixl "\<otimes>" 40) where
"tspfComp f1 f2 \<equiv>
let I = tspfCompI f1 f2;
    Oc = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)
in Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = I) \<leadsto> tsbFix (tspfCompH f1 f2 x) Oc)"


(*

(* checks that neither f1 nor f2 feed back into themselves and that their outputs don't collide *)
  (* = spfComp_well + no_selfloops *)
definition comp_well:: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> bool" where
"comp_well f1 f2 \<equiv> tspfDom\<cdot>f2 \<inter>tspfRan\<cdot>f2 = {}
                \<and>  tspfDom\<cdot>f1 \<inter>tspfRan\<cdot>f1 = {}
                \<and> tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}"

*)

(*
(* applies a TSPF to an input TSB, resulting in an infinite output TSB *)
definition tspf_the_tsb:: "'m TSPF \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB_inf" (" _ \<rightharpoondown> _" )where
"tspf \<rightharpoondown> tb \<equiv> ((Rep_TSPF tspf)\<rightharpoonup> (tsb2tsbInf tb))"

(* defines the behaviour of the composition of TSPFs at time n + 1 in terms of its behaviour up to time n *)
primrec comp_helper_inf :: "nat \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSB_inf \<Rightarrow> 'm TSB" where
"comp_helper_inf 0 f1 f2 tb = tsbLeast  (tspfCompAll f1 f2) " |
"comp_helper_inf (Suc n) f1 f2 tb =( let last = comp_helper_inf n f1 f2 tb in
    (tb  \<uplus>  (f1 \<rightharpoondown> (last \<bar> tspfDom\<cdot>f1)) \<uplus> (f2 \<rightharpoondown> (last \<bar> tspfDom\<cdot>f2))   \<down> (Suc n) ))"

declare comp_helper_inf.simps(2) [simp del]

definition tspfComp :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF" (infixl "\<otimes>" 50) where
"tspfComp f1 f2 \<equiv>  Abs_TSPF (
  \<lambda> tb. (tsbiDom\<cdot>tb=(tspfCompIn f1 f2)) \<leadsto>
      (tsb2tsbInf (\<Squnion>i. comp_helper_inf i f1 f2 tb )\<bar> tspfCompOut f1 f2) )"





(* \<mu>-def *)
primrec tspfMu_helper :: "nat \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSB_inf \<Rightarrow> 'm TSB" where
"tspfMu_helper 0 f1 tb = tsbLeast (tspfDom\<cdot>f1 \<union> tspfRan\<cdot>f1) " |
"tspfMu_helper (Suc n) f1 tb =( let last = tspfMu_helper n f1 tb in
    (tb  \<uplus>  (f1 \<rightharpoondown> (last \<bar> tspfDom\<cdot>f1))  \<down> (Suc n) ))"

definition tspfMu :: "'m TSPF  \<Rightarrow> 'm TSPF" ("\<mu>_" 50) where
"tspfMu f1 \<equiv>  Abs_TSPF (
  \<lambda> tb. (tsbiDom\<cdot>tb=(tspfDom\<cdot>f1 - tspfRan\<cdot>f1)) \<leadsto>
      (tsb2tsbInf (\<Squnion>i. tspfMu_helper i f1 tb )\<bar> (tspfRan\<cdot>f1 - tspfDom\<cdot>f1)) )"



definition tspf1to1Lift :: "('m tstream \<Rightarrow> 'm tstream) \<Rightarrow>  channel \<Rightarrow> channel \<Rightarrow> 'm TSPF" where
"tspf1to1Lift f cIn cOut = Abs_TSPF (\<lambda>tb. (tsbiDom\<cdot>tb = {cIn}) \<leadsto> Abs_TSB_inf [cOut \<mapsto> f tb. cIn])"


definition tspf2to1Lift :: "('m tstream \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> 'm TSPF" where
"tspf2to1Lift f cIn1 cIn2 cOut = Abs_TSPF (\<lambda>tb. (tsbiDom\<cdot>tb = {c1,c2}) \<leadsto> Abs_TSB_inf [cOut \<mapsto> f (tb. cIn1) (tb. cIn2)])"
*)

(* ----------------------------------------------------------------------- *)
  section \<open>Lemmas on  TSPF\<close>
(* ----------------------------------------------------------------------- *)


  subsection \<open>Rep_CTSPF / Abs_CTSPF\<close>
    (* lemmas about rep/aps and so on *)
lemma rep_tspf_chain [simp]: assumes "chain Y" shows "chain (\<lambda>i. Rep_TSPF (Y i))"
  by (meson assms below_TSPF_def po_class.chain_def)

lemma rep_tspf_mono [simp]: "monofun Rep_TSPF"
  by (meson below_TSPF_def monofunI)

lemma rep_tspf_cont [simp]: "cont Rep_TSPF"
  by (metis (mono_tags, lifting) Abs_TSPF_inverse Prelude.contI2 Rep_TSPF adm_def lub_TSPF
            lub_eq mem_Collect_eq po_eq_conv rep_tspf_chain rep_tspf_mono tspf_well_adm)

lemma rep_tspf_well [simp]: "tspf_well (Rep_TSPF f)"
  using Rep_TSPF by blast

lemma rep_cspf_well [simp]: "tspf_well (Abs_cfun (Rep_CTSPF f))"
  by (simp add: Cfun.cfun.Rep_cfun_inverse Rep_CTSPF_def)

lemma rep_ctspf_cont1 [simp]: "cont Rep_CTSPF"
  by (simp add: Rep_CTSPF_def)

lemma rep_ctspf_cont2 [simp]: "cont (Rep_CTSPF f)"
  by (simp add: Rep_CTSPF_def)

lemma rep_abs_tspf [simp]: assumes "tspf_well f"
  shows "Rep_TSPF (Abs_TSPF f) = f"
  by (simp add: Abs_TSPF_inverse assms)


lemma rep_abs_ctspf [simp]: assumes "cont f" and "tspf_well (Abs_cfun f)"
  shows "Rep_CTSPF (Abs_CTSPF f) = f"
  by (simp add: Abs_CTSPF_def Rep_CTSPF_def assms(1) assms(2))



  subsection \<open>basic lemmata about TSPF\<close>

    (* inter rule for tspf_well proofs *)
lemma tspf_wellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (tsbDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> tsbDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (tsbDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  and "\<And> b. (b \<in> dom (Rep_cfun f) \<longrightarrow> #\<surd>tsb b \<le> #\<surd>tsb (the (f\<cdot>b)))"
shows "tspf_well f"
  by (meson assms(1) assms(2) assms(3) assms(4) tspf_type_def tspf_well_def)


(* mapt.empty is not an TSPF *)
lemma map_not_tspf [simp]: "\<not>(tspf_well (Abs_cfun empty))"
  apply (simp add: tspf_well_def tspf_type_def)
  using tsbleast_tsdom by blast

(* domain of an TSPF is never empty \<Rightarrow> ensured by tspf_type *)
lemma tspf_dom_not_empty [simp]: "\<exists> x. x \<in> dom (Rep_CTSPF f)"
  by (metis Cfun.cfun.Rep_cfun_inverse Rep_CTSPF_def all_not_in_conv dom_empty map_not_tspf
            part_eq rep_tspf_well)
(* range of an TSPF is never empty \<Rightarrow> ensured by tspf_type *)
lemma tspf_ran_not_empty [simp]: "\<exists> x. x \<in> ran (Rep_CTSPF f)"
  by (meson domD ranI tspf_dom_not_empty)

(* if the input of an SPF has the same domain so does its output *)
lemma tspf_sbdomeq_to_domeq: assumes "tsbDom\<cdot>x=tsbDom\<cdot>y"
  shows "x \<in> dom (Rep_CTSPF f) \<longleftrightarrow> y \<in> dom (Rep_CTSPF f)"
  by (metis Cfun.cfun.Rep_cfun_inverse Rep_CTSPF_def assms rep_cspf_well tspf_type_def
            tspf_well_def)

(* helper function for "spf_ran2sbdom". Somehow it doesn't work without *)
lemma ran2exists [simp]: assumes "x\<in>(ran f)"
  shows "\<exists> xb. ((f xb) = (Some x))"
  using assms by (simp add: ran_def)          
          
(* the domain of the SB as a result of an SPF is always the same \<Rightarrow> ensured by tspf_type *)
lemma tspf_raneq_to_sbdomeq: assumes "x \<in> ran (Rep_CTSPF f)" and "y \<in> ran (Rep_CTSPF f)"
  shows "tsbDom\<cdot>x = tsbDom\<cdot>y"
    (* ISAR Proof generateable via sledgehammer *)
  by (smt Cfun.cfun.Rep_cfun_inverse Rep_CTSPF_def assms(1) assms(2) domIff mem_Collect_eq
          option.sel option.simps(3) ran_def rep_cspf_well tspf_type_def tspf_well_def)

(* If an TSPF is applied to an input x, the output has more ticks  *)
lemma tspf_less_in_than_out_ticks: assumes "x \<in> dom (Rep_CTSPF f)"
  shows "#\<surd>tsb x \<le> #\<surd>tsb (f \<rightleftharpoons> x)"
  by (metis Rep_CTSPF_def assms rep_tspf_well tspf_well_def)

    
(* only 'm SBs with the same domain are in an 'm SPF *)
lemma tspf_dom2tsbdom: assumes "x\<in>dom (Rep_CTSPF f)" and "y\<in>dom (Rep_CTSPF f)" 
  shows "tsbDom\<cdot>x = tsbDom\<cdot>y"
  by (metis (no_types) Rep_CTSPF_def assms(1) assms(2) rep_tspf_well tspf_type_def tspf_well_def)
    
    
(* if two TSPFS are in a below-relation their input-channels are equal *)
lemma spf_below_sbdom: assumes "a\<sqsubseteq>b"  and "y \<in> dom (Rep_CTSPF a)" and "x \<in> dom (Rep_CTSPF b)"
  shows "tsbDom\<cdot>x = tsbDom\<cdot>y"
  by (metis Rep_CTSPF_def assms below_TSPF_def below_cfun_def part_dom_eq tspf_dom2tsbdom)

(* if two TSPFS are in a below-relation their output-channels are equal *)
lemma spf_below_ran: assumes "a\<sqsubseteq>b" and "x \<in> ran (Rep_CTSPF b)" and "y \<in> ran (Rep_CTSPF a)"
  shows "tsbDom\<cdot>x = tsbDom\<cdot>y"
proof -
  obtain sx where sx_def: "((Rep_CTSPF b) sx) =  (Some x)" using assms ran2exists by fastforce
  obtain sy where sy_def: "((Rep_CTSPF a) sy) =  (Some y)" using assms ran2exists by fastforce
      
  have "dom (Rep_CTSPF a) = dom (Rep_CTSPF b)"
    by (metis Rep_CTSPF_def assms(1) below_TSPF_def below_cfun_def part_dom_eq)
  thus ?thesis
    sorry
qed


(* a monotone function which has the the last property of tspf_well is weak causal *)
lemma tspf_is_weak: fixes f :: "'m TSB \<Rightarrow> 'm TSB option"
                    assumes "monofun f" and "\<And> b. (b \<in> dom f) \<longrightarrow> #\<surd>tsb b \<le> (#\<surd>tsb (the (f b)))"
                    and "tb1 \<in> dom f" and "tb2 \<in> dom f"
                    and "#\<surd>tsb tb1 = \<infinity>" and  "#\<surd>tsb tb2 = \<infinity>"
                    and "tsbTTake n\<cdot>tb1 = tsbTTake n\<cdot>tb2"
  shows "tsbTTake n\<cdot>(f\<rightharpoonup>tb1) = tsbTTake n\<cdot>(f\<rightharpoonup>tb2)"
proof (cases "tsbDom\<cdot>tb1 \<noteq> {}")
  case True
  have f0: "tsbDom\<cdot>tb1 \<noteq> {}"
    by (simp add: True)
  have f1: "tsbDom\<cdot>tb2 \<noteq> {}"
    by (metis True assms(7) tsbttake_dom)
  show ?thesis
    proof -
      (* begin with the left side *)
      have f10: "tsbTTake n\<cdot>tb1 \<in> dom f"
        by (metis assms(1) assms(3) below_option_def domIff monofun_def tsbttake_below)
      have f11: "#\<surd>tsb (tsbTTake n\<cdot>tb1) = Fin n"
        by (simp add: f0 assms(5) tsbtick_tsbttake)
      have f12: "(f\<rightharpoonup>(tsbTTake n\<cdot>tb1)) \<sqsubseteq> (f\<rightharpoonup>tb1)"
        by (metis assms(1) below_option_def eq_imp_below monofun_def tsbttake_below)
      have f14: "#\<surd>tsb (f\<rightharpoonup>(tsbTTake n\<cdot>tb1)) \<ge> Fin n"
        by (metis (full_types) assms(2) f10 f11)
      have f15: "tsbTTake n\<cdot>(f\<rightharpoonup>(tsbTTake n\<cdot>tb1)) = tsbTTake n\<cdot>(f\<rightharpoonup>tb1)"
        by (simp add: f12 f14 tsbtick_pref_eq)
      
      (* now the right side *)
      have f20: "tsbTTake n\<cdot>tb2 \<in> dom f"
        using assms(7) f10 by presburger
      have f21: "#\<surd>tsb (tsbTTake n\<cdot>tb2) = Fin n"
        by (simp add: f1 assms(6) tsbtick_tsbttake)
      have f22: "(f\<rightharpoonup>(tsbTTake n\<cdot>tb2)) \<sqsubseteq> (f\<rightharpoonup>tb2)"
        by (metis assms(1) below_option_def eq_imp_below monofun_def tsbttake_below)
      have f24: "#\<surd>tsb (f\<rightharpoonup>(tsbTTake n\<cdot>tb2)) \<ge> Fin n"
        by (metis (full_types) assms(2) f20 f21)
      have f25: "tsbTTake n\<cdot>(f\<rightharpoonup>(tsbTTake n\<cdot>tb2)) = tsbTTake n\<cdot>(f\<rightharpoonup>tb2)"
        by (simp add: f22 f24 tsbtick_pref_eq)
      show ?thesis
        using assms(7) f15 f25 by presburger
    qed
next
  case False
  have f2: "tsbDom\<cdot>tb1 = {}"
    using False by blast
  moreover
  have  "tsbDom\<cdot>tb2 = {}"
    by (metis (no_types) assms(7) f2 tsbttake_dom)
  ultimately show ?thesis
    by (metis empty_iff tsb_eq)  
qed
  
  
  subsection \<open>tspfDom\<close>

thm tspfDom_def    

  subsubsection \<open>cont\<close>
  
(* tspfDom is monotone *)
lemma tspf_dom_mono [simp]: "monofun (\<lambda> F. tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF F)))"
  proof (rule monofunI)
    fix x y :: "'m TSPF"
    assume "x \<sqsubseteq> y"
    thus "tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF x)) \<sqsubseteq> tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF y))"
      by (simp add: Rep_CTSPF_def below_TSPF_def below_cfun_def part_dom_eq)
  qed
    
lemma tspf_dom_contlub: assumes "chain Y"
  shows "tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF (\<Squnion>i. Y i))) = (\<Squnion>i. tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF (Y i))))"
proof -
  obtain tt :: "'a TSPF \<Rightarrow> 'a TSB" where
    f1: "\<forall>t. tt t \<in> dom (Rep_CTSPF t)"
    by moura
  then have f2: "\<forall>n. tsbDom\<cdot>(tt (Y n)) = tsbDom\<cdot>(tt (Lub Y))"
    by (metis (no_types) assms is_ub_thelub spf_below_sbdom)
  have f3: "\<forall>n t. (SOME t. t \<in> dom (Rep_CTSPF (Y n))) \<noteq> t \<or> tsbDom\<cdot>t = tsbDom\<cdot>(tt (Y n))"
    using f1 by (meson exE_some tspf_dom2tsbdom)
  have "tsbDom\<cdot>(SOME t. t \<in> dom (Rep_CTSPF (Lub Y))) = tsbDom\<cdot>(tt (Lub Y))"
    using f1 by (meson exE_some tspf_dom2tsbdom)
  then show ?thesis
    using f3 f2 below_refl by auto
qed
   
(* tspfDom is cont *)
lemma tspf_dom_cont [simp]: "cont (\<lambda> F. tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF F)))"
  by (simp add: contI2 tspf_dom_contlub)
    



  subsubsection \<open>equalities\<close>
  
(* insertion rule for tspfDom *)
lemma tspf_dom_insert: "tspfDom\<cdot>f = tsbDom\<cdot>(SOME b. b \<in> dom (Rep_CTSPF f))"
  by (simp add: tspfDom_def)
    
(* of two spfs are in a below relation the have the same input-channel set *)
lemma tspf_dom_below_eq: assumes "x \<sqsubseteq> y"
  shows "tspfDom\<cdot>x = tspfDom\<cdot>y"
proof -
  have "\<And>t ta. t \<notin> dom (Rep_CTSPF y) \<or> ta \<notin> dom (Rep_CTSPF x) \<or> tsbDom\<cdot>t = tsbDom\<cdot>ta"
    by (meson assms spf_below_sbdom)
  then show ?thesis
    by (metis (no_types) someI_ex tspf_dom_insert tspf_dom_not_empty)
qed


lemma tspf_dom_lub_eq: assumes "chain Y"
  shows "tspfDom\<cdot>(\<Squnion>i. Y i) = tspfDom\<cdot>(Y i)"
  using assms is_ub_thelub tspf_dom_below_eq by blast
    
lemma tspf_dom_2tsbdom [simp]: assumes "(Rep_CTSPF S) a = Some b"
  shows "tspfDom\<cdot>S = tsbDom\<cdot>a"
  by (metis assms domI someI_ex tspf_dom2tsbdom tspf_dom_insert)
    
lemma tspf_least_in_dom: "(tsbLeast (tspfDom\<cdot>f)) \<in> dom (Rep_CTSPF f)"
  by (metis someI_ex tsbleast_tsdom tspf_dom_insert tspf_dom_not_empty tspf_sbdomeq_to_domeq)
    
lemma tspf_dom_2_dom_ctspf: assumes "tspfDom\<cdot>f = tspfDom\<cdot>g"
  shows "dom (Rep_CTSPF f) = dom (Rep_CTSPF g)"
    by (metis (no_types, lifting) Cfun.cfun.Rep_cfun_inverse Collect_cong Rep_CTSPF_def assms(1) 
          dom_def mem_Collect_eq rep_cspf_well tspf_least_in_dom tspf_type_def tspf_well_def)

lemma tspf_belowI: assumes "tspfDom\<cdot>f = tspfDom\<cdot>g"
  and "\<And>x. (tsbDom\<cdot>x = tspfDom\<cdot>f \<Longrightarrow> (Rep_CTSPF f)\<rightharpoonup>x \<sqsubseteq> (Rep_CTSPF g)\<rightharpoonup>x)"
  shows "f \<sqsubseteq> g"
proof -
  have "dom (Rep_CTSPF f) = dom (Rep_CTSPF g)"
    by (meson assms(1) tspf_dom_2_dom_ctspf)
  thus ?thesis
    by (metis Cfun.cfun.Rep_cfun_inverse Rep_CTSPF_def assms(2) below_TSPF_def below_cfun_def 
              part_below rep_cspf_well tsbleast_tsdom tspf_least_in_dom tspf_type_def 
              tspf_well_def)
qed
  
    
    
  subsection \<open>tspfRan\<close>

  thm tspfRan_def  

  subsubsection \<open>cont\<close>

(* Show that tspfRan is monotone *)
lemma tspf_ran_mono [simp]: "monofun (\<lambda> F. tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF F)))"
proof (rule monofunI)
  fix x y :: "'m TSPF"
  assume "x \<sqsubseteq> y"
  thus "tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF x)) \<sqsubseteq> tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF y))"
  proof -
    obtain tt :: "'m TSPF \<Rightarrow> 'm TSB" where
      f1: "\<forall>t. tt t \<in> ran (Rep_CTSPF t)"
      by (meson tspf_ran_not_empty)
    then have f2: "tsbDom\<cdot>(SOME t. t \<in> ran (Rep_CTSPF y)) = tsbDom\<cdot>(tt x)"
      by (meson \<open>x \<sqsubseteq> y\<close> someI_ex spf_below_ran)
    have "\<And>t. tsbDom\<cdot>(SOME ta. ta \<in> ran (Rep_CTSPF t)) = tsbDom\<cdot>(tt t)"
      using f1 by (meson below_refl someI_ex spf_below_ran)
    then show ?thesis
      using f2 by simp
  qed
qed
  

lemma tspf_ran_contlub [simp]: assumes "chain Y"
  shows "tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF (\<Squnion>i. Y i))) 
          \<sqsubseteq> (\<Squnion>i. tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF (Y i))))"
  by (metis (no_types, lifting) assms below_refl is_ub_thelub po_class.chain_def someI_ex 
            spf_below_ran tspf_ran_not_empty)
    
lemma tspf_ran_cont [simp]: "cont (\<lambda> F. tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF F)))"
  by (rule contI2, simp_all)
    
  subsubsection \<open>equalities\<close>
  
lemma tspf_ran_insert: "tspfRan\<cdot>f = tsbDom\<cdot>(SOME b. b \<in> ran (Rep_CTSPF f))"
  by (simp add: tspfRan_def)
    
(* if two TSPFs are in a below relation their output channels are equal *)
lemma tspf_ran_below: assumes "x \<sqsubseteq> y"
  shows "tspfRan\<cdot>x = tspfRan\<cdot>y"
  by (smt Abs_cfun_inverse2 assms someI_ex tspfRan_def spf_below_ran tspf_ran_cont 
          tspf_ran_not_empty)
    
(* the lub of an TSPF chain has the same output channels as all the TSPFs in the chain *)
lemma tspf_ran_lub_eq: assumes "chain Y"
  shows "tspfRan\<cdot>(\<Squnion>i. Y i) = tspfRan\<cdot>(Y i)"
  using assms is_ub_thelub tspf_ran_below by blast

lemma tspf_ran_2_tsbdom [simp]: assumes "(Rep_CTSPF F) a = Some b"
  shows "tspfRan\<cdot>F = tsbDom\<cdot>b"
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms ranI someI_ex tspfRan_def 
            tspf_raneq_to_sbdomeq tspf_ran_cont)

lemma spfran_least: "tspfRan\<cdot>f = tsbDom\<cdot>(f\<rightleftharpoons> (tsbLeast (tspfDom\<cdot>f)))"
  apply (simp add: tspfRan_def)
  by (metis (no_types) domD option.sel tspf_least_in_dom tspf_ran_2_tsbdom tspf_ran_insert)
    
lemma tspf_ran_2_tsbdom2 [simp]: assumes "tsbDom\<cdot>tb = tspfDom\<cdot>f"
  shows "tsbDom\<cdot>(f\<rightleftharpoons>tb) = tspfRan\<cdot>f"
  by (metis (no_types) assms domIff option.collapse tsbleast_tsdom tspf_least_in_dom 
             tspf_ran_2_tsbdom tspf_sbdomeq_to_domeq)
    

  subsection \<open>tspfType\<close>

  thm tspfType_def
 
lemma tspf_type_cont [simp]: "cont (\<lambda>f. (tspfDom\<cdot>f, tspfRan\<cdot>f))"
  by simp
    
lemma tspf_type_insert: "tspfType\<cdot>f = (tspfDom\<cdot>f, tspfRan\<cdot>f)"
  by (simp add: tspfType_def)

  subsection \<open>tspfwell\<close>
  
    (*
lemma tspfwell_to_weak: assumes "tspf_well f"
  shows "tspf_weakCausality f"*)
    

  subsection \<open>comp-sets\<close>
    (* lemmas about I, Oc, etc. and how they correlate *)
    
  subsubsection \<open>subsets\<close>
lemma tspfcomp_I_subset_C [simp]: "(tspfCompI f1 f2) \<subseteq> (tspfCompC f1 f2)"
  using tspfCompI_def tspfCompC_def by blast

lemma tspfcomp_L_subset_C [simp]: "(tspfCompL f1 f2) \<subseteq> (tspfCompC f1 f2)"
  using tspfCompL_def tspfCompC_def by blast
    
lemma tspfcomp_pl_subset_L [simp]: "(tspfComp_pL f1 f2) = (tspfCompL f1 f2)"
  using tspfComp_pL_def tspfCompL_def by blast
    
lemma tspfcomp_pL_subset_C [simp]: "(tspfComp_pL f1 f2) \<subseteq> (tspfCompC f1 f2)"
  using tspfComp_pL_def tspfCompC_def by blast

lemma tspfcomp_Oc_subset_C [simp]: "(tspfCompOc f1 f2) \<subseteq> (tspfCompC f1 f2)"
  using tspfCompOc_def tspfCompC_def by blast

lemma tspfcomp_L_subset_Oc [simp]: "(tspfCompL f1 f2) \<subseteq> (tspfCompOc f1 f2)"
  using tspfCompL_def tspfCompOc_def by blast

lemma tspfcomp_I_inter_L_empty [simp]: "(tspfCompI f1 f2) \<inter> (tspfCompL f1 f2) = {}"
  using tspfCompI_def tspfCompL_def by blast

lemma tspfcomp_I_inter_Oc_empty [simp]: "(tspfCompI f1 f2) \<inter> (tspfCompOc f1 f2) = {}"
  using tspfCompI_def tspfCompOc_def by blast
    

    
  subsubsection \<open>commutativness\<close> 
lemma tspfcomp_I_commu: "(tspfCompI f1 f2) = (tspfCompI f2 f1)"
  using tspfCompI_def by blast

lemma tspfcomp_L_commu: "(tspfCompL f1 f2) = (tspfCompL f2 f1)"
  using tspfCompL_def by blast

lemma tspfcomp_Oc_commu: "(tspfCompOc f1 f2) = (tspfCompOc f2 f1)"
  using tspfCompOc_def by blast

lemma tspfcomp_C_commu: "(tspfCompC f1 f2) = (tspfCompC f2 f1)"
  using tspfCompC_def by blast
   

 
subsection \<open>tsbFix2\<close>

lemma tsbIterate_chain: "tsbDom\<cdot>(f\<cdot>(tsbLeast cs)) = cs \<Longrightarrow>chain (\<lambda>i. iterate i\<cdot>f\<cdot>(tsbLeast cs))"
  apply (rule chainI, subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by simp    
 

  
lemma tsbfix_2_tsbfix2: "tsbFix (F x) cs = tsbFix2 F x cs"
  by (metis (mono_tags, lifting) lub_eq tsbFix2_def tsbFix_def)  
  
lemma tsbfix2iter_eq: "tsbFix2 F x cs = (\<Squnion> i. iter_tsbfix2 F i cs x)"
  using tsbFix2_def by force
  
  subsubsection \<open>iter_tsbFix2\<close>
  
lemma iter_tsbfix2_cont [simp]: assumes "cont F"
  shows "cont (\<lambda> x. iter_tsbfix2 F i cs x)"
  by (simp add: assms)
    
lemma iter_tsbfix2_mono_pre: assumes "cont F" and "x \<sqsubseteq> y"
  shows "\<forall> i. (iter_tsbfix2 F i cs x) \<sqsubseteq> (iter_tsbfix2 F i cs y)"
  by (simp add: assms(1) assms(2) cont2monofunE monofun_cfun_fun)
    

    
lemma iter_tsbfix2_chain: assumes "tsbfun_io_eq (F x) cs"
  shows "chain (\<lambda> i. iter_tsbfix2 F i cs x)"
  by (simp add: assms(1) tsbIterate_chain)
    
    
(* the domain is always the same if io_eq holds *)
lemma iter_tsbfix2_dom: assumes "tsbfun_io_eq (F x) cs"
  shows "tsbDom\<cdot>(iter_tsbfix2 F i cs x) = tsbDom\<cdot>((F x)\<cdot>(tsbLeast cs))"
    proof (induction i)
      case 0
      then show ?case
        by (simp add: assms(1))
    next
      case (Suc i)
      then show ?case
      proof -
        have "\<And>c. (c\<cdot>(tsbLeast cs)::'a TSB) \<sqsubseteq> c\<cdot>(F x\<cdot>(tsbLeast cs))"
          by (simp add: assms monofun_cfun_arg)
        then show ?thesis
          by (metis (no_types) Suc iterate_Suc2 tsbdom_below)
      qed        
qed


subsubsection \<open>lub_iter_tsbfix2\<close>

(* mono *)

lemma lub_iter_tsbfix2_mono_pre [simp]: assumes "x \<sqsubseteq> y" and "cont F" and "tsbfun_io_eq (F x) cs"
  shows "(\<Squnion> i. iter_tsbfix2 F i cs x) \<sqsubseteq> (\<Squnion> i. iter_tsbfix2 F i cs y)"
proof -
  have f1: "\<And> i. (iter_tsbfix2 F i cs x) \<sqsubseteq>  (iter_tsbfix2 F i cs y)"
    by (simp add: assms(1) assms(2) iter_tsbfix2_mono_pre)
  moreover
  have f2: "tsbDom\<cdot>x = tsbDom\<cdot>y"
    by (simp add: assms(1) tsbdom_below)
  moreover
  have f3: "tsbfun_io_eq (F y) cs"
    using assms(1) assms(2) assms(3) cont2monofunE monofun_cfun_fun tsbdom_below by blast
  ultimately
    show ?thesis
    proof -
      have f1: "chain (\<lambda>n. iter_tsbfix2 F n cs x)"
        using assms(3) tsbIterate_chain by blast
      have "chain (\<lambda>n. iter_tsbfix2 F n cs y)"
        using f3 tsbIterate_chain by blast
      then show ?thesis
        by (simp add: assms(1) assms(2) f1 iter_tsbfix2_mono_pre lub_mono)
    qed
qed
    
(* cont *)
  
lemma chain_lub_iter_sbfix2: assumes "chain Y" and "cont F" and "tsbfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_tsbfix2 F ia cs (Y i))"
proof -
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    by (simp add: assms(1) po_class.chainE)
  have f2: "\<And> ia. tsbfun_io_eq (F (Y ia)) cs"
    proof -
      fix ia :: nat
      have f1: "\<forall>f fa. \<not> cont f \<or> \<not> chain fa \<or> chain (\<lambda>n. f (fa n::'a TSB)::'a TSB \<rightarrow> 'a TSB)"
        using ch2ch_cont by blast
      then have "tsbDom\<cdot>(F (Y ia)\<cdot>(tsbLeast cs)) = tsbDom\<cdot>(\<Squnion>n. F (Y n)\<cdot>(tsbLeast cs))"
        using assms(1) assms(2) ch2ch_Rep_cfunL tsbChain_dom_eq2 by blast
      then have "tsbDom\<cdot>(F (Y ia)\<cdot>(tsbLeast cs)) = tsbDom\<cdot>(F (Lub Y)\<cdot>(tsbLeast cs))"
        using f1 by (metis (no_types) assms(1) assms(2) cont2contlubE contlub_cfun_fun)
      thus "tsbfun_io_eq (F (Y ia)) cs"
        using assms(3) by presburger
    qed
    
  thus ?thesis
    apply (subst chainI, simp_all add: assms)
    by (simp add: lub_iter_tsbfix2_mono_pre f1 f2 assms)
qed
  
lemma chain_lub_lub_iter_tsbfix2: assumes "chain Y" and "cont F" 
                                  and "tsbfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "(\<Squnion> i ia. iter_tsbfix2 F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_tsbfix2 F ia cs (Y i))"
proof -
  have f1: "\<And> i. cont (\<lambda> x. iter_tsbfix2 F i cs x)"
    by (simp add: assms(2))
  moreover
  have f2: "(\<Squnion>i. iter_tsbfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_tsbfix2 F ia cs (Y i))"
    by (metis (no_types) assms(1) assms(2) ch2ch_Rep_cfunR ch2ch_cont cont2contlubE 
              contlub_cfun_arg contlub_cfun_fun)
  moreover
  have f3: "\<And> ia. tsbfun_io_eq (F (Y ia)) cs"
    using assms(1) assms(2) assms(3) cont2monofunE is_ub_thelub 
          monofun_cfun_fun tsbdom_below by blast
  ultimately show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_tsbfix2_chain)
qed
  
(* dom *)
  
  
lemma lub_iter_tsbfix2_dom: assumes "tsbfun_io_eq (F x) cs"
  shows "tsbDom\<cdot>(\<Squnion>i. iter_tsbfix2 F i cs x) =  tsbDom\<cdot>((F x)\<cdot>(tsbLeast cs))"
proof -
  have "\<And>n. tsbfun_io_eq (iterate n\<cdot>(F x)) cs"
    by (simp add: assms iter_tsbfix2_dom)
  then show ?thesis
    using assms tsbChain_dom_eq2 tsbIterate_chain by blast
qed
    

subsubsection \<open>if_lub_iter_tsbfix2\<close>

(* mono *)
  
lemma if_lub_iter_tsbfix2_mono_pre: assumes "x\<sqsubseteq> y" and "cont F"
                                   and "(P x) \<Longrightarrow> tsbfun_io_eq (F x) cs"
                                   and "tsbDom\<cdot>x = tsbDom\<cdot>y \<Longrightarrow> (P x) = (P y)"
  shows "((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_tsbfix2 F i cs) x)) x)
         \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_tsbfix2 F i cs) x)) y)"
proof (cases "(P x)")
  case True
  hence f1: "tsbfun_io_eq (F x) cs"
    by (simp add: assms(3))
  have f2: "tsbDom\<cdot>x = tsbDom\<cdot>y"
    by (simp add: assms(1) tsbdom_below)
  have f3: "(\<Squnion>i.(iter_tsbfix2 F i cs) x) \<sqsubseteq> (\<Squnion>i.(iter_tsbfix2 F i cs) y)"
    by (simp add: assms(1) assms(2) f1 lub_iter_tsbfix2_mono_pre)
  thus ?thesis
    using assms(4) f2 some_below by auto
next
  case False
  have "tsbDom\<cdot>y = tsbDom\<cdot>x"
    by (metis assms(1) tsbdom_below)
  then show ?thesis
    using False assms(4) by auto
qed

(* Intro lemma for if sbfix is mono *)  
lemma tsbfix_monoI [simp]: assumes "cont F" "\<And> x. (P x) \<Longrightarrow> tsbfun_io_eq (F x) cs" 
                          and "\<And> x y. tsbDom\<cdot>x = tsbDom\<cdot>y \<Longrightarrow> P x = P y"
                        shows "monofun (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_tsbfix2 F i cs) x))"
proof (rule monofunI)
    fix x :: "'a TSB" and y :: "'a TSB"
    assume a1: "x \<sqsubseteq> y"
    hence f2: "\<And>t. P y \<or> tsbDom\<cdot>t \<noteq> tsbDom\<cdot>x \<or> \<not> P t"
      by (meson assms(3) tsbdom_below)
    have "\<And>t. P t \<or> tsbDom\<cdot>x \<noteq> tsbDom\<cdot>t \<or> \<not> P y"
    using a1 by (meson assms(3) tsbdom_below)
  moreover
  { assume "Some (\<Squnion>n. iter_tsbfix2 F n cs x) \<notsqsubseteq> Some (\<Squnion>n. iter_tsbfix2 F n cs y)"
    then have "tsbDom\<cdot>(F x\<cdot>(tsbLeast cs)) \<noteq> cs"
      using a1 assms(1) lub_iter_tsbfix2_mono_pre some_below by blast
    then have "\<exists>t. \<not> P t \<and> \<not> P x \<and> tsbDom\<cdot>x = tsbDom\<cdot>t"
      using assms(2) by blast }
  ultimately show "(P x)\<leadsto>\<Squnion>n. iter_tsbfix2 F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_tsbfix2 F n cs y"
    using f2 by auto
qed

   
(* cont *)
  
(* two lubs can be merged together if a function F is cont in x for every i *)
lemma cont2lub_lub_eq: assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
proof -
  { assume "\<exists>a. (\<Squnion>n. F a (Y n)) \<noteq> F a (Lub Y)"
    have ?thesis
      by (simp add: cont cont2contlubE) }
  then show ?thesis
    by force
qed
  
lemma chain_if_lub_iter_tsbfix2_case:  assumes "P (\<Squnion>i. Y i)" 
                                      and  "chain Y" and "cont F"
                                      and "\<And> x. (P x) \<Longrightarrow> tsbfun_io_eq (F x) cs" 
                                      and "\<And> x y. tsbDom\<cdot>x = tsbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_tsbfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_tsbfix2 F ia cs) (Y i)))"
proof -
  have f1: "tsbfun_io_eq (F (\<Squnion>i. Y i)) cs"
    by (simp add: assms(1) assms(4))
  have f2: "(\<Squnion>i. iter_tsbfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_tsbfix2 F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f3: "\<And> ia. tsbfun_io_eq (F (Y ia)) cs"
    by (simp add: assms(1) assms(2) assms(4) assms(5))
  have f4: "(\<Squnion>i ia. iter_tsbfix2 F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_tsbfix2 F ia cs (Y i))"
    by (simp add: assms(2) assms(3) chain_lub_lub_iter_tsbfix2 f1)
      
  (* PART II: show the equality for the packaging with Some *)
  have f10: "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i. iter_tsbfix2 F i cs (\<Squnion>i. Y i)) 
              = Some (\<Squnion>i. iter_tsbfix2 F i cs (\<Squnion>i. Y i))"
   by (simp add: assms(1))
  have f11: "(\<Squnion>i. (P (Y i)) \<leadsto>  \<Squnion>ia. iter_tsbfix2 F ia cs (Y i)) 
              = Some (\<Squnion>i ia. iter_tsbfix2 F ia cs (Y i))"
  proof -
    have f111: "(\<Squnion>i. (P (Y i)) \<leadsto>   \<Squnion>ia. iter_tsbfix2 F ia cs (Y i)) 
                 = (\<Squnion>i. Some(\<Squnion>ia. iter_tsbfix2 F ia cs (Y i)))"
      by (simp add: assms(1) assms(2) assms(5))
    have f112_chain: "chain (\<lambda>i. \<Squnion>ia. iter_tsbfix2 F ia cs (Y i))"
      by (simp add: assms(2) assms(3) chain_lub_iter_sbfix2 f1)
    have f112: "(\<Squnion>i. Some(\<Squnion>ia. iter_tsbfix2 F ia cs (Y i))) 
            = Some (\<Squnion>i ia. iter_tsbfix2 F ia cs (Y i))"
      by (simp add: cont2contlubE f112_chain)
    thus ?thesis
      using f111 by auto
  qed
    
  show ?thesis
    apply (subst f10, subst f11)
    by (simp add: f2 f4 some_below)
qed
  
  
lemma chain_if_lub_iter_tsbfix2:  assumes "chain Y" and "cont F"
                                  and "\<And> x. (P x) \<Longrightarrow> tsbfun_io_eq (F x) cs" 
                                  and "\<And> x y. tsbDom\<cdot>x = tsbDom\<cdot>y \<Longrightarrow> P x = P y" 
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_tsbfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_tsbfix2 F ia cs) (Y i)))"
proof (cases "P (\<Squnion>i. Y i)")
  case True
  thus ?thesis
    using  chain_if_lub_iter_tsbfix2_case assms by blast
next
  case False
  hence f1: "(P (\<Squnion>i. Y i)) = False"
    by simp
  have f2: "\<forall>i. tsbDom\<cdot>(Y i) = tsbDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  hence f3: "\<forall>i. (P (Y i)) = (P (\<Squnion>i. Y i))"
      by (metis assms(4))
    thus ?thesis
  by (simp add: False)
qed
  
          
(* Intro lemma for cont proofs with tsbfix *)
lemma tsbfix_contI [simp]:   assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> tsbfun_io_eq (F x) cs" 
                             and "\<And> x y. tsbDom\<cdot>x = tsbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "cont (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_tsbfix2 F i cs) x) )"
    apply (rule contI2)
    using tsbfix_monoI assms apply blast
    using chain_if_lub_iter_tsbfix2 assms by blast
      
lemma tsbfix_contI2 [simp]: fixes F :: "'m TSB \<Rightarrow> 'm TSB \<rightarrow> 'm TSB"
                            assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> tsbfun_io_eq (F x) cs" 
                            and "\<And> x y. tsbDom\<cdot>x = tsbDom\<cdot>y \<Longrightarrow> P x = P y"
                            shows "cont (\<lambda> x. (P x) \<leadsto> tsbFix (F x) cs)"
proof -
  have f1: "(\<lambda> x. (P x) \<leadsto> tsbFix (F x) cs) = (\<lambda> x. (P x) \<leadsto> tsbFix2 F x cs)"
    apply (subst tsbfix_2_tsbfix2)
    by simp
  show ?thesis
    apply (subst f1, subst tsbFix2_def)
    using tsbfix_contI assms by blast
qed
  
  
section \<open>tspfComp\<close>  
  
  subsection \<open>pre\<close>

lemma tspfcomp2_lubiter: "tspfComp f1 f2 = 
  Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) 
      \<leadsto> (\<Squnion>i. iterate i\<cdot>(tspfCompH f1 f2 x)\<cdot>(tsbLeast (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2))))"
  apply (subst tspfComp_def, subst tsbFix_def)
  by (simp)
    
lemma tspfcomp2_iterCompH: "tspfComp f1 f2 = 
  Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) 
      \<leadsto> (\<Squnion>i. iter_tspfCompH f1 f2 i x))"
  by (simp add: tspfcomp2_lubiter)


  subsection \<open>tspfCompH\<close>
  (* lemmas about the composition helper *)
  (* the proofs below are very comparable to those in SPF_Comp.thy *)  
  thm tspfCompH_def
    
subsubsection \<open>cont\<close>

lemma tspfcomph_cont [simp]: 
  shows "cont (\<lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f2)))"
proof -
  have f1: "cont (\<lambda> z. (Rep_cfun (Rep_TSPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f1)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  moreover 
  have f2: "cont (\<lambda> z. (Rep_cfun (Rep_TSPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f2)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>z. tsbUnion\<cdot>(Rep_cfun (Rep_TSPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f1))) 
        \<and> cont (\<lambda>z. Rep_TSPF f2\<cdot>((x \<uplus> z)\<bar>tspfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> z. (Rep_cfun (Rep_TSPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f1)) 
                          \<uplus> (Rep_cfun (Rep_TSPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by (simp add: Rep_CTSPF_def)
qed
  
lemma tspfcomph_cont2 [simp]:
  shows "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f2)))"
proof -
  have f0: "cont (\<lambda>x. (x \<uplus> z))"
    by simp
  have f1: "cont (\<lambda> x. (Rep_cfun (Rep_TSPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f1)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  moreover
  have f2: "cont (\<lambda> x. (Rep_cfun (Rep_TSPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f2)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>x. tsbUnion\<cdot>(Rep_cfun (Rep_TSPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f1))) 
        \<and> cont (\<lambda>x. Rep_TSPF f2\<cdot>((x \<uplus> z)\<bar>tspfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> x. (Rep_cfun (Rep_TSPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f1)) 
                    \<uplus> (Rep_cfun (Rep_TSPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>tspfDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by (simp add: Rep_CTSPF_def)
qed
  
lemma tspfcomph_cont_x [simp]: "cont (\<lambda> x. tspfCompH f1 f2 x)"
  apply (subst tspfCompH_def)
  by (simp only: cont2cont_LAM tspfcomph_cont tspfcomph_cont2)
    
lemma tspfcomph_insert: "tspfCompH f1 f2 x\<cdot>z= ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f2)))"
  by (simp add: tspfCompH_def)

    
subsubsection \<open>dom\<close>
  
lemma tspfcomph_dom [simp]: assumes "tsbDom\<cdot>x = tspfCompI f1 f2"
                            and "tsbDom\<cdot>tb = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"
  shows "tsbDom\<cdot>((tspfCompH f1 f2 x)\<cdot>tb) = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"
proof -
  have f0: "tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 - (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) = tsbDom\<cdot>x"
        using assms(1) tspfCompI_def by blast
  have f1: "tsbDom\<cdot>(f1 \<rightleftharpoons> ((x \<uplus> tb)  \<bar> tspfDom\<cdot>f1)) = tspfRan\<cdot>f1"
    by (metis Un_Diff_cancel2 Un_upper1 assms(2) f0 sup.coboundedI1 tsbunion_dom 
              tspf_ran_2_tsbdom2 tsresrict_dom2)
  have f2: "tsbDom\<cdot>(f2 \<rightleftharpoons> ((x \<uplus> tb)  \<bar> tspfDom\<cdot>f2)) = tspfRan\<cdot>f2"
    proof -
      have "tspfDom\<cdot>f2 \<subseteq> tsbDom\<cdot>(x \<uplus> tb)"
        using assms(2) f0 by auto
      then show ?thesis
        by (meson tspf_ran_2_tsbdom2 tsresrict_dom2)
    qed
    show ?thesis
      by (simp add: f1 f2 assms tspfCompH_def)
qed
    
  
  
  subsection \<open>iter_tspfCompH\<close>      
    
lemma iter_tspfcomph_cont [simp]: "cont (\<lambda> x. iter_tspfCompH f1 f2 i x)"
  by simp
    
lemma iter_tspfcomph_chain [simp]: assumes "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "chain (\<lambda> i. iter_tspfCompH f1 f2 i x)"
  by (simp add: assms tsbIterate_chain)    
    
lemma iter_tspfcomph_dom [simp]: assumes "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "tsbDom\<cdot>(iter_tspfCompH f1 f2 i x) = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"
  by (simp add: assms iter_tsbfix2_dom)

lemma lub_iter_tspfcomph_dom [simp]: assumes "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "tsbDom\<cdot>(\<Squnion> i. iter_tspfCompH f1 f2 i x) = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)"
  by (simp add: assms lub_iter_tsbfix2_dom)
    
    
subsection \<open>basic properties\<close>
    
lemma tspfcomp_cont [simp]: 
  shows "cont (\<lambda> x. (tsbDom\<cdot>x = (tspfCompI f1 f2)) 
                \<leadsto> tsbFix (tspfCompH f1 f2 x) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2))"
  by simp
  
    
    
end