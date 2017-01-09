(*  Title:        TSPFTheorie.thy
    Author:       Sebastian Stüber, Jens Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
                  jens.buerger@rwth-aachen.de

    Description: 
*)

(* WARNING: THIS IS NOT A PRODUCTION THEORY, DO NOT IMPORT *)
(* Changes: weak causality is the new standard for TSPF *)
(* Checked compability with TSPS *)

theory TSPFTheorie_JB
imports TSBTheorie
begin

default_sort message


(* ----------------------------------------------------------------------- *)
  section \<open>Definition of "Timed Stream (Bundle) Processing Function"\<close>
(* ----------------------------------------------------------------------- *)


  (* normal wellformed definition, similar to SPF *)
  (* an 'm TSPF has a fixed input-channel-set and output-set.  *)
  definition tspf_type :: "('m TSB_inf \<rightharpoonup> 'm TSB_inf) \<Rightarrow> bool" where
  "tspf_type f \<equiv>  (\<exists> In.  \<forall>b. (b \<in> dom f \<longleftrightarrow>  tsbiDom\<cdot>b = In)) \<and> 
                  (\<exists> Out. \<forall>b. (b \<in> ran f \<longrightarrow>  tsbiDom\<cdot>b = Out))"

  (* tspf_weakCausality defines equality of the input up to time n to imply equality of the output 
     up to time n *)
  definition tspf_weakCausality :: "('m TSB_inf \<rightharpoonup> 'm TSB_inf) \<Rightarrow> bool" where
  "tspf_weakCausality f \<equiv> (\<forall> (n :: nat) (b1 :: 'm TSB_inf)  b2. b1\<in> dom f \<longrightarrow> b2 \<in>dom f
      \<longrightarrow> tsbiTTake n\<cdot>b1  = tsbiTTake n\<cdot>b2 
      \<longrightarrow> (tsbiTTake n\<cdot>(f \<rightharpoonup> b1) = tsbiTTake n\<cdot>(f \<rightharpoonup> b2)))"

  (* A component may only react one time-stamp after it received the input *)
  definition tspf_strongCausality :: "('m TSB_inf \<rightharpoonup> 'm TSB_inf) \<Rightarrow> bool" where
  "tspf_strongCausality f \<equiv> (\<forall> (n :: nat) (b1 :: 'm TSB_inf)  b2. b1\<in> dom f \<longrightarrow> b2 \<in>dom f
      \<longrightarrow> tsbiTTake n\<cdot>b1  = tsbiTTake n\<cdot>b2 
      \<longrightarrow> (tsbiTTake (Suc n)\<cdot>(f \<rightharpoonup> b1) = tsbiTTake (Suc n)\<cdot>(f \<rightharpoonup> b2)))" 


   definition tspfs_well ::"('m TSB_inf \<rightharpoonup> 'm TSB_inf) \<Rightarrow> bool" where
   "tspfs_well f \<equiv> tspf_strongCausality f \<and> tspf_type f"

   definition tspfw_well ::"('m TSB_inf \<rightharpoonup> 'm TSB_inf) \<Rightarrow> bool" where
   "tspfw_well f \<equiv> tspf_weakCausality f \<and> tspf_type f"



    (* Proof admissibility on the first part of spf_wellformed *)
  lemma tspf_type_adm1[simp]: "adm (\<lambda>f. \<exists>In. \<forall>b. (b \<in> dom f) = (tsbiDom\<cdot>b = In))"
  by (smt adm_upward below_cfun_def part_dom_eq)
  
    (* Proof admissibility on the second part of spf_wellformed *)
  lemma tspf_type_adm2[simp]: "adm (\<lambda>f. \<exists>Out. \<forall>b. b \<in> dom f \<longrightarrow> tsbDom\<cdot>(f\<rightharpoonup>b) = Out)"   
  apply(rule admI)
  by (metis part_the_chain part_the_lub tsbChain_dom_eq2 part_dom_lub) 


  lemma tspf_strongc_exists: "tspf_strongCausality [(Abs_TSB_inf empty) \<mapsto> (Abs_TSB_inf empty)]"
  by(simp add: tspf_strongCausality_def)

  lemma tspf_weakc_exists: "tspf_weakCausality [(Abs_TSB_inf empty) \<mapsto> (Abs_TSB_inf empty)]"
  by(simp add: tspf_weakCausality_def)

  lemma tspfs_well_exists: "tspfs_well [Abs_TSB_inf Map.empty \<mapsto> Abs_TSB_inf Map.empty]"
  apply(simp add: tspfs_well_def tsbdom_insert dom_def tsb_well_def)
  apply(rule+)
  apply (simp add: tspf_strongc_exists)
  apply(simp add: tspf_type_def)
  by (metis dom_empty empty_iff tsb_inf_exists tsbi_eq tsbidom_rep_eq)


  lemma tspfw_well_exists: "tspfw_well [Abs_TSB_inf Map.empty \<mapsto> Abs_TSB_inf Map.empty]"
  apply(simp add: tspfw_well_def tsbdom_insert dom_def tsb_well_def)
  apply(rule+)
  apply (simp add: tspf_weakc_exists)
  apply(simp add: tspf_type_def)
  by (metis dom_empty empty_iff tsb_inf_exists tsbi_eq tsbidom_rep_eq)
  


  cpodef 'm TSPF = "{F :: 'm TSB_inf \<rightharpoonup> 'm TSB_inf. tspfw_well F}"
  using tspfw_well_exists apply blast
  using tsbi_option_adm by blast
  
  
setup_lifting type_definition_TSPF



(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Definition on TSPF\<close>
(* ----------------------------------------------------------------------- *)


  (* Input Channel set of an 'm TSPF-Component *)
  definition tspfDom :: "'m TSPF \<rightarrow> channel set" where
  "tspfDom \<equiv> \<Lambda> F. tsbiDom\<cdot>(SOME b. b \<in> dom (Rep_TSPF F))"

  (* Output Channel set of an 'm TSPF-Component *)
  definition tspfRan :: "'m TSPF \<rightarrow> channel set" where
  "tspfRan \<equiv> \<Lambda> F. tsbiDom\<cdot>(SOME b. b \<in> ran (Rep_TSPF F))"




abbreviation tspf_the_abbrv:: "'m TSPF \<Rightarrow> 'm TSB_inf \<Rightarrow> 'm TSB_inf" (" _ \<rightharpoonup> _" )where
"tspf \<rightharpoonup> tb \<equiv> the ((Rep_TSPF tspf) tb)"


(* the union of all input and output channels *)
definition tspfCompAll :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompAll f1 f2 = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 \<union> tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2"

(* the channels flowing from f1 to f2 and vice versa *)
definition tspfCompInternal :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompInternal f1 f2 = ((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"

(* the input channels not fed by f1 or f2 themselves *)
definition tspfCompIn :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompIn f1 f2 = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) - ((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"

(* the output channels not leading back into the TSPF composition *)
definition tspfCompOut :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> channel set" where
"tspfCompOut f1 f2 = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) - ((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"

(* checks that neither f1 nor f2 feed back into themselves and that their outputs don't collide *)
definition comp_well:: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> bool" where
"comp_well f1 f2 \<equiv> tspfDom\<cdot>f2 \<inter>tspfRan\<cdot>f2 = {}
                \<and>  tspfDom\<cdot>f1 \<inter>tspfRan\<cdot>f1 = {} 
                \<and> tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}"

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


(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Lemmas on  TSPF\<close>
(* ----------------------------------------------------------------------- *)


lemma tspf_weakCausalityI: assumes "\<And>n b1 b2. b1\<in> dom f \<Longrightarrow> b2 \<in>dom f
      \<Longrightarrow> tsbiTTake n\<cdot>b1  = tsbiTTake n\<cdot>b2 
      \<Longrightarrow> (tsbiTTake n\<cdot>(f \<rightharpoonup> b1) = tsbiTTake n\<cdot>(f \<rightharpoonup> b2))"
      shows "tspf_weakCausality f"
apply(auto simp add: tspf_weakCausality_def)
using assms by fastforce


lemma tspf_strongCausalityI: assumes "\<And>n b1 b2. b1\<in> dom f \<Longrightarrow> b2 \<in>dom f
      \<Longrightarrow> tsbiTTake n\<cdot>b1  = tsbiTTake n\<cdot>b2 
      \<Longrightarrow> (tsbiTTake (Suc n)\<cdot>(f \<rightharpoonup> b1) = tsbiTTake (Suc n)\<cdot>(f \<rightharpoonup> b2))"
      shows "tspf_strongCausality f"
apply(auto simp add: tspf_strongCausality_def)
using assms by fastforce


lemma tspf_StrongImpWeak[simp]: assumes "tspf_strongCausality  f" 
  shows "tspf_weakCausality f"
by (metis assms tsbiSucTake tspf_strongCausality_def tspf_weakCausality_def)

lemma rep_tspfw_well [simp]: "tspfw_well (Rep_TSPF F)"
using Rep_TSPF by blast

lemma [simp]: assumes "tspfw_well F" shows "Rep_TSPF (Abs_TSPF F) = F"
using Abs_TSPF_inverse assms tspfs_well_def by auto

(* Show that Map.empty is not an SPF *)
lemma map_not_tspf [simp]: "\<not>(tspfs_well empty)"
  apply (simp add: tspfs_well_def)
  apply rule
  by(simp add: tspf_type_def tsbidom_insert)


(* the "dom" of an SPF is never empty *) 
(* Used in "Some" proofs, for example in "spfDom" *)
lemma spf_dom_not_empty [simp]: 
  shows "\<exists>x. x\<in>dom (Rep_TSPF F)"
by (meson rep_tspfw_well tsbi_dom_ex tspf_type_def tspfw_well_def)

(* the "rand" of an SPF is never empty *) 
(* Used in "Some" proofs, for example in "spfRan" *)
lemma spf_ran_not_empty [simp]: 
  shows "\<exists>x. x\<in> (ran (Rep_TSPF F))"
by (meson domIff not_None_eq ranI spf_dom_not_empty)

(* only StBundles with the same domain are in an SPF *)
lemma tspf_tsbdom2dom: assumes "tsbiDom\<cdot>x = tsbiDom\<cdot>y" 
  shows "x\<in>dom (Rep_TSPF f) \<longleftrightarrow>y\<in>dom (Rep_TSPF f)"
by (metis assms rep_tspfw_well tspf_type_def tspfw_well_def)

(* only StBundles with the same domain are in an SPF *)
lemma tspf_dom2tsbdom: assumes "x\<in>dom (Rep_TSPF f)" and "y\<in>dom (Rep_TSPF f)" 
  shows "tsbiDom\<cdot>x = tsbiDom\<cdot>y"
by (metis assms(1) assms(2) rep_tspfw_well tspf_type_def tspfw_well_def)

(* helper function for "spf_ran2sbdom". Somehow it doesn't work without *)
lemma ran2exists[simp]: assumes "x\<in>(ran f)"
  shows "\<exists> xb. ((f xb) = (Some x))"
using assms by (simp add: ran_def)

(* only StBundles with the same domain are in an SPF *)
lemma tspf_ran2tsbdom: assumes "x\<in>ran (Rep_TSPF f)" and "y\<in>ran (Rep_TSPF f)" 
  shows "tsbiDom\<cdot>x = tsbiDom\<cdot>y"
by (metis assms(1) assms(2) rep_tspfw_well tspf_type_def tspfw_well_def)


(* if 2 SPF's are in a below-relation their Input-Channels are equal *)
lemma tspf_below_tsbdom: assumes "a\<sqsubseteq>b" and "x \<in> dom (Rep_TSPF b)" and "y \<in> dom (Rep_TSPF a)"
  shows "tsbiDom\<cdot>x = tsbiDom\<cdot>y"
by (metis  assms(1) assms(2) assms(3) below_TSPF_def below_cfun_def part_dom_eq tspf_dom2tsbdom)

(* if 2 SPF's are in a below-relation their Output-Channels are equal *)
lemma tspf_below_ran: assumes "a\<sqsubseteq>b" and "x \<in> ran (Rep_TSPF b)" and "y \<in> ran (Rep_TSPF a)"
  shows "tsbiDom\<cdot>x = tsbiDom\<cdot>y"
proof -
  obtain sx where sx_def: "((Rep_TSPF b) sx) =  (Some x)" using assms ran2exists by fastforce
  obtain sy where sy_def: "((Rep_TSPF a) sy) =  (Some y)" using assms ran2exists by fastforce

  have "dom (Rep_TSPF a) = dom (Rep_TSPF b) " by (metis assms(1) below_TSPF_def part_dom_eq) 
 thus ?thesis by (metis assms(2) assms(3) tsbi_option_below assms(1) below_TSPF_def rep_tspfw_well tspfw_well_def tspf_type_def)
qed

lemma tspf_typeI: assumes "\<And>b. b\<in>dom f \<Longrightarrow> tsbiDom\<cdot>b = In"
  and "\<And>b. tsbiDom\<cdot>b = In \<Longrightarrow> b\<in>dom f"
  and "\<And> h. (h\<in>ran f) \<Longrightarrow> (tsbiDom\<cdot>h = Out)"
  shows "tspf_type f"
  apply(simp add: tspf_type_def)
  apply rule
   apply (meson assms(1) assms(2))
  using assms(3) by blast






(* tspfDom *)


(* tspfDom is monotonic. Used to show that tspfDom is continuous *)
lemma tspf_dom_mono[simp]: "monofun (\<lambda>f. tsbiDom\<cdot>(SOME b. b \<in> dom (Rep_TSPF f)))"
apply(rule monofunI)
by (simp add: below_TSPF_def part_dom_eq)


(* used to show that tspfDom is continuous *)
lemma tspf_dom_contlub [simp]: assumes "chain Y" 
  shows "tsbiDom\<cdot>(SOME b. b \<in> dom (Rep_TSPF (\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. tsbiDom\<cdot>(SOME b. b \<in> dom (Rep_TSPF (Y i))))"
by (metis (mono_tags, lifting) assms below_refl is_ub_thelub lub_chain_maxelem po_eq_conv someI_ex tspf_below_tsbdom spf_dom_not_empty)


(* tspfDom is continuous *)
lemma tspf_dom_cont [simp]:"cont (\<lambda>f. tsbiDom\<cdot>(SOME b. b \<in> dom (Rep_TSPF f)))"
by(simp add: contI2)

lemma tspfdom_insert: "tspfDom\<cdot>F = tsbiDom\<cdot>(SOME b. b \<in> dom (Rep_TSPF F))"
by (simp add: tspfDom_def)

lemma tspfdom_below: assumes "x\<sqsubseteq>y"
  shows "tspfDom\<cdot>x = tspfDom\<cdot>y"
by (metis (no_types, lifting) assms someI spf_dom_not_empty tspf_below_tsbdom tspfdom_insert)

lemma tsbiDom_part: "b \<in> dom (\<lambda>tb. (tsbiDom\<cdot>tb = cs)\<leadsto> g tb) \<Longrightarrow> tsbiDom\<cdot>b = cs"
  by (smt domIff)


lemma tsbidom_dom [simp]: assumes "tsbiDom\<cdot>tbi = tspfDom\<cdot>f"
  shows "tbi \<in> (dom (Rep_TSPF f))" 
by (metis someI_ex spf_dom_not_empty tspf_tsbdom2dom tspfdom_insert assms)

(* if two TSPFs x and y share the same domains and agree elementwise on their outputs then they are
   the same TSPF *)
lemma tspf_eq: assumes "tspfDom\<cdot>x = tspfDom\<cdot>y"
                   and "\<And>tbi. (tsbiDom\<cdot>tbi = tspfDom\<cdot>x) \<Longrightarrow> (((Rep_TSPF x) \<rightharpoonup> tbi)= ((Rep_TSPF y)\<rightharpoonup>tbi))"
               shows "x=y"
proof -
  have "dom (Rep_TSPF x) = dom (Rep_TSPF y)"
  by (metis (no_types, lifting) Collect_cong assms(1) dom_def mem_Collect_eq tsbidom_dom tspf_dom2tsbdom tspfdom_insert)
  thus ?thesis
  by (metis Rep_TSPF_inject assms(2) part_eq tsbidom_dom tspf_dom2tsbdom tspfdom_insert) 
qed


lemma tspf_dom_ex: "\<exists>b. b \<in> dom (\<lambda>tb . (tsbiDom\<cdot>tb = cs) \<leadsto> g tb)" (is "_dom ?F")
by (simp add: domIff2 tsbi_dom_ex)

lemma tspf_domp_simps[simp]: "tsbiDom\<cdot>(SOME b. b \<in> dom (\<lambda>tb . (tsbiDom\<cdot>tb = cs) \<leadsto> g tb)) = cs"
proof -
  have "\<exists>f. (SOME t. t \<in> dom (\<lambda>t. (tsbiDom\<cdot>t = cs)\<leadsto>g t)) \<in> dom (\<lambda>t. (tsbiDom\<cdot>t = cs)\<leadsto>f t::'b)"
    by (metis (no_types) ex_in_conv some_in_eq tspf_dom_ex)
  then show ?thesis
    by (metis (no_types) tsbiDom_part)
qed





(* tspfRan *)

(* Shows that "spfRan" is "monofun". Used to show that spfRan is cont *)
lemma tspf_ran_mono[simp]: "monofun (\<lambda> f.  tsbiDom\<cdot>(SOME b. b \<in> ran (Rep_TSPF f)))"
apply(rule monofunI)
by (metis (full_types) below_TSPF_def po_eq_conv tsbi_option_below)

(* used to show that spfRan is cont *)
lemma tspf_ran_contlub [simp]: assumes "chain Y"
  shows "tsbiDom\<cdot>(SOME b. b \<in> ran (Rep_TSPF (\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. tsbiDom\<cdot>(SOME b. b \<in> ran (Rep_TSPF (Y i))))"
by (metis (mono_tags, lifting) assms is_ub_thelub lub_chain_maxelem po_eq_conv someI_ex spf_ran_not_empty tspf_below_ran)

(* Shows that "spfRan" is "cont" *)
lemma tspf_ran_cont[simp]: "cont (\<lambda>f. tsbiDom\<cdot>(SOME b. b \<in> ran (Rep_TSPF f)))"
apply(rule contI2)
by simp_all

lemma tspfran_insert: "tspfRan\<cdot>F =  tsbiDom\<cdot>(SOME b. b \<in> ran (Rep_TSPF F))"
by(simp add: tspfRan_def)


(* In a chain all elements have the same Out-channel set *)
lemma tspfran_eq: assumes "x\<sqsubseteq>y"
  shows "tspfRan\<cdot>x = tspfRan\<cdot>y"
by (smt Abs_cfun_inverse2 assms someI_ex tspfRan_def tspf_below_ran tspf_ran_cont spf_ran_not_empty)


lemma part_ran: "ran (\<lambda>tb. (tsbiDom\<cdot>tb = cs) \<leadsto> g tb) = g ` dom (\<lambda>tb. (tsbiDom\<cdot>tb = cs) \<leadsto> g tb)"
apply rule
apply (smt domI image_eqI option.distinct(1) option.sel ran2exists subsetI)
by (smt domIff image_subsetI ranI)


lemma part_ran2: "ran (\<lambda>tb. (tsbiDom\<cdot>tb = cs) \<leadsto> g tb) = g ` TSBi cs"
apply(simp add: TSBi_def part_ran)
by (smt Collect_cong domI dom_def mem_Collect_eq)


lemma tspfdom2ran[simp]:  assumes "tspfDom\<cdot>f = tsbiDom\<cdot>tbi"
  shows "tsbiDom\<cdot>(f \<rightharpoonup> tbi) = tspfRan\<cdot>f"
apply(simp add: tspfran_insert)
by (metis assms domD option.sel ranI someI_ex tsbidom_dom tspf_ran2tsbdom)








(* Composition *)


lemma [simp]: "tspfCompIn f1 f2 \<subseteq> tspfCompAll f1 f2"
using tspfCompAll_def tspfCompIn_def by fastforce

lemma [simp]: assumes "c\<in>tspfCompIn f1 f2"
  shows "c\<in>tspfCompAll f1 f2"
using assms tspfCompAll_def tspfCompIn_def by fastforce





  (* allgemeine Domain lemmas *)

(* sending a TSB tb which contains a superset of the domain of the TSPF f1 through f1 surjectively
   covers the entire range of f1 *)
lemma tsbdom_2 [simp]: assumes "tspfDom\<cdot>f1 \<subseteq> tsbDom\<cdot>tb"
  shows "tsbiDom\<cdot>(f1 \<rightharpoondown> (tb \<bar> tspfDom\<cdot>f1)) = tspfRan\<cdot>f1"
proof -
  have "tsbiDom\<cdot>(tsb2tsbInf (tb \<bar> tspfDom\<cdot>f1)) = tspfDom\<cdot>f1" using assms tsb2tsbInf_dom tsresrict_dom2 by blast
  hence "(tsb2tsbInf (tb \<bar> tspfDom\<cdot>f1)) \<in> (dom (Rep_TSPF f1))"
    by (metis rep_tspfw_well someI spf_dom_not_empty tspf_type_def tspfw_well_def tspfdom_insert)
  thus ?thesis
    by (metis (no_types, lifting) domD option.sel ranI rep_tspfw_well someI_ex tspf_the_tsb_def tspf_type_def tspfw_well_def tspfran_insert) 
qed

lemma tsbidom_2 [simp]: assumes "tspfDom\<cdot>f1 \<subseteq> tsbDom\<cdot>tb"
  shows "tsbiDom\<cdot> f1 \<rightharpoonup> tsb2tsbInf (tb \<bar> tspfDom\<cdot>f1) = tspfRan\<cdot>f1"
by (metis assms tsbdom_2 tspf_the_tsb_def)



(* Lemmas über: comp_helper_inf *)


lemma comp_helper_dom[simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
  shows "tsbDom\<cdot>(comp_helper_inf i f1 f2 tb) = tspfCompAll f1 f2"
  apply(induction i)
  apply simp
  apply(subst comp_helper_inf.simps)
  apply(simp only: tsbiunion_dom Let_def tspfCompAll_def tsbttake_dom assms tspfCompIn_def)
  apply(simp add: inf_sup_ord(3) le_supI1)
  apply(auto simp add: assms tspfCompIn_def)
done

lemma comp_chain[simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2" and "comp_well f1 f2"
  shows "chain (\<lambda>i. comp_helper_inf i f1 f2 tb)"
apply(rule chainI)
apply(simp add: comp_helper_inf.simps Let_def)
apply(rule tsb_below)
apply (auto simp add: assms tspfCompAll_def tspfCompIn_def le_supI1)[1]
apply(case_tac "i=0")
apply simp
apply (auto simp add: assms tspfCompAll_def tspfCompIn_def le_supI1 comp_well_def)[1]
sorry



lemma comp_helper_commutative: assumes   "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
            and "tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}"
  shows "comp_helper_inf i f1 f2 tb = comp_helper_inf i f2 f1 tb" (is "?L i = _")
proof (induction i)
  case 0 thus ?case by (simp add: Un_left_commute inf_sup_aci(5) tspfCompAll_def)
next
  case (Suc i) 
  have f1_ran: "(tsbiDom\<cdot>(f1 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f1)))) = tspfRan\<cdot>f1" 
    by (simp add: assms(1) sup.coboundedI1 tspfCompAll_def)
  have f2_ran: "(tsbiDom\<cdot>(f2 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f2)))) = tspfRan\<cdot>f2"
    by (simp add: assms(1) le_supI1 tspfCompAll_def)
  hence "(f1 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f1))) \<uplus> (f2 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f2))) 
       = (f2 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f2))) \<uplus> (f1 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f1)))"
        using assms(2) f1_ran tsbiunion_commutative by blast

  hence "(tb \<uplus> f1 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f1))) \<uplus> (f2 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f2))) 
       = (tb \<uplus> f2 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f2))) \<uplus> (f1 \<rightharpoondown> ((?L i) \<bar> (tspfDom\<cdot>f1)))"
       by (simp only: tsbiunion_assoc)
  thus ?case by (metis Suc.IH comp_helper_inf.simps(2)) 
qed


  (* zuerst über domains *)



lemma comp_helper_dom_Lub [simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2" and "comp_well f1 f2"
  shows "tsbDom\<cdot>(\<Squnion>i. comp_helper_inf i f1 f2 tb) = tspfCompAll f1 f2"
using assms comp_chain tsbChain_dom_eq2 by fastforce

lemma tspfCompIn_getch1[simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
          and "c\<notin>tspfRan\<cdot>f1" and "c\<notin>tspfRan\<cdot>f2"
          and "c \<in>tspfCompIn f1 f2"
      shows "comp_helper_inf (Suc i) f1 f2 tb . c = tb  . c \<down>(Suc i)"
apply(simp add: comp_helper_inf.simps Let_def )
apply(auto simp add: assms(1) assms(4))
by (simp add: assms(1) assms(2) assms(3) subsetI tspfCompAll_def)


lemma tspfCompIn_getch[simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
          and "c\<notin>tspfRan\<cdot>f1" and "c\<notin>tspfRan\<cdot>f2"
          and "c\<in>tspfCompIn f1 f2"
      shows "comp_helper_inf i f1 f2 tb . c = tb . c \<down> i" (is "?L = ?R")
apply(cases "i=0")
apply(auto simp add: assms(1) assms(4))
by (metis Suc_pred assms tspfCompIn_getch1)

lemma tspfCompIn_restrict: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
          and "comp_well f1 f2"
  shows "comp_helper_inf i f1 f2 tb \<bar> tspfCompIn f1 f2 = tb \<down>  i" (is "?L = ?R")
proof (rule tsb_eq)
  show "tsbDom\<cdot>?L = tsbDom\<cdot>?R" by (auto simp add: assms(1))
  fix c
  assume "c\<in>tsbDom\<cdot>?L"
  hence "c\<in>tspfCompIn f1 f2" by (simp add: assms(1))
  hence "c\<notin>tspfRan\<cdot>f1"
    by (smt Diff_iff IntI Un_iff assms(2) comp_well_def disjoint_iff_not_equal tspfCompIn_def)
  hence "c\<notin>tspfRan\<cdot>f2"
    by (smt DiffE IntI Un_iff \<open>c \<in> tspfCompIn f1 f2\<close> assms(2) comp_well_def disjoint_iff_not_equal tspfCompIn_def)
  thus "?L .c = ?R.c"
    by (simp add: \<open>c \<in> tspfCompIn f1 f2\<close> \<open>c \<notin> tspfRan\<cdot>f1\<close> assms(1)) 
qed




lemma tspfCompIn_restrict_Lub [simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
          and "comp_well f1 f2"
  shows "(\<Squnion>i. comp_helper_inf i f1 f2 tb) \<bar> tspfCompIn f1 f2 = tsbInf2tsb\<cdot>tb" (is "?L = ?R")
proof -
  have "chain (\<lambda>i. comp_helper_inf i f1 f2 tb)" by (simp add: assms)
  hence "?L = (\<Squnion>i.  (tb \<down> i))"
    by (smt  assms(1) assms(2) contlub_cfun_arg lub_eq tspfCompIn_restrict)
  thus "?L = ?R"  by simp
qed

lemma tsbCompIn_getch[simp]: assumes "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
          and "comp_well f1 f2"
          and "c\<in>tspfCompIn f1 f2"
        shows "(\<Squnion>i. comp_helper_inf i f1 f2 tb).c = tb. c"
proof -
  have "(\<Squnion>i. comp_helper_inf i f1 f2 tb) . c = (\<Squnion>i. comp_helper_inf i f1 f2 tb . c)"
    by (simp add: assms(1) assms(2) contlub_cfun_arg contlub_cfun_fun) 
  hence "(\<Squnion>i. comp_helper_inf i f1 f2 tb) \<bar> tspfCompIn f1 f2  = tsbInf2tsb\<cdot>tb "
    using assms(1) assms(2) tspfCompIn_restrict_Lub by blast
  hence "((\<Squnion>i. comp_helper_inf i f1 f2 tb) \<bar> tspfCompIn f1 f2) . c   = tb .c" by simp
  thus ?thesis by (simp add: assms(3)) 
qed


lemma tspf_strongC: "tsbiDom\<cdot>tb = tspfDom\<cdot>f1 \<Longrightarrow> ((f1 \<rightharpoondown> ((tb) \<down> i)) . c) \<down> (Suc i) =  ((f1 \<rightharpoonup> tb) . c) \<down> (Suc i)"
apply(simp add: tspf_the_tsb_def)
sorry

(* shows the equivalence of an alternative definition of comp_helper_inf under certain conditions *)
lemma tspf_comp_helper_parallel: assumes "tspfCompInternal f1 f2 = {}"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
        and "c\<in>tspfRan\<cdot>f1"
     shows "(comp_helper_inf i f1 f2 tb) . c = (f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1)) .c \<down> i" (is "?L i = ?R i")
proof(induction i)
  case 0
  have "c\<in>tspfCompAll f1 f2"
    by (metis UnI1 Un_commute assms(4) tspfCompAll_def)
  thus ?case by simp
next
  case (Suc i)
  have int_subset: "tspfDom\<cdot>f1 \<subseteq> tspfCompIn f1 f2"
    using assms(1) tspfCompIn_def tspfCompInternal_def by fastforce 
  have "c\<notin>tspfRan\<cdot>f2" using assms(3) assms(4) comp_well_def by blast
  have "tsbDom\<cdot>(tsbInf2tsb\<cdot>tb) = tsbiDom\<cdot>tb" by simp
  hence int_1: "comp_helper_inf i f1 f2 tb \<bar> tspfCompIn f1 f2 = tb \<down> i"
    by (simp add: assms(2) assms(3) tspfCompIn_restrict)
  hence int_2: "comp_helper_inf i f1 f2 (tb) \<bar> tspfDom\<cdot>f1 = (tb) \<down> i \<bar> tspfDom\<cdot>f1"
    by (smt Diff_empty Rep_TSB_inverse Un_assoc assms(1) assms(2) comp_helper_dom part_eq rev_subsetD sup_ge1 tsbdom_insert tsbgetch_insert tsbgetch_restrict tspfCompAll_def tspfCompIn_def tspfCompInternal_def tsresrict_dom2)

  have int_c1:"c\<notin>tsbiDom\<cdot>((f2 \<rightharpoondown> ((comp_helper_inf i f1 f2 tb) \<bar> tspfDom\<cdot>f2)))" 
      by (simp add: \<open>(c::channel) \<notin> tspfRan\<cdot>(f2::'a TSPF)\<close> assms(2) le_supI1 tspfCompAll_def)

  have "c\<in>tsbDom\<cdot>((f1 \<rightharpoondown> ((comp_helper_inf i f1 f2 (tb)) \<bar> tspfDom\<cdot>f1)) \<down> Suc i)"
    by (simp add: assms(2) assms(4) int_2 int_subset)

   hence "?L (Suc i) = ((f1 \<rightharpoondown> ((comp_helper_inf i f1 f2 (tb)) \<bar> tspfDom\<cdot>f1)) \<down> Suc i) .c" 
    by (simp add: comp_helper_inf.simps Let_def int_c1)
  hence "?L (Suc i) = ((f1 \<rightharpoondown> (tb \<down> i  \<bar> tspfDom\<cdot>f1)) \<down> Suc i)  . c"
    using int_2 by presburger
  hence "?L (Suc i) = ((f1 \<rightharpoondown> (tb \<down> i  \<bar> tspfDom\<cdot>f1)))  . c  \<down> Suc i"
    by (metis Un_assoc assms(2) assms(4) comp_helper_dom int_2 sup_ge1 tsbdom_2 tsbittake_getch tspfCompAll_def)
  thus ?case 
    by (metis assms(2) int_subset tsb_ttake_restrict tsbiresrict_dom2 tspf_strongC) 
qed

  


(* tspfComp *)

thm tspfComp_def
lemma tspfComp_well [simp]: "tspfs_well (\<lambda> tb. (tsbiDom\<cdot>tb=(tspfCompIn f1 f2)) \<leadsto> 
      (tsb2tsbInf (\<Squnion>i. comp_helper_inf i f1 f2 tb) \<bar> tspfCompOut f1 f2))"
sorry

lemma tspfCompRan[simp]: "tspfRan\<cdot>(f1\<otimes>f2) = tspfCompOut f1 f2"
apply(simp add: tspfComp_def tspfran_insert)
sorry

lemma tspfCompDom[simp]: "tspfDom\<cdot>(f1\<otimes>f2) = tspfCompIn f1 f2"
apply(simp add: tspfComp_def tspfdom_insert)
sorry


(* carries over the result from tspf_comp_helper_parallel to infinite TSBs *)
lemma tspfComp_parallel: assumes "tspfCompInternal f1 f2 = {}"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
        and "c\<in>tspfRan\<cdot>f1"
shows "(\<Squnion>i. comp_helper_inf i f1 f2 tb). c =  f1 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f1). c" 
proof -
  have "\<And>i. (comp_helper_inf i f1 f2 tb . c)  = f1 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f1) .c \<down> i"
    by (simp add: assms tspf_comp_helper_parallel)
  thus ?thesis by (simp add: assms(2) assms(3) contlub_cfun_arg contlub_cfun_fun)
qed

lemma compInf [simp]: "tsb2tsbInf (\<Squnion>i. comp_helper_inf i f1 f2 tb) . c  = (\<Squnion>i. comp_helper_inf i f1 f2 tb) . c"
sorry

lemma comp_well_commu: "comp_well f1 f2 \<Longrightarrow> comp_well f2 f1"
by (simp add: Int_commute comp_well_def)

lemma comp_internal_commu: "tspfCompInternal f1 f2 = tspfCompInternal f2 f1"
by (simp add: sup_commute tspfCompInternal_def)

lemma comp_in_commu: "tspfCompIn f1 f2 = tspfCompIn f2 f1"
by (simp add: inf_sup_aci(5) tspfCompIn_def)

lemma tspfComp_parallelAll: assumes "tspfCompInternal f1 f2 = {}"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
shows "tsb2tsbInf (\<Squnion>i. comp_helper_inf i f1 f2 tb) =  tb \<uplus> (f1 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f1)) \<uplus> (f2 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f2))"   
          (is "?L = ?R")
proof (rule tsbi_eq)
  have l_dom: "tsbiDom\<cdot>?L = tspfCompAll f1 f2" by (simp add: assms(2) assms(3))
  have r_dom: "tsbiDom\<cdot>?R = tspfCompAll f1 f2"
    by (metis Diff_empty assms(1) assms(2) sup_ge1 sup_ge2 tsbiresrict_dom2 tsbiunion_dom tspfCompAll_def tspfCompIn_def tspfCompInternal_def tspfdom2ran)
  show "tsbiDom\<cdot>?L = tsbiDom\<cdot>?R" using l_dom r_dom by blast 

  fix c
  assume "c\<in>tsbiDom\<cdot>?L"
  hence c_all: "c\<in>tspfCompAll f1 f2" using l_dom by blast
  thus "?L .c = ?R .c"
  proof (cases "c\<in>tspfCompIn f1 f2")
    case True 
    hence c_nf1: "c\<notin>tspfRan\<cdot>f1"
      by (metis DiffD2 Diff_empty IntI Un_iff assms(1) assms(3) comp_well_def tspfCompIn_def tspfCompInternal_def)
    hence c_nf2: "c\<notin>tspfRan\<cdot>f2"
      by (metis True DiffD2 Diff_empty IntI Un_iff assms(1) assms(3) comp_well_def tspfCompIn_def tspfCompInternal_def)
   
    hence r_i: "?R . c = tb .c"
      by (metis (no_types, lifting) Diff_empty Int_commute Un_commute assms(1) assms(2) c_nf1 inf_sup_absorb tsbirestrict_dom3 tsbiunion_getchL tspfCompIn_def tspfCompInternal_def tspfdom2ran)
    have "(\<Squnion>i. comp_helper_inf i f1 f2 tb) . c = tb .c" using True assms(2) assms(3) by auto
    thus ?thesis using r_i by simp
  next
    case False
    note c_notIn = this
    thus ?thesis
    proof (cases "c\<in>tspfRan\<cdot>f1")    
      case True 
      have c_nf2: "c\<notin>tspfRan\<cdot>f2" using True assms(3) comp_well_def by blast
      hence "?R . c = (f1 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f1)) . c"
        by (metis (no_types, lifting) Diff_empty Int_commute True Un_commute assms(1) assms(2) inf_sup_absorb tsbirestrict_dom3 tsbiunion_getchL tsbiunion_getchR tspfCompIn_def tspfCompInternal_def tspfdom2ran)
      thus ?thesis by(simp add: tspfComp_parallel assms True)
    next
      case False
      hence c_f2: "c\<in>tspfRan\<cdot>f2"
        by (metis Diff_empty UnE assms(1) c_all c_notIn tspfCompAll_def tspfCompIn_def tspfCompInternal_def)
      hence r_2: "?R . c = (f2 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f2)) . c"
        by (metis Diff_empty assms(1) assms(2) inf_sup_ord(4) tsbiresrict_dom2 tsbiunion_getchR tspfCompIn_def tspfCompInternal_def tspfdom2ran)
      have "(\<Squnion>i. comp_helper_inf i f1 f2 tb) . c = (f2 \<rightharpoonup> (tb \<bar> tspfDom\<cdot>f2)) . c"
        by (metis (no_types, lifting) assms(1) assms(2) assms(3) c_f2 comp_helper_commutative comp_in_commu comp_internal_commu comp_well_commu comp_well_def image_cong tspfComp_parallel)
      thus ?thesis using r_2 by auto
   qed
 qed
qed



thm tspfComp_def
lemma tspfCompParallelGetch: assumes "tspfCompInternal f1 f2 = {}"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
        and "c\<in>tspfRan\<cdot>f1"
        shows "(f1\<otimes>f2) \<rightharpoonup> tb . c = f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1) . c"
proof -
  have c_out: "c\<in>tspfCompOut f1 f2" using assms(1) assms(4) tspfCompInternal_def tspfCompOut_def by fastforce
  have "(\<Squnion>i. comp_helper_inf i f1 f2 tb) . c = f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1) . c"
    using assms(1) assms(2) assms(3) assms(4) tspfComp_parallel by blast
  hence "tsb2tsbInf (\<Squnion>i. comp_helper_inf i f1 f2 tb) . c = f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1) . c" by simp
  thus ?thesis by(simp add: tspfComp_def assms c_out)
qed

lemma tspfCompCommu: assumes "comp_well f1 f2"
  shows "(f1 \<otimes> f2) = (f2\<otimes>f1)"
sorry

lemma tspfCompParallelGetch2: assumes "tspfCompInternal f1 f2 = {}"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
        and "c\<in>tspfRan\<cdot>f2"
        shows "(f1\<otimes>f2) \<rightharpoonup> tb . c = f2 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f2) . c"
by (metis assms(1) assms(2) assms(3) assms(4) comp_in_commu comp_internal_commu comp_well_commu tspfCompCommu tspfCompParallelGetch)



(* Teste die Composition *)
(* variante 1: Keine internen channels *)
lemma tspfCompParallel: assumes "tspfCompInternal f1 f2 = {}"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
  shows "(f1\<otimes>f2) \<rightharpoonup> tb = (f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1)) \<uplus>  (f2 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f2))" (is "?L = ?R")
proof (rule tsbi_eq)
  have comp_out: "tspfCompOut f1 f2 = tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2"
    using assms(1) tspfCompInternal_def tspfCompOut_def by fastforce
  thus "tsbiDom\<cdot>?L = tsbiDom\<cdot>?R"
    by (metis Diff_empty assms(1) assms(2) sup.cobounded1 sup_ge2 tsbiresrict_dom2 tsbiunion_dom tspfCompDom tspfCompIn_def tspfCompInternal_def tspfCompRan tspfdom2ran)
  
  fix c
  assume "c \<in> tsbiDom\<cdot>?L"
  hence "c\<in>tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2" by (simp add: assms(2) tspfCompOut_def)
  hence c_def: "c\<in>tspfCompOut f1 f2" using comp_out by blast
  thus "?L . c = ?R . c"
  proof (cases "c \<in>tspfRan\<cdot>f1")
    case True thus ?thesis
      by (metis Diff_empty assms(1) assms(2) assms(3) sup_ge2 tsbiresrict_dom2 tsbiunion_getchL tsbiunion_getchR tspfCompIn_def tspfCompInternal_def tspfCompParallelGetch tspfCompParallelGetch2 tspfdom2ran)
   next
    case False thus ?thesis
      by (metis Diff_empty UnE \<open>(c::channel) \<in> tspfRan\<cdot>(f1::'a TSPF) \<union> tspfRan\<cdot>(f2::'a TSPF)\<close> assms(1) assms(2) assms(3) sup_ge2 tsbiresrict_dom2 tsbiunion_getchR tspfCompIn_def tspfCompInternal_def tspfCompParallelGetch2 tspfdom2ran)
   qed
qed


lift_definition tspfEmpty :: "'m TSPF" is "[Abs_TSB_inf Map.empty \<mapsto> Abs_TSB_inf Map.empty]"
by (simp add: tspfw_well_exists)

lemma [simp]: "tspfDom\<cdot>tspfEmpty = {}"
apply(simp add: tspfdom_insert tspfEmpty.rep_eq)
by (simp add: tsbidom_insert tsb_inf_well_def)

lemma [simp]: "tspfRan\<cdot>tspfEmpty = {}"
apply(simp add: tspfran_insert tspfEmpty.rep_eq)
by(simp add: tsbidom_insert tsb_inf_well_def)


(*
lemma  assumes"tsbiDom\<cdot>tb = tspfCompIn tspfEmpty tspfEmpty"
          and "\<forall>c \<in> dom (Rep_TSB_inf tb). #\<surd>(f\<rightharpoonup>c) = \<infinity>"
  shows "(\<Squnion>i. comp_helper_inf i tspfEmpty tspfEmpty tb) = tb"
proof -
  have "tsbDom\<cdot>tb = {}" by(simp add: assms(1) tspfCompIn_def)
  thus ?thesis apply(subst comp_helper_inf_def)
thm part_eq
lemma assumes "tspfCompInternal f1 f2 = {}" 
          and "tsbDom\<cdot>tb = tspfCompIn f1 f2"
          and "\<forall>c \<in> dom (Rep_TSB tb). #\<surd>(f\<rightharpoonup>c) = \<infinity>"
  shows "(\<Squnion>i. comp_helper_inf i f1 f2 tb) = tb"

thm comp_helper_inf_def
*)





(*


(*old *)
lemma ex_restrict [simp]: assumes "cs1\<inter>cs2 = {}" and "\<forall>x. tsbiDom\<cdot>(f x) = cs1"
  shows "\<exists>z. z \<bar> cs1 = f (z\<bar>cs2)"
by (metis assms(1) assms(2) tsbunion_restrict tsbunion_restrict2)

lemma dom2tspfDom: assumes "b\<in> dom (Rep_TSPF f1)"
  shows "tsbiDom\<cdot>b = tspfDom\<cdot>f1"
by (metis assms rep_tspfs_well someI_ex tspfs_well_def2 tspfdom_insert)
  
lemma dom2tspfRan: assumes "b\<in> dom (Rep_TSPF f1)"
  shows "tsbiDom\<cdot>(Rep_TSPF f1)\<rightharpoonup>b = tspfRan\<cdot>f1"
by (metis (mono_tags, lifting) assms domI option.sel ran2exists rep_tspfs_well someI_ex spf_ran_not_empty tspfs_well_def2 tspfran_insert)

lemma tspfdom_eq: "(tsbiDom\<cdot>b = tspfDom\<cdot>f1) \<longleftrightarrow> b \<in> dom (Rep_TSPF f1)"
by (metis dom2tspfDom spf_dom_not_empty tspf_tsbdom2dom)
   
lemma test: "\<exists>s. s \<uplus> input \<bar> (tsbiDom\<cdot>input) = input"
by simp


(* ?z \<bar> (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 - (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 \<union> tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1)) = input \<and>
    ?z \<bar> tspfRan\<cdot>f1 = Rep_TSPF f1\<rightharpoonup>?z \<bar> tspfDom\<cdot>f1 \<and>
    ?z \<bar> tspfRan\<cdot>f2 = Rep_TSPF f2\<rightharpoonup>?z \<bar> tspfDom\<cdot>f2 \<and> tsbiDom\<cdot>?z = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 \<union> tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2
*)

lemma [simp]: assumes "tsbiDom\<cdot>input = cs"
  shows "s \<uplus> input \<bar> cs = input"
using assms tsbunion_restrict2 by blast

lemma [simp]: "tsbiDom\<cdot>(tb1 \<uplus> tb2) = tsbiDom\<cdot>tb1 \<union> tsbiDom\<cdot>tb2"
by(simp add: tsbunion_insert tsbdom_insert Un_commute)

thm ex_restrict

lemma ex_restrict2 [simp]: assumes "tspfDom\<cdot>f1\<inter>tspfRan\<cdot>f1 = {}"
  shows "\<exists>z. z \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>(z \<bar> tspfDom\<cdot>f1)"
by (metis (no_types, lifting) Abs_cfun_inverse2 assms dom2tspfRan tsbunion_commutative tsbunion_restrict2 tspfDom_def tspf_dom_cont tspfdom_eq)

lemma ex_restrict3 [simp]: assumes "tspfDom\<cdot>f1\<inter>tspfRan\<cdot>f1 = {}"
  shows "\<exists>z. z \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>(z \<bar> tspfDom\<cdot>f1) \<and> tsbiDom\<cdot>z = (tspfDom\<cdot>f1 \<union> tspfRan\<cdot>f1)"
proof -
  obtain input where in_def: "tsbiDom\<cdot>input = tspfDom\<cdot>f1" by (simp add: tspfdom_insert)
  obtain out where out_def: "out = (Rep_TSPF f1)\<rightharpoonup>input" by simp
  hence "tsbiDom\<cdot>out = tspfRan\<cdot>f1" using \<open>tsbiDom\<cdot>input = tspfDom\<cdot>f1\<close> dom2tspfRan tspfdom_eq by auto
  hence "(input\<uplus>out) \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>((input\<uplus>out) \<bar> tspfDom\<cdot>f1)"
    by (metis assms in_def out_def tsbunion_commutative tsbunion_restrict2)
  thus ?thesis using \<open>tsbiDom\<cdot>out = tspfRan\<cdot>f1\<close> in_def tsbunion_dom by blast 
qed


lemma [simp]: assumes "z1 \<bar> tspfRan\<cdot>f = (Rep_TSPF f)\<rightharpoonup>(z1 \<bar> tspfDom\<cdot>f)" and "tspfDom\<cdot>f \<subseteq> tsbiDom\<cdot>z1"
  shows "tspfRan\<cdot>f \<subseteq> tsbiDom\<cdot>z1"
by (metis assms(1) assms(2) dom2tspfRan tspfdom_eq tsresrict_dom2 tsrestrict_dom)

lemma ex_restrictNoInternal [simp]: assumes "tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}"
                               and "tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {}"
                               and "(tspfDom\<cdot>f1\<union>tspfRan\<cdot>f1) \<inter> (tspfDom\<cdot>f2\<union>tspfRan\<cdot>f2) = {}"
  shows "\<exists>z. z \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>(z \<bar> tspfDom\<cdot>f1) \<and>
             z \<bar> tspfRan\<cdot>f2 = (Rep_TSPF f2)\<rightharpoonup>(z \<bar> tspfDom\<cdot>f2)" (is "\<exists>z. ?F z")
proof -
  obtain z1 where z1_def: "z1 \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>(z1 \<bar> tspfDom\<cdot>f1) \<and> tsbiDom\<cdot>z1 = tspfDom\<cdot>f1\<union>tspfRan\<cdot>f1"
    using assms(1) ex_restrict3 by blast 
  obtain z2 where z2_def: "z2 \<bar> tspfRan\<cdot>f2 = (Rep_TSPF f2)\<rightharpoonup>(z2 \<bar> tspfDom\<cdot>f2) \<and> tsbiDom\<cdot>z2 = tspfDom\<cdot>f2\<union>tspfRan\<cdot>f2"
    using assms(2) ex_restrict3 by blast 
  hence "(z1 \<uplus> z2) \<bar> (tspfDom\<cdot>f1\<union>tspfRan\<cdot>f1) = z1" by (metis assms(3) inf_sup_aci(1) tsbunion_restrict3 z1_def)  
  hence "?F (z1 \<uplus> z2)"
    by (smt Abs_TSB_inverse Int_absorb1 mem_Collect_eq restrict_restrict sup_ge1 sup_ge2 tsbrestrict_insert tsbrestrict_well tsbunion_restrict2 z1_def z2_def)
  thus ?thesis by blast
qed

lemma ex_restrict [simp]: assumes "tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}"
                               and "tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {}"
                               and "tspfDom\<cdot>f1 \<inter> tspfDom\<cdot>f2 = {}" 
                               and "tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}" 
  shows "\<exists>z. z \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>(z \<bar> tspfDom\<cdot>f1) \<and>
             z \<bar> tspfRan\<cdot>f2 = (Rep_TSPF f2)\<rightharpoonup>(z \<bar> tspfDom\<cdot>f2)" (is "\<exists>z. ?F z")
proof -
  obtain Internalf1_f2 where "Internalf1_f2 = tspfRan\<cdot>f1 \<inter> tspfDom\<cdot>f2"  (* channels from f1 to f2 *)
    by simp
  obtain Internalf2_f1 where "Internalf2_f1 = tspfRan\<cdot>f2 \<inter> tspfDom\<cdot>f1"  (* channels from f2 to f1 *)
    by simp
oops




lemma tspfCompHelper2_Exists:
    assumes  "tspfDom\<cdot>f1 \<inter> tspfDom\<cdot>f2 = {}" 
        and  "tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}" 
        and  "tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}"
        and  "tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {}"
        and "tsbiDom\<cdot>input = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)-((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
shows "\<exists>z. tspfCompHelpersHelper f1 f2 input z"
proof -
  have "\<exists>s. s \<bar> tspfRan\<cdot>f1 = (Rep_TSPF f1)\<rightharpoonup>((s) \<bar> tspfDom\<cdot>f1)" by (simp add: assms(3))
  have "\<exists>s. tspfCompHelpersHelper f1 f2 input (s\<uplus>input)"  sorry
  thus ?thesis by blast 
qed

lemma tspfCompHelper2_dom: assumes "tb \<in> dom (tspfCompHelper2 f1 f2)"
  shows "tsbiDom\<cdot>tb = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)-((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
using assms apply(simp add: tspfCompHelper2_def Let_def)
by (smt domIff)

lemma tspfCompHelper_dom: assumes "tb \<in> dom (tspfCompHelper f1 f2)"
  shows "tsbiDom\<cdot>tb = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)-((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
using assms apply(simp add: tspfCompHelper_def Let_def)
by (smt domIff)



(* neu*)


lemma tspfCompHelper2_ran: assumes "tb \<in> ran (tspfCompHelper2 f1 f2)"
               and  "tspfDom\<cdot>f1 \<inter> tspfDom\<cdot>f2 = {}" 
               and  "tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}" 
  shows "tsbiDom\<cdot>tb = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2 -(tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 \<union> tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
using assms apply(simp add: tspfCompHelper2_def Let_def)
oops

lemma tspfCompHelper_ran: assumes "tb \<in> ran (tspfCompHelper f1 f2)"
  shows "tsbiDom\<cdot>tb = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2 -(tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 \<union> tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
using assms apply(simp add: tspfCompHelper_def Let_def)
sorry

lemma tspfcomp_well [simp]: "tspfs_well (tspfCompHelper f1 f2)"
apply(rule tspfs_wellI)
using tspfCompHelper_dom apply simp
apply(simp add: tspfCompHelper_def Let_def domIff)
using tspfCompHelper_ran by simp





lemma tspfcomp_dom : "tspfDom\<cdot>(f1\<otimes>f2) = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) 
            - ((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
sorry
(*proof-
  have "\<And> tb. tb\<in>dom (tspfCompHelper f1 f2) \<Longrightarrow> tspfDom\<cdot>(f1\<otimes>f2) = tsbiDom\<cdot>tb"
    by (metis Abs_TSPF_inverse mem_Collect_eq someI_ex tspfComp_def tspfs_well_def tspfcomp_well tspfdom_insert)
  thus ?thesis by (metis Abs_TSPF_inverse mem_Collect_eq spf_dom_not_empty tspfCompHelper_dom tspfcomp_well) 
qed *)

lemma tspfcomp_ran : "tspfRan\<cdot>(f1\<otimes>f2) = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2 -(tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 \<union> tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f1))"
sorry
(*proof -
 have "\<And> tb. tb\<in>ran (tspfCompHelper f1 f2) \<Longrightarrow> tspfRan\<cdot>(f1\<otimes>f2) = tsbiDom\<cdot>tb"
  by (metis Abs_TSPF_inverse mem_Collect_eq someI_ex tspfComp_def tspf_ran2tsbdom tspfcomp_well tspfran_insert)
  thus ?thesis
    by (metis Abs_TSPF_inverse mem_Collect_eq spf_ran_not_empty tspfCompHelper_ran tspfcomp_well) 
qed *)

lemma tspg_compHelper_commutative: "tspfCompHelpersHelper f1 f2 inp z = tspfCompHelpersHelper f2 f1 inp z"
apply(simp add: tspfCompHelpersHelper_def Let_def)
by (smt sup_assoc sup_commute)

(* composit operator is commutative *)
lemma tspfcomp_commute: "(a \<otimes> b) = (b \<otimes> a)"
apply(simp add: tspfComp_def tspfCompHelper_def tspfCompHelper2_def Let_def)
sorry
(*apply(simp add: tspfComp_def tspfCompHelper_def Let_def)
by (metis Collect_conj_eq Int_commute Un_commute setcompr_eq_image) *)


lemma [simp]: "tspfs_well (tspfCompHelper2 f1 f2)"
sorry
(* toDo: composite operator is associative *)
  (* stronger / different assumtions needed \<Or>? *)
lemma tspf_comp_domp: assumes "tspfDom\<cdot>a \<inter> tspfDom\<cdot>b = {}"
       and     "tspfDom\<cdot>b \<inter> tspfDom\<cdot>c = {}"
     shows "tspfDom\<cdot>((a \<otimes> b) \<otimes> c) = tspfDom\<cdot>(a \<otimes> (b \<otimes> c))"
using assms by(auto simp add: tspfcomp_dom tspfcomp_ran)

lemma  tspf_comp_ran: assumes (* "tspfDom\<cdot>a \<inter> tspfDom\<cdot>b = {}" *)
              (* and "tspfDom\<cdot>b \<inter> tspfDom\<cdot>c = {}"*)
               (*and "tspfDom\<cdot>a \<inter> tspfDom\<cdot>c = {}"*)
                 "tspfRan\<cdot>a \<inter> tspfRan\<cdot>b = {}" 
               and  "tspfRan\<cdot>b \<inter> tspfRan\<cdot>c = {}" 
              (* and "tspfRan\<cdot>a \<inter> tspfRan\<cdot>c = {}" *)
     shows "tspfRan\<cdot>((a \<otimes> b) \<otimes> c) = tspfRan\<cdot>(a \<otimes> (b \<otimes> c))"
using assms by(auto simp add: tspfcomp_dom tspfcomp_ran)

lemma assumes  "tspfDom\<cdot>a \<inter> tspfDom\<cdot>b = {}" 
               and "tspfDom\<cdot>b \<inter> tspfDom\<cdot>c = {}"
               and "tspfDom\<cdot>a \<inter> tspfDom\<cdot>c = {}"
                 "tspfRan\<cdot>a \<inter> tspfRan\<cdot>b = {}" 
               and  "tspfRan\<cdot>b \<inter> tspfRan\<cdot>c = {}" 
               and "tspfRan\<cdot>a \<inter> tspfRan\<cdot>c = {}" 
     shows "Rep_TSPF ((a \<otimes> b) \<otimes> c) = Rep_TSPF (a \<otimes> (b \<otimes> c))"
apply(auto simp add: tspfComp_def)
apply(simp add: tspfCompHelper2_def Let_def)
oops



*)

  cpodef 'm TSPFs = "{F :: 'm TSB_inf \<rightharpoonup> 'm TSB_inf. tspfs_well F}"
  using tspfs_well_exists apply blast
  using tsbi_option_adm by blast

 setup_lifting type_definition_TSPFs





end