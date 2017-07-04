(*  Title:        TSPSTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  
*)
theory TSPS
imports TSPF

begin
  default_sort message




(* ----------------------------------------------------------------------- *)
  subsection \<open>Definition of "Timed Stream Processing Specifications"\<close>
(* ----------------------------------------------------------------------- *)

definition tsps_well :: "'m TSPF set \<Rightarrow> bool" where
"tsps_well S \<equiv> \<exists>In Out. \<forall> f\<in>S . (tspfDom\<cdot>f = In \<and> tspfRan\<cdot>f=Out) "

lemma tsps_wellI: assumes "\<And>f. f \<in> S \<Longrightarrow> tspfDom\<cdot>f = In"
                      and "\<And>f. f \<in> S \<Longrightarrow> tspfRan\<cdot>f = Out"
                  shows "tsps_well S"
using assms by(auto simp add: tsps_well_def)

lemma [simp]: "tsps_well {}"
by(simp add: tsps_well_def)

lemma tsps_subset_well: assumes "A \<subseteq> B" and "tsps_well B"
  shows "tsps_well A"
by (meson assms(1) assms(2) subset_iff tsps_well_def)

lemma tsps_dom_eq: assumes "a1\<in>A" and "a2\<in>A" and "tsps_well A"
  shows "tspfDom\<cdot>a1 = tspfDom\<cdot>a2"
by (metis assms(1) assms(2) assms(3) tsps_well_def)

lemma tsps_ran_eq: assumes "a1\<in>A" and "a2\<in>A" and "tsps_well A"
  shows "tspfRan\<cdot>a1 = tspfRan\<cdot>a2"
by (metis assms(1) assms(2) assms(3) tsps_well_def)


lemma chain_notEmpty: assumes "chain Y" and "Y i \<noteq> {}" and "i\<le>j"
  shows "Y j \<noteq>{}"
proof -
  have "Y i \<subseteq> Y j" by (metis assms(1) assms(3) po_class.chain_mono set_cpo_simps(1))
  thus ?thesis using assms(2) by blast 
qed

lemma tsps_well_adm1: assumes "chain Y" and "Y 0 \<noteq> {}" and "\<And>i. tsps_well (Y i)"
  shows "tsps_well (\<Union>i. Y i)"
proof(rule tsps_wellI)
  fix f
  assume as_f: "f\<in>(\<Union>i. Y i)"
  obtain i where i_def: "f\<in>Y i" using as_f by blast
  thus "tspfDom\<cdot>f = tspfDom\<cdot>(SOME a. a\<in>(Y 0))"
    by (metis assms(1) assms(2) assms(3) contra_subsetD le0 po_class.chain_mono set_cpo_simps(1) 
              some_in_eq tsps_dom_eq)
  thus "tspfRan\<cdot>f = tspfRan\<cdot>(SOME a. a\<in>(Y 0))"
    by (metis i_def assms(1) assms(2) assms(3) contra_subsetD le0 po_class.chain_mono 
              set_cpo_simps(1) some_in_eq tsps_ran_eq)
qed




lemma tsps_well_adm[simp]: "adm tsps_well"
proof(rule admI)
  fix Y :: "nat \<Rightarrow> 'a TSPF set"
  assume as1: "chain Y" and as2: "\<forall>i. tsps_well (Y i)"
  hence "tsps_well (\<Union>i. Y i)"  
  proof (cases "(\<Union>i. Y i) = {}")
    case True thus ?thesis by simp
  next
    case False
    obtain k where k_def: "Y k\<noteq>{}" using False by auto
    hence chain_d: "chain (\<lambda>i. Y (i + k))" (is "chain ?D") by (simp add: as1 po_class.chainE 
                                                                         po_class.chainI)
    have "\<And>i. ?D i \<noteq> {}" using as1 chain_notEmpty k_def le_add2 by blast
    hence "tsps_well (\<Union>i. ?D i)" using as2 chain_d tsps_well_adm1 by blast
    thus ?thesis by (metis as1 lub_range_shift set_cpo_simps(2)) 
  qed
  thus "tsps_well (\<Squnion>i. Y i)" by (metis set_cpo_simps(2)) 
qed


(* Timed Stream Processing Specifications *)
pcpodef 'm TSPS = "{S :: 'm TSPF set . tsps_well S }"
by (auto simp add: UU_eq_empty)


setup_lifting type_definition_TSPS




(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Definition on TSPS\<close>
(* ----------------------------------------------------------------------- *)

definition tspsDom :: "'m TSPS \<Rightarrow> channel set" where
"tspsDom S = tspfDom\<cdot>(SOME f. f\<in> Rep_TSPS S)"

definition tspsRan :: "'m TSPS \<Rightarrow> channel set" where
"tspsRan S = tspfRan\<cdot>(SOME f. f\<in> Rep_TSPS S)"

(*
definition tspsComp :: "'m TSPS \<Rightarrow> 'm TSPS \<Rightarrow> 'm TSPS" (infixl "\<Otimes>" 50) where 
"tspsComp S1 S2 \<equiv> let repS1 = Rep_TSPS S1;
                      repS2 = Rep_TSPS S2     in
                  Abs_TSPS {f1 \<otimes> f2 | f1 f2. f1\<in>repS1 \<and> f2\<in>repS2}"
*)



(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Lemmas on TSPS\<close>
(* ----------------------------------------------------------------------- *)

lemma tsps_eq: assumes "\<And>f1 . f1\<in>(Rep_TSPS S1) \<Longrightarrow> f1\<in>(Rep_TSPS S2)" 
      and "\<And>f2 . f2\<in>(Rep_TSPS S2) \<Longrightarrow> f2\<in>(Rep_TSPS S1)"
  shows "S1 = S2"
by (metis (full_types) Rep_TSPS_inverse assms(1) assms(2) equalityI subsetI)


lemma [simp]: assumes "tsps_well x" 
  shows "Rep_TSPS (Abs_TSPS x) = x"
by (simp add: Abs_TSPS_inverse assms)

lemma [simp]: "tsps_well (Rep_TSPS x)"
using Rep_TSPS by blast


lemma tsps_rep_mono [simp]: "monofun Rep_TSPS"
apply(rule monofunI)
by (simp add: below_TSPS_def)

lemma tsps_rep_cont [simp]: "cont Rep_TSPS"
apply(rule contI2)
apply simp
apply auto
  by (metis (mono_tags, lifting) Abs_TSPS_inverse Rep_TSPS adm_def below_TSPS_def eq_imp_below 
            image_cong lub_TSPS mem_Collect_eq po_class.chain_def tsps_well_adm)

lemma "S \<noteq> \<bottom> \<Longrightarrow> Rep_TSPS S \<noteq> {}"
using Rep_TSPS_bottom_iff UU_eq_empty by fastforce




lemma tspsdom_eq: assumes "S1\<noteq>\<bottom>" and "S1\<sqsubseteq>S2"
  shows "tspsDom S1 = tspsDom S2"
proof -
  { fix tt :: "'a TSPF"
    have "\<And>t. tsps_well (Rep_TSPS (t::'a TSPS))"
      using Rep_TSPS by blast
    then have "tspfDom\<cdot>(SOME t. t \<in> Rep_TSPS S1) = tspfDom\<cdot>(SOME t. t \<in> Rep_TSPS S2) 
                \<or> tt \<in> Rep_TSPS S1 \<and> tt \<in> Rep_TSPS S2 \<or> tt \<notin> Rep_TSPS S1 \<and> tt \<notin> Rep_TSPS S2"
      by (metis Abs_TSPS_strict Rep_TSPS_inverse SetPcpo.less_set_def UU_eq_empty assms(1) assms(2) 
                below_TSPS_def contra_subsetD empty_iff some_in_eq tsps_dom_eq) }
  then have "tspfDom\<cdot>(SOME t. t \<in> Rep_TSPS S1) = tspfDom\<cdot>(SOME t. t \<in> Rep_TSPS S2)"
    by meson
  thus ?thesis by(simp add: tspsDom_def)
qed

lemma tsps_allDom: "\<exists>In. \<forall>f\<in>Rep_TSPS S1. tspfDom\<cdot>f=In"
using tsps_well_def by fastforce

  (*
lemma assumes "tsps_well S1" and "tsps_well S2" 
  shows "\<exists>In. \<forall>f1\<in>S1. \<forall> f2\<in>S2. tspfCompIn f1 f2 = In"
  apply(cases "S1 = {} \<or> S2 = {}")
   apply blast
  apply rule+
   apply (auto simp add: tspfCompIn_def)
    oops

lemma tspsComp_well [simp]: "tsps_well {f1 \<otimes> f2 | f1 f2. f1\<in> (Rep_TSPS S1) \<and> f2\<in>(Rep_TSPS S2)}"
  apply(cases "S1 = \<bottom> \<or> S2 = \<bottom>")
   apply (smt Collect_empty_eq Rep_TSPS Rep_TSPS_strict UU_eq_empty bot_set_def mem_Collect_eq)
  apply(rule tsps_wellI)
   apply auto
   apply (auto simp add: tspfCompIn_def)
sorry
*)

lemma "X= Y \<Longrightarrow> Abs_TSPS X=Abs_TSPS Y"
  by simp

thm Rep_TSPS_inject

  (*
(* composite operator in TSPS is commutative *)
lemma tspscomp_commute: "(X \<Otimes> Y) = (Y \<Otimes> X)"
apply(simp add: tspsComp_def)

sorry

(* The empty-specification composed with anything is again empty *)
lemma [simp]: "(Abs_TSPS {}) \<Otimes> X = (Abs_TSPS {})"
by(simp add: tspsComp_def tsps_well_def)

(* on one-element sets the \<Otimes>-operator behaves exactly like \<otimes> *)
lemma [simp]: "(Abs_TSPS {f1}) \<Otimes> (Abs_TSPS {f2}) = Abs_TSPS{f1\<otimes>f2}"
by(simp add: tspsComp_def tsps_well_def)

*)


end
