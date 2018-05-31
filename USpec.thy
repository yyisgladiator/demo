(*  Title:        USpec
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "universal specification" 
*)

theory USpec
  imports UnivClasses SetRev
begin

default_sort ufuncl

(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
fun uspecWell :: "'m set rev \<Rightarrow> channel set discr \<Rightarrow> channel set discr \<Rightarrow> bool" where
"uspecWell (Rev S) (Discr csIn) (Discr csOut)  = (\<forall> f\<in>S . (ufclDom\<cdot>f = csIn \<and> ufclRan\<cdot>f=csOut) )"
(* define a Set of 'm SPF's. all SPS in a set must have the same In/Out channels *)


(* Every "empty" uspec is allowed *)
lemma uspecwell_exists: "uspecWell (Rev {}) csIn csOut"
  using uspecWell.elims(3) by fastforce

(* Required for cpodef proof *)
lemma uspecwell_adm: "adm (\<lambda>x::'m set rev \<times> channel set discr \<times> channel set discr.
            x \<in> {(S::'m set rev, csIn::channel set discr, csOut::channel set discr). uspecWell S csIn csOut})"
proof(rule admI)
  fix Y::"nat \<Rightarrow> 'm set rev \<times> channel set discr \<times> channel set discr"
  assume chainY: "chain Y" and 
    allWell: "\<forall>i::nat. Y i \<in> {(S::'m set rev, csIn::channel set discr, csOut::channel set discr). uspecWell S csIn csOut}"

  obtain csIn where csIn_def: "\<forall>i::nat. (Discr csIn) = (fst (snd (Y i)))"
    by (metis chainY discr.exhaust discrete_cpo fst_conv is_ub_thelub old.prod.inject snd_conv snd_monofun surj_pair)
  obtain csOut where csOut_def: "\<forall>i::nat. (Discr csOut) = (snd (snd (Y i)))"
    by (metis chainY discr.exhaust discrete_cpo fst_conv is_ub_thelub old.prod.inject snd_conv snd_monofun surj_pair)

  have h1: "fst (Y 0 ) \<sqsubseteq> fst (\<Squnion>i::nat. Y i)"
    using chainY fst_monofun is_ub_thelub by blast
  hence h2: "((inv Rev) (fst (\<Squnion>i::nat. Y i))) \<subseteq> ((inv Rev) (fst (Y 0 )))"
    by (metis below_rev.elims(2) inv_rev_rev set_cpo_simps(1))
  show "(\<Squnion>i::nat. Y i) \<in> {(S::'m set rev, csIn::channel set discr, csOut::channel set discr). uspecWell S csIn csOut}" 
  proof(cases "fst (\<Squnion>i::nat. Y i) = Rev {}")
    case True
    then show ?thesis
      using uspecWell.elims(3) by fastforce
  next
    case False
    then show ?thesis
      by (smt CollectD CollectI allWell below_rev.elims(2) case_prod_unfold chainY csIn_def csOut_def discrete_cpo h1 h2 inv_rev_rev is_ub_thelub snd_monofun subsetCE uspecWell.simps)
    qed
qed





cpodef 'm::ufuncl uspec = "{(S::'m set rev, csIn :: channel set discr, csOut::channel set discr). uspecWell S csIn csOut }"
  using uspecwell_exists apply blast
  using uspecwell_adm by blast

setup_lifting type_definition_uspec



(****************************************************)
section\<open>Definitions\<close>
(****************************************************) 
  
subsection\<open>abbreviations\<close>

abbreviation Rep_rev_uspec:: "'m uspec \<Rightarrow> 'm set" where
"Rep_rev_uspec uspec \<equiv> inv Rev (fst (Rep_uspec uspec))"

abbreviation Abs_rev_uspec:: "'m set \<Rightarrow> channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" where
"Abs_rev_uspec spec csIn csOut \<equiv> Abs_uspec ((Rev spec), Discr csIn, Discr csOut)"


subsection\<open>\<close>

(* Get the set of all ufuns in the uspec *)
definition uspecRevSet :: "'m uspec \<rightarrow> 'm set rev" where
"uspecRevSet = (\<Lambda> uspec. (fst (Rep_uspec uspec)))"

(* The domain. Notice this also works on empty uspecs *)
definition uspecDom :: "'m uspec \<rightarrow> channel set" where
"uspecDom = (\<Lambda> S. undiscr (fst (snd (Rep_uspec S))))"

(* The range. Notice this also works on empty uspecs *)
definition uspecRan :: "'m uspec \<rightarrow> channel set" where
"uspecRan = (\<Lambda> S. undiscr (snd (snd (Rep_uspec S))))"

definition uspecUnion :: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecUnion \<equiv> \<Lambda> S1 S2. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran)"


(****************************************************)
section\<open>Predicates\<close>
(****************************************************) 

definition uspecIsConsistent :: "'m uspec \<Rightarrow> bool" where
"uspecIsConsistent S \<equiv> ((Rep_rev_uspec S) \<noteq> {})"




(****************************************************)
section\<open>Lemmas\<close>
(****************************************************) 
subsection \<open>General Lemmas\<close>

lemma uspec_wellI: assumes "\<forall> f \<in> S. ufclDom\<cdot>f = In" and "\<forall> f \<in> S. ufclRan\<cdot>f = Out"
  shows "uspecWell (Rev S) (Discr In) (Discr Out)"
  by (simp add: assms(1) assms(2))

(* rep abs subtitution  *)
lemma rep_abs_uspec [simp]: assumes "uspecWell S csIn csOut" 
  shows "Rep_uspec (Abs_uspec (S,csIn, csOut)) =  (S,csIn, csOut)"
  by (simp add: Abs_uspec_inverse assms)

(* rep_uspec is a monofun *)
lemma uspec_rep_mono [simp]: "monofun Rep_uspec"
  apply(rule monofunI)
  by (simp add: below_uspec_def)

(* rep_uspec is a cont function  *)
lemma uspec_rep_cont [simp]: "cont Rep_uspec"
  by (metis (mono_tags, lifting) Abs_uspec_inverse Cont.contI2 Rep_uspec 
        adm_def adm_uspec lub_eq lub_uspec po_eq_conv uspec_rep_mono)

(* rule to prove that below relation between uspecs  *)
lemma rep_uspec_belowI: assumes "S1 \<sqsubseteq> S2"
  shows "(Rep_uspec S1) \<sqsubseteq> (Rep_uspec S2)"
  by (meson assms below_uspec_def)

(*  *)
lemma abs_rep_simp[simp]: "Abs_uspec (Rep_uspec S1) = S1"
  by (simp add: Rep_uspec_inverse)


lemma rep_abs_rev_simp[simp]: assumes "uspecWell (Rev S) (Discr csIn) (Discr csOut)"
  shows "Rep_rev_uspec (Abs_rev_uspec S csIn csOut) = S"
  by (metis assms fstI inv_rev_rev rep_abs_uspec)

lemma not_uspec_consisten_empty_eq: assumes "\<not> uspecIsConsistent S"
  shows "Rep_rev_uspec S = {}"
  using assms by (simp add: uspecIsConsistent_def assms)

lemma uspec_consist_f_ex: assumes "uspecIsConsistent S" shows "\<exists> f. f \<in> Rep_rev_uspec S"
  using assms uspecIsConsistent_def by auto

lemma uspec_obtain: 
  obtains S2 csIn csOut 
  where "Abs_uspec (Rev S2, Discr csIn, Discr csOut) = S" and "uspecWell (Rev S2) (Discr csIn) (Discr csOut)"
  by (metis (mono_tags, lifting) Rep_uspec Rep_uspec_inverse mem_Collect_eq old.prod.case uspecWell.cases)




subsection \<open>RevSet\<close>

thm uspecRevSet_def

lemma uspecrevset_cont: "cont (\<lambda> uspec. fst (Rep_uspec uspec))"
  by simp

lemma uspecrevset_insert: "uspecRevSet\<cdot>S = fst (Rep_uspec S)"
  by(simp add: uspecRevSet_def)



subsection \<open>Dom\<close>

lemma uspecdom_cont[simp]: "cont (\<lambda> S. undiscr (fst (snd (Rep_uspec S))))"
  apply(rule contI2)
   apply(rule monofunI)
   apply (metis (mono_tags, lifting) below_uspec_def discrete_cpo eq_imp_below snd_monofun)
  apply auto
  by (smt below_uspec_def discrete_cpo is_ub_thelub lub_const lub_eq po_eq_conv snd_monofun)
  
lemma uspecdom_insert: "uspecDom\<cdot>S = undiscr (fst (snd (Rep_uspec S)))"
  by (simp add: uspecDom_def)

(* dom of of two consitent uspec is eq  *)
lemma uspecdom_eq[simp]: assumes "S1\<sqsubseteq>S2"
  shows "uspecDom\<cdot>S1 = uspecDom\<cdot>S2"
  by (metis (mono_tags, lifting) assms discrete_cpo rep_uspec_belowI snd_monofun uspecdom_insert)

(* all element in uspec have the same dom  *)
lemma uspec_allDom: assumes "f\<in>inv Rev (uspecRevSet\<cdot>S)"
  shows "ufclDom\<cdot>f=uspecDom\<cdot>S"
  by (metis (no_types, hide_lams) Discr_undiscr assms fst_conv rep_abs_rev_simp rep_abs_uspec snd_conv uspecWell.simps uspec_obtain uspecdom_insert uspecrevset_insert)







  subsection \<open>Ran\<close>


lemma uspecran_cont[simp]: "cont (\<lambda> S. undiscr (snd (snd (Rep_uspec S))))"
  apply(rule contI2)
   apply(rule monofunI)
   apply (metis (mono_tags, lifting) below_uspec_def discrete_cpo eq_imp_below snd_monofun)
  apply auto
  by (smt below_uspec_def discrete_cpo is_ub_thelub lub_const lub_eq po_eq_conv snd_monofun)
  
lemma uspecran_insert: "uspecRan\<cdot>S = undiscr (snd (snd (Rep_uspec S)))"
  by (simp add: uspecRan_def)

lemma uspecran_eq[simp]: assumes "S1\<sqsubseteq>S2"
  shows "uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
  by (metis (mono_tags, lifting) assms discrete_cpo rep_uspec_belowI snd_monofun uspecran_insert)

(* all element in uspec have the same Ran  *)
lemma uspec_allRan: assumes "f\<in>inv Rev (uspecRevSet\<cdot>S)"
  shows "ufclRan\<cdot>f=uspecRan\<cdot>S"
  by (metis (mono_tags, lifting) assms fst_conv inv_rev_rev rep_abs_uspec snd_conv undiscr_Discr uspecWell.simps uspec_obtain uspecran_insert uspecrevset_insert)
  

subsection \<open>General Lemma 2\<close>

(* rule to prove the equality of uspec *)
lemma uspec_eqI: assumes "uspecRevSet\<cdot>S1 = uspecRevSet\<cdot>S2"
  and "uspecDom\<cdot>S1 = uspecDom\<cdot>S2"
  and "uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
  shows "S1 = S2"
  by (metis Discr_undiscr Rep_uspec_inject assms(1) assms(2) assms(3) prod.collapse uspecdom_insert uspecran_insert uspecrevset_insert)

lemma uspec_eqI2: assumes "uspecRevSet\<cdot>S1 = uspecRevSet\<cdot>S2"
  and "uspecIsConsistent S1"
  shows "S1 = S2"
  by (metis assms(1) assms(2) uspec_allDom uspec_allRan uspec_consist_f_ex uspec_eqI uspecrevset_insert)

(* if the upper uspec is consistent then the lower uspec is also consistent  *)
lemma uspec_isconsistent_below: assumes "S1\<sqsubseteq>S2" and "uspecIsConsistent S2"
  shows "uspecIsConsistent S1"
proof -
  have "uspecRevSet\<cdot>S1 \<sqsubseteq> uspecRevSet\<cdot>S2"
    by (simp add: assms(1) cont2monofunE) 
  thus ?thesis
    by (metis (no_types, lifting) Abs_cfun_inverse2 assms(2) below_rev.elims(2) eq_bottom_iff fst_conv rep_abs_rev_simp rep_abs_uspec set_cpo_simps(3) uspecIsConsistent_def uspecRevSet_def uspec_obtain uspecrevset_cont)
qed


subsection \<open>uspecUnion\<close>

lemma uspecUnion_sym: "(\<lambda> S1 S2. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran)) =
                       (\<lambda> S2 S1. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran))"
  by (simp add: sup_commute)

lemma uspecUnion_sym2: "(\<lambda> S1. \<Lambda> S2. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran)) =
                       (\<lambda> S2. \<Lambda> S1. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran))"
  by (simp add: sup_commute)

lemma uspecUnion_mono: "monofun (\<lambda> S1. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran))"
  apply(rule monofunI)
  sorry

(* lemma uspecUnion_cont_helper: "\<And>S2. cont (\<lambda> S1. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran))"
  sorry *)

lemma uspecUnion_cont_helper2: "cont (\<lambda> S1 S2. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran))"
  sorry

lemma uspecUnion_cont: "cont (\<lambda> S1. \<Lambda> S2. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                        let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                        let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2))) in
                        let filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all
                        in Abs_uspec (filtered, Discr dom, Discr ran))"
  apply(rule cont2cont_LAM)
  sorry

lemma uspecUnion_well: "\<And>S1 S2. uspecWell (let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2 in
                                            let ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2 in
                                            let all = Rev ((inv Rev (uspecRevSet\<cdot>S1)) \<union> (inv Rev (uspecRevSet\<cdot>S2)))
                                            in setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)\<cdot>all)
                                          (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2))
                                          (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))"
  sorry

(* TODO apply *)


end