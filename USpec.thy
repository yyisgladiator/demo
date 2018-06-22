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

(* Eases the proofs (by removing a lot of the text) *)
definition uspecUnion_general:: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecUnion_general \<equiv> (\<lambda> S1 S2. Abs_uspec (
    (setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)
                    \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))
                 \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2))),
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)),
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))))"

definition uspecUnion :: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecUnion \<equiv> \<Lambda> S1 S2. uspecUnion_general S1 S2"


definition uspecFilter_general :: "('m \<Rightarrow> bool) \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecFilter_general P \<equiv> \<lambda> S. Abs_uspec (setrevFilter P \<cdot>(uspecRevSet\<cdot>S),
    Discr (uspecDom\<cdot>S), Discr (uspecRan\<cdot>S))"

definition uspecFilter :: "('m \<Rightarrow> bool) \<Rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecFilter P \<equiv> \<Lambda> S. uspecFilter_general P S"


definition uspecInter_general :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecInter_general \<equiv> \<lambda> S1 S2. Abs_uspec (
    setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2),
    Discr (uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2), 
    Discr (uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2))"

definition uspecInter :: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecInter \<equiv> \<Lambda> S1 S2. uspecInter_general S1 S2"

definition uspecForall:: "('m::ufuncl \<Rightarrow> bool) \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspecForall P S \<equiv> setrevForall P (uspecRevSet\<cdot>S)"

definition uspecExists:: "('m::ufuncl \<Rightarrow> bool) \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspecExists P S \<equiv> setrevExists P (uspecRevSet\<cdot>S)"

(* Helper for uspecFlatten *)
definition uspec_set_filter:: "channel set \<Rightarrow> channel set \<Rightarrow> ('m uspec) set rev \<rightarrow> ('m uspec) set rev" where
"uspec_set_filter In Out = (\<Lambda> uspecs. (setrevFilter (\<lambda> uspec. uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out)\<cdot>uspecs))"

(* Computes a big Union over all Elements *)
(* This function is not cont, counterexample here: https://git.rwth-aachen.de/montibelle/automaton/core/issues/77 *)
definition uspecFlatten:: "channel set \<Rightarrow> channel set \<Rightarrow> ('m uspec) set rev \<Rightarrow> 'm uspec"
  where "uspecFlatten In Out = (\<lambda> uspecs. Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` (inv Rev (uspec_set_filter In Out\<cdot>uspecs)))) In Out)"

abbreviation  uspec_in:: "'m \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_in a S \<equiv> a \<in> inv Rev (uspecRevSet\<cdot>S)"

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

lemma uspec_wellI2: assumes "\<forall> f \<in> (inv Rev S). ufclDom\<cdot>f = In" and "\<forall> f \<in> (inv Rev S). ufclRan\<cdot>f = Out"
  shows "uspecWell S (Discr In) (Discr Out)"
  by (metis assms(1) assms(2) discr.inject inv_rev_rev uspecWell.elims(3))

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

lemma rep_rev_revset: "Rep_rev_uspec S = inv Rev (uspecRevSet\<cdot>S)"
  by(simp add: uspecRevSet_def)

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

lemma uspecdom_chain: assumes "chain Y"
                        shows "\<And>i j. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Y j)"
  using assms is_ub_thelub uspecdom_eq by blast

lemma uspecdom_chain_lub: assumes "chain Y"
                            shows "\<And>i. uspecDom\<cdot>(Y i) = (\<Squnion>j. uspecDom\<cdot>(Y j))"
  using assms contlub_cfun_arg is_ub_thelub uspecdom_eq by blast

lemma uspecdom_lub_chain: assumes "chain Y"
                            shows "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(\<Squnion>j. Y j)"
  by (simp add: assms is_ub_thelub)





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
  
lemma uspecran_chain: assumes "chain Y"
                        shows "\<And>i j. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Y j)"
  using assms is_ub_thelub uspecran_eq by blast

lemma uspecran_chain_lub: assumes "chain Y"
                            shows "\<And>i. uspecRan\<cdot>(Y i) = (\<Squnion>j. uspecRan\<cdot>(Y j))"
  using assms contlub_cfun_arg is_ub_thelub uspecran_eq by blast

lemma uspecran_lub_chain: assumes "chain Y"
                            shows "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(\<Squnion>j. Y j)"
  by (simp add: assms is_ub_thelub)


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

lemma uspec_belowI: assumes "uspecDom\<cdot>x = uspecDom\<cdot>y"
                        and "uspecRan\<cdot>x = uspecRan\<cdot>y"
                        and "uspecRevSet\<cdot>x \<sqsubseteq> uspecRevSet\<cdot>y"
                      shows "x \<sqsubseteq> y"
  proof -
    obtain x1 x2 x3 where x_def: "Rep_uspec x = (x1,x2,x3)"
      by (metis  surjective_pairing)
    obtain y1 y2 y3 where y_def: "Rep_uspec y = (y1,y2,y3)"
      by (metis  surjective_pairing)
    show ?thesis
      apply(simp add: below_uspec_def x_def y_def)
      by (metis assms fst_conv snd_conv undiscr_Discr uspecWell.cases uspecdom_insert uspecran_insert uspecrevset_insert x_def y_def)
   qed


subsection \<open>RevSet 2\<close>

(* Needs Dom/Ran lemmas *)
lemma uspecRevSet_condition: assumes "x \<in> inv Rev (uspecRevSet\<cdot>S1)"
                               shows "ufclDom\<cdot>x = uspecDom\<cdot>S1 \<and> ufclRan\<cdot>x = uspecRan\<cdot>S1"
  by (simp add: assms uspec_allDom uspec_allRan)


subsection \<open>uspecUnion\<close>

lemma uspecUnion_general_well[simp]: "\<And>S1 S2. uspecWell
    (setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)
                     \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))
                  \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2)))
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2))
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))"
  apply(rule uspec_wellI2)
  by (metis (mono_tags, lifting) setrevfilter_condition)+

lemma uspecUnion_lub_well[simp]:
assumes "chain Y"
  shows "\<And>S1. uspecWell
    (setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>(Lub Y))
                     \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>(Lub Y)))
                  \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>(Lub Y))))
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>(Lub Y)))
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>(Lub Y)))"
  apply(rule uspec_wellI2)
  by (metis (mono_tags, lifting) setrevfilter_condition)+

lemma uspecUnion_general_sym: 
"uspecUnion_general = (\<lambda> S1 S2. (uspecUnion_general S2 S1))"
  by (simp add: uspecUnion_general_def sup_commute setrevUnion_sym2)
        
(* Dom and ran for general (non cont) function *)                             
lemma uspecUnion_general_dom: "uspecDom\<cdot>(uspecUnion_general S1 S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  apply(simp add: uspecUnion_general_def)
  apply(subst uspecdom_insert)
  by(simp)

lemma uspecUnion_general_ran: "uspecRan\<cdot>(uspecUnion_general S1 S2) = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"
  apply(simp add: uspecUnion_general_def)
  apply(subst uspecran_insert)
  by(simp)

lemma uspecUnion_mono[simp]: "\<And>S1. monofun (uspecUnion_general S1)"
  proof (rule monofunI)
    fix S1::"'a uspec" and x::"'a uspec" and y::"'a uspec"
    assume a1: "x \<sqsubseteq> y"
    have h1: "uspecDom\<cdot>x = uspecDom\<cdot>y"
      by (simp add: a1)
    have h2: "uspecRan\<cdot>x = uspecRan\<cdot>y"
      by (simp add: a1)
    have h3: "(Rev (inv Rev (uspecRevSet\<cdot>S1) \<union> inv Rev (uspecRevSet\<cdot>x)))
            \<sqsubseteq> (Rev (inv Rev (uspecRevSet\<cdot>S1) \<union> inv Rev (uspecRevSet\<cdot>y)))"
      by (metis SetPcpo.less_set_def a1 below_refl below_rev.simps monofun_cfun_arg rev_inv_rev sup_mono)
    show "(uspecUnion_general S1 x) \<sqsubseteq> (uspecUnion_general S1 y)"
      apply(rule uspec_belowI)
      apply(simp add: uspecUnion_general_dom)
      apply(simp only: h1)
      apply(simp add: uspecUnion_general_ran)
      apply(simp only: h2)
      apply(simp add: uspecrevset_insert )
      apply(simp add: uspecUnion_general_def)
      apply(subst h1, subst h2)
      by (simp add: a1 monofun_cfun_arg)
  qed

lemma uspecUnion_chain:
  assumes "chain Y"
   shows "\<And>S1. chain (\<lambda>i. (uspecUnion_general S1 (Y i)))"
  using ch2ch_monofun assms uspecUnion_mono by blast  

lemma uspecUnion_cont1[simp]: "\<And>S1. cont (uspecUnion_general S1)"
  apply(rule contI2)
  apply simp
  apply(rule allI, rule impI)
   proof -
    fix S1::"'a uspec" and Y::"nat \<Rightarrow> 'a uspec"
    assume a1: "chain Y"
    have "chain (\<lambda>i. uspecUnion_general S1 (Y i))"
      by (simp add: a1 uspecUnion_chain)
    then have h1: "fst (Rep_uspec (\<Squnion>i::nat. uspecUnion_general S1 (Y i)))
                 = fst (\<Squnion>i::nat. Rep_uspec (uspecUnion_general S1 (Y i)))"
      by (metis cont2contlubE uspec_rep_cont)
    have "chain (\<lambda>i. Rep_uspec (uspecUnion_general S1 (Y i)))"
      using a1 uspecUnion_chain ch2ch_monofun uspec_rep_mono by blast
    then have h2: "fst (\<Squnion>i::nat. Rep_uspec (uspecUnion_general S1 (Y i)))
                 = (\<Squnion>i::nat. fst (Rep_uspec (uspecUnion_general S1 (Y i))))"
      using lub_prod by fastforce
    have h3: "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Lub Y)"
      by (simp add: a1 uspecdom_lub_chain)
    have h4: "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Lub Y)"
      by (simp add: a1 uspecran_lub_chain)
    show "uspecUnion_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecUnion_general S1 (Y i))"
      apply(rule uspec_belowI)
      apply(simp add: uspecUnion_general_dom)
      using a1 uspecUnion_chain uspecUnion_general_dom uspecdom_lub_chain apply blast
      apply(simp add: uspecUnion_general_ran)
      using a1 uspecUnion_chain uspecUnion_general_ran uspecran_lub_chain apply blast
      apply(simp add: uspecRevSet_def)
      apply(simp add: h1)
      apply(simp add: h2)
      apply(simp add: uspecUnion_general_def)
      apply(subst h3, subst h4)
      by (simp add: a1 contlub_cfun_arg)
  qed

lemma uspecUnion_cont2[simp]: "cont ( \<lambda>S1. \<Lambda> S2. (uspecUnion_general S1 S2))"
  apply(rule cont2cont_LAM)
  apply(simp only: uspecUnion_cont1)
  apply(rule easy_cont)
  apply(subst uspecUnion_general_sym)
  by simp+

lemma uspecUnion_apply: "\<And>A B. (\<Lambda> S1 S2. uspecUnion_general S1 S2)\<cdot>A\<cdot>B = (uspecUnion_general A B)"
  by (simp add: uspecUnion_def)

lemma uspecUnion_dom: "\<And>S1 S2. uspecDom\<cdot>(uspecUnion\<cdot>S1\<cdot>S2) = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)"
  by (simp add: uspecUnion_def uspecUnion_general_dom)

lemma uspecUnion_ran: "\<And>S1 S2. uspecRan\<cdot>(uspecUnion\<cdot>S1\<cdot>S2) = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)"
  by (simp add: uspecUnion_def uspecUnion_general_ran)

lemma uspecUnion_setrev: 
"\<And>S1 S2. uspecRevSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2) = (setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)
                                                          \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))
                                         \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2)))"
  apply(simp add: uspecRevSet_def)
  apply(simp add: uspecUnion_def)
  apply(simp add: uspecUnion_general_def)
  by (simp add: uspecrevset_insert)

lemma uspecUnion_setrev_condition: "\<And>S1 S2 x. x \<in> inv Rev(uspecRevSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2))
                                 \<longleftrightarrow> ((x \<in> inv Rev (uspecRevSet\<cdot>S1) \<or> x \<in> inv Rev (uspecRevSet\<cdot>S2))
                                  \<and> ufclDom\<cdot>x = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2
                                  \<and> ufclRan\<cdot>x = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)"
  apply(simp add: uspecUnion_setrev)
  by (metis (mono_tags, lifting) setrevFilter_gdw setrevUnion_gdw)

lemma uspecUnion_setrev_condition2:
  "\<And>S1 S2 x. x \<in> inv Rev(uspecRevSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2))
         \<longleftrightarrow> (x \<in> inv Rev (uspecRevSet\<cdot>S1) \<and> uspecDom\<cdot>S1 \<supseteq> uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 \<supseteq> uspecRan\<cdot>S2 
            \<or> x \<in> inv Rev (uspecRevSet\<cdot>S2) \<and> uspecDom\<cdot>S1 \<subseteq> uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 \<subseteq> uspecRan\<cdot>S2)"
  by (metis subset_Un_eq sup.absorb_iff1 uspecUnion_setrev_condition uspec_allDom uspec_allRan)

lemma uspecUnion_commutative: "\<And>S1 S2 S3. (uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3)) = (uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3)"
  proof -
    fix S1::"'a uspec" and S2::"'a uspec" and S3::"'a uspec"
    have h1: "uspecDom\<cdot>(uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3)) = uspecDom\<cdot>(uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3)"
      by (simp add: sup_assoc uspecUnion_dom)
    have h2: "uspecRan\<cdot>(uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3)) = uspecRan\<cdot>(uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3)"
      by (simp add: sup_assoc uspecUnion_ran)
    have h3: "inv Rev (uspecRevSet\<cdot>(uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3))) = inv Rev (uspecRevSet\<cdot>(uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3))"
      apply auto
      apply(simp add: uspecUnion_setrev_condition2 uspecUnion_dom uspecUnion_ran)
      apply auto
      apply(simp add: uspecUnion_setrev_condition2 uspecUnion_dom uspecUnion_ran)
      by auto
    show "uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3) = uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3"
      by (metis h1 h2 h3 rev_inv_rev uspec_eqI)
  qed

lemma uspecUnion_sym: "\<And>S1 S2. uspecUnion\<cdot>S1\<cdot>S2 = uspecUnion\<cdot>S2\<cdot>S1"
  by (metis uspecUnion_apply uspecUnion_def uspecUnion_general_sym)

lemma uspecUnion_consistent1: assumes "uspecIsConsistent S1"
                                  and "uspecDom\<cdot>S1 \<supseteq> uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 \<supseteq> uspecRan\<cdot>S2"
                                shows "uspecIsConsistent (uspecUnion\<cdot>S1\<cdot>S2)"
  proof -
    have "\<exists>x. x \<in> inv Rev(uspecRevSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2))"
      apply(simp add: uspecUnion_setrev_condition2)      
      by (metis assms rep_rev_revset uspec_consist_f_ex)
    then show ?thesis
      using not_uspec_consisten_empty_eq rep_rev_revset by fastforce
  qed

lemma uspecUnion_consistent2: assumes "uspecIsConsistent S2"
                                  and "uspecDom\<cdot>S1 \<subseteq> uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 \<subseteq> uspecRan\<cdot>S2"
                                shows "uspecIsConsistent (uspecUnion\<cdot>S1\<cdot>S2)"
  proof -
    have "\<exists>x. x \<in> inv Rev(uspecRevSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2))"
      apply(simp add: uspecUnion_setrev_condition2)      
      by (metis assms rep_rev_revset uspec_consist_f_ex)
    then show ?thesis
      using not_uspec_consisten_empty_eq rep_rev_revset by fastforce
  qed

lemma ucpecunion_fit_filtered:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
    shows "setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>A \<union> uspecDom\<cdot>B)
                    \<and> ufclRan\<cdot>f = (uspecRan\<cdot>A \<union> uspecRan\<cdot>B))
                 \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)) =
                 setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)"
proof -
  have b0: "\<forall>x \<in> inv Rev (setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)).
     ufclDom\<cdot>x = uspecDom\<cdot>A \<union> uspecDom\<cdot>B"
    by (metis assms(1) setrevUnion_gdw sup.idem uspec_allDom)
  have b1: "\<forall>x \<in> inv Rev (setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)).
     ufclRan\<cdot>x = uspecRan\<cdot>A \<union> uspecRan\<cdot>B"
    by (metis assms(2) setrevUnion_gdw sup.idem uspec_allRan)
  have b2: "Set.filter (\<lambda>f::'a. ufclDom\<cdot>f = uspecDom\<cdot>A \<union> uspecDom\<cdot>B \<and> ufclRan\<cdot>f = uspecRan\<cdot>A \<union> uspecRan\<cdot>B)
    (inv Rev (setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B))) = 
    (inv Rev (setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)))"
    using b0 b1 by fastforce
  show ?thesis
    apply(simp add: setrevFilter_def)
    by (simp add: b2 rev_inv_rev)
qed

lemma uspecunion_easy_def: 
 assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
     and "uspecRan\<cdot>A = uspecRan\<cdot>B"
   shows "uspecUnion_general A B = Abs_uspec (
    (setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)),
    (Discr (uspecDom\<cdot>A \<union> uspecDom\<cdot>B)),
    (Discr (uspecRan\<cdot>A \<union> uspecRan\<cdot>B)))"
proof -
  have b0:  "setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>A \<union> uspecDom\<cdot>B)
                    \<and> ufclRan\<cdot>f = (uspecRan\<cdot>A \<union> uspecRan\<cdot>B))
                 \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)) =
                 setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B)"
    using assms(1) assms(2) ucpecunion_fit_filtered by blast
  show ?thesis
    apply (simp add: uspecUnion_general_def)
    apply (subst b0)
    by auto
qed
 
lemma uspecunion_rule1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "P (Abs_uspec (setrevUnion\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B),
          Discr (uspecDom\<cdot>A), Discr (uspecRan\<cdot>A)))"
    shows "P (uspecUnion\<cdot>A\<cdot>B)"
  apply (simp add: uspecUnion_def)
  using assms by (simp add: uspecunion_easy_def)

(*
(* would be nice to prove this! *)
lemma uspec_union_notfit: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "uspecRevSet\<cdot>(uspecUnion\<cdot>A\<cdot>B) = Rev {}"
  oops
*)

subsection \<open>uspecFilter\<close> 

lemma uspecFilterSubset: 
"\<And>S::'a uspec. \<forall>f::'a\<in>inv Rev (setrevFilter P\<cdot>(uspecRevSet\<cdot>S)). f \<in> inv Rev (uspecRevSet\<cdot>S)"
  by (simp add: inv_rev_rev setrevfilter_insert)

lemma uspecFilter_general_well[simp]: "\<And>S. uspecWell (setrevFilter P \<cdot>(uspecRevSet\<cdot>S))
    (Discr (uspecDom\<cdot>S)) (Discr (uspecRan\<cdot>S))"
  by (metis (no_types, lifting) inv_rev_rev undiscr_Discr 
    uspecFilterSubset uspecWell.elims(3) uspec_allDom uspec_allRan)
        
(* Dom and ran for general (non cont) function *)                             
lemma uspecFilter_general_dom: "uspecDom\<cdot>(uspecFilter_general P S) = uspecDom\<cdot>S"
  apply (simp add: uspecFilter_general_def)
  apply (subst uspecdom_insert)
  by simp

lemma uspecFilter_general_ran: "uspecRan\<cdot>(uspecFilter_general P S) = uspecRan\<cdot>S"
  apply (simp add: uspecFilter_general_def)
  apply (subst uspecran_insert)
  by simp

lemma uspecFilter_mono[simp]: "monofun (\<lambda> S. uspecFilter_general P S)"
  proof (rule monofunI)
    fix x::"'a uspec" and y::"'a uspec"
    assume a1: "x \<sqsubseteq> y"
    have h1: "uspecDom\<cdot>x = uspecDom\<cdot>y"
      by (simp add: a1)
    have h2: "uspecRan\<cdot>x = uspecRan\<cdot>y"
      by (simp add: a1)
    show "uspecFilter_general P x \<sqsubseteq> uspecFilter_general P y"
      apply (rule uspec_belowI)
      apply (simp add: h1 uspecFilter_general_dom)
      apply (simp add: h2 uspecFilter_general_ran)
      by (metis a1 cont_pref_eq1I fst_conv rep_abs_uspec uspecFilter_general_def 
        uspecFilter_general_well uspecrevset_insert)
  qed

lemma uspecFilter_chain:
  assumes "chain Y"
    shows "chain (\<lambda>i. (uspecFilter_general P (Y i)))"
  using ch2ch_monofun assms uspecFilter_mono by blast

lemma uspecFilter_cont[simp]: "cont (\<lambda> S. uspecFilter_general P S)"
  apply(rule contI2)
  apply simp
  apply(rule allI, rule impI)
   proof -
    fix Y::"nat \<Rightarrow> 'a uspec"
    assume a1: "chain Y"
    have "chain (\<lambda>i. uspecFilter_general P (Y i))"
      by (simp add: a1 uspecFilter_chain)
    then have h1: "fst (Rep_uspec (\<Squnion>i::nat. uspecFilter_general P (Y i)))
                 = fst (\<Squnion>i::nat. Rep_uspec (uspecFilter_general P (Y i)))"
      by (metis cont2contlubE uspec_rep_cont)
    have "chain (\<lambda>i. Rep_uspec (uspecFilter_general P (Y i)))"
      using a1 uspecFilter_chain ch2ch_monofun uspec_rep_mono by blast
    then have h2: "fst (\<Squnion>i::nat. Rep_uspec (uspecFilter_general P (Y i)))
                 = (\<Squnion>i::nat. fst (Rep_uspec (uspecFilter_general P (Y i))))"
      using lub_prod by fastforce
    have h3: "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Lub Y)"
      using a1 is_ub_thelub uspecdom_eq by blast
    have h4: "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Lub Y)"
      using a1 is_ub_thelub uspecran_eq by blast
    show "uspecFilter_general P (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecFilter_general P (Y i))"
      apply (rule uspec_belowI)
      apply (simp add: uspecFilter_general_dom)
      using \<open>chain (\<lambda>i::nat. uspecFilter_general (P::'a \<Rightarrow> bool) ((Y::nat \<Rightarrow> 'a uspec) i))\<close> h3 
        is_ub_thelub uspecFilter_general_dom uspecdom_eq apply blast
      apply (simp add: uspecFilter_general_ran)
      using \<open>chain (\<lambda>i::nat. uspecFilter_general (P::'a \<Rightarrow> bool) ((Y::nat \<Rightarrow> 'a uspec) i))\<close> h4 
        is_ub_thelub uspecFilter_general_ran uspecran_eq apply blast
      apply(simp add: uspecRevSet_def)
      apply(simp add: h1)
      apply(simp add: h2)
      apply(simp add: uspecFilter_general_def)
      by (simp add: a1 contlub_cfun_arg)
  qed

lemma uspecfilter_insert: "uspecFilter P\<cdot>S = uspecFilter_general P S"
  by (simp add: uspecFilter_def)

lemma uspecfilter_condition: "\<And>x. uspec_in x (uspecFilter P\<cdot>A) \<Longrightarrow> P x"
proof -
  fix x :: 'a
  assume a1: "uspec_in x (uspecFilter P\<cdot>A)"
  have "(\<lambda>u. fst (Rep_uspec (u::'a uspec))) = Rep_cfun uspecRevSet"
    by (simp add: uspecRevSet_def)
  then have f2: "\<forall>u p. setrevFilter p\<cdot>(uspecRevSet\<cdot>(u::'a uspec)) = uspecRevSet\<cdot>(uspecFilter_general p u)"
    by (metis (no_types) fst_conv rep_abs_uspec uspecFilter_general_def uspecFilter_general_well)
  have "uspec_in x (uspecFilter_general P A)"
    using a1 by (simp add: uspecfilter_insert)
  then show "P x"
    using f2 by (metis setrevFilter_gdw)
qed

lemma uspecfilter_included: "\<And>x. uspec_in x (uspecFilter P\<cdot>A) \<Longrightarrow> uspec_in x A"
proof -
  fix x :: 'a
  assume a1: "uspec_in x (uspecFilter P\<cdot>A)"
  have "setrevFilter P\<cdot>(uspecRevSet\<cdot>A) = fst (Rep_uspec (uspecFilter P\<cdot>A))"
    by (simp add: uspecFilter_general_def uspecfilter_insert)
  then have "x \<in> inv Rev (setrevFilter P\<cdot>(uspecRevSet\<cdot>A))"
    using a1 rep_rev_revset by auto
  then show "uspec_in x A"
    by (meson uspecFilterSubset)
qed

subsection \<open>uspecInter\<close> 

lemma uspecInter_filtered: " setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2)
                          \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2))
                          \<cdot>(setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2)) =
                        setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2) "
proof -
  have b0: "\<forall>f \<in> inv Rev (setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2)).
            ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2)"
    by (metis IntD1 inf.idem inf_commute inv_rev_rev setrevinter_insert uspec_allDom)
  have b1: "\<forall>f \<in> inv Rev (setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2)).
            ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2)"
    by (metis IntD2 inf.idem inf_commute inv_rev_rev setrevinter_insert uspec_allRan)
  show ?thesis
    apply (simp add: setrevfilter_insert)
    by (smt Collect_cong Set.filter_def b0 b1 inf_set_def mem_Collect_eq rev.inject rev_inv_rev setrevinter_insert)
qed

lemma uspecInter_general_well[simp]: "\<And>S1 S2. uspecWell
    (setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2)
                     \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2))
                  \<cdot>(setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2)))
    (Discr (uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2))
    (Discr (uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2))"
  apply(rule uspec_wellI2)
  by (metis (mono_tags, lifting) setrevfilter_condition)+

lemma uspecInter_general_sym: 
"uspecInter_general = (\<lambda> S1 S2. (uspecInter_general S2 S1))"
  by (simp add: uspecInter_general_def inf_commute setrevInter_sym2)
        
(* Dom and ran for general (non cont) function *)                             
lemma uspecInter_general_dom: "uspecDom\<cdot>(uspecInter_general S1 S2) = uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2"
  apply(simp add: uspecInter_general_def)
  apply(subst uspecdom_insert)
  by (metis (no_types, lifting) Discr_undiscr discr.simps(1) fst_conv uspecInter_filtered rep_abs_uspec 
    snd_conv uspecInter_general_well uspecrevset_insert)

lemma uspecInter_general_ran: "uspecRan\<cdot>(uspecInter_general S1 S2) = uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2"
  apply(simp add: uspecInter_general_def)
  apply(subst uspecran_insert)
  by (metis (no_types, lifting) uspecInter_filtered rep_abs_uspec snd_conv undiscr_Discr uspecInter_general_well)


lemma uspecInter_mono[simp]: "\<And>S1. monofun (uspecInter_general S1)"
  proof (rule monofunI)
    fix S1::"'a uspec" and x::"'a uspec" and y::"'a uspec"
    assume a1: "x \<sqsubseteq> y"
    have h1: "uspecDom\<cdot>x = uspecDom\<cdot>y"
      by (simp add: a1)
    have h2: "uspecRan\<cdot>x = uspecRan\<cdot>y"
      by (simp add: a1)
    have h3: "(Rev (inv Rev (uspecRevSet\<cdot>S1) \<inter> inv Rev (uspecRevSet\<cdot>x)))
            \<sqsubseteq> (Rev (inv Rev (uspecRevSet\<cdot>S1) \<inter> inv Rev (uspecRevSet\<cdot>y)))"
      by (metis a1 monofun_cfun_arg setrevinter_insert)
    show "(uspecInter_general S1 x) \<sqsubseteq> (uspecInter_general S1 y)"
      apply(rule uspec_belowI)
      apply(simp add: uspecInter_general_dom)
      apply(simp only: h1)
      apply(simp add: uspecInter_general_ran)
      apply(simp only: h2)
      apply(simp add: uspecrevset_insert)
      apply(simp add: uspecInter_general_def)
      by (metis (no_types, lifting) fst_conv h3 uspecInter_filtered rep_abs_uspec setrevinter_insert uspecInter_general_well)
  qed

lemma uspecInter_chain:
  assumes "chain Y"
   shows "\<And>S1. chain (\<lambda>i. (uspecInter_general S1 (Y i)))"
  using ch2ch_monofun assms uspecInter_mono by blast  

lemma uspecInter_cont1[simp]: "\<And>S1. cont (uspecInter_general S1)"
  apply(rule contI2)
  apply simp
  apply(rule allI, rule impI)
   proof -
    fix S1::"'a uspec" and Y::"nat \<Rightarrow> 'a uspec"
    assume a1: "chain Y"
    have "chain (\<lambda>i. uspecInter_general S1 (Y i))"
      by (simp add: a1 uspecInter_chain)
    then have h1: "fst (Rep_uspec (\<Squnion>i::nat. uspecInter_general S1 (Y i)))
                 = fst (\<Squnion>i::nat. Rep_uspec (uspecInter_general S1 (Y i)))"
      by (metis cont2contlubE uspec_rep_cont)
    have "chain (\<lambda>i. Rep_uspec (uspecInter_general S1 (Y i)))"
      using a1 uspecInter_chain ch2ch_monofun uspec_rep_mono by blast
    then have h2: "fst (\<Squnion>i::nat. Rep_uspec (uspecInter_general S1 (Y i)))
                 = (\<Squnion>i::nat. fst (Rep_uspec (uspecInter_general S1 (Y i))))"
      using lub_prod by fastforce
    have h3: "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Lub Y)"
      by (simp add: a1 uspecdom_lub_chain)
    have h4: "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Lub Y)"
      by (simp add: a1 uspecran_lub_chain)
    show "uspecInter_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecInter_general S1 (Y i))"
      apply(rule uspec_belowI)
      apply(simp add: uspecInter_general_dom)
      using a1 uspecInter_chain uspecInter_general_dom uspecdom_lub_chain apply blast
      apply(simp add: uspecInter_general_ran)
      using a1 uspecInter_chain uspecInter_general_ran uspecran_lub_chain apply blast
      apply(simp add: uspecRevSet_def)
      apply(simp add: h1)
      apply(simp add: h2)
      apply(simp add: uspecInter_general_def)
      by (smt a1 ch2ch_Rep_cfunR contlub_cfun_arg fst_conv uspecInter_filtered 
        lub_eq not_below2not_eq rep_abs_uspec uspecInter_general_well)
  qed

lemma uspecInter_cont2[simp]: "cont ( \<lambda>S1. \<Lambda> S2. (uspecInter_general S1 S2))"
  apply(rule cont2cont_LAM)
  apply(simp only: uspecInter_cont1)
  apply(rule easy_cont)
  apply(subst uspecInter_general_sym)
  by simp+

lemma uspecInter_insert: "uspecInter\<cdot>S1\<cdot>S2 = uspecInter_general S1 S2"
  by (simp add: uspecInter_def)

lemma uspecInter_apply: "\<And>A B. (\<Lambda> S1 S2. uspecInter_general S1 S2)\<cdot>A\<cdot>B = uspecInter_general A B"
  by simp

lemma uspecInter_dom: "\<And>S1 S2. uspecDom\<cdot>(uspecInter\<cdot>S1\<cdot>S2) = uspecDom\<cdot>S1 \<inter> uspecDom\<cdot>S2"
  by (simp add: uspecInter_def uspecInter_general_dom)

lemma uspecInter_ran: "\<And>S1 S2. uspecRan\<cdot>(uspecInter\<cdot>S1\<cdot>S2) = (uspecRan\<cdot>S1 \<inter> uspecRan\<cdot>S2)"
  by (simp add: uspecInter_def uspecInter_general_ran)

lemma uspecInter_setrev: 
"\<And>S1 S2. uspecRevSet\<cdot>(uspecInter\<cdot>S1\<cdot>S2) = (setrevInter\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2))"
  apply(simp add: uspecRevSet_def)
  apply(simp add: uspecInter_def)
  apply(simp add: uspecInter_general_def)
  by (metis (mono_tags, lifting) fst_conv rep_abs_uspec uspecInter_filtered uspecInter_general_well uspecrevset_insert)

lemma uspecinter_rule1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
     and  "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "P (Abs_uspec (setrevInter\<cdot>(uspecRevSet\<cdot>A)\<cdot>(uspecRevSet\<cdot>B),
          Discr (uspecDom\<cdot>A), Discr (uspecRan\<cdot>A)))"
    shows "P (uspecInter\<cdot>A\<cdot>B)"
 apply (simp add: uspecInter_insert uspecInter_general_def)
 using assms(1) assms(2) assms(3) by auto

lemma uspecinter_incl1: "\<forall>x\<in> inv Rev (uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). x \<in> inv Rev (uspecRevSet\<cdot>A)"
  by (simp add: setrevInter_gdw uspecInter_setrev)

lemma uspecinter_incl2: "\<forall>x\<in> inv Rev (uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). x \<in> inv Rev (uspecRevSet\<cdot>B)"
    by (simp add: setrevInter_gdw uspecInter_setrev)

lemma uspec_inter_notfit: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B) = Rev {}"
proof - 
  have b0: "\<forall>x\<in> inv Rev (uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). uspecDom\<cdot>A = ufclDom\<cdot>x"
    using uspecinter_incl1 uspec_allDom by blast
  have b1: "\<forall>x\<in> inv Rev (uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). uspecDom\<cdot>B = ufclDom\<cdot>x"
    using uspecinter_incl2 uspec_allDom by blast
  have b2: "\<forall>x\<in> inv Rev (uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). uspecRan\<cdot>A = ufclRan\<cdot>x"
    using uspecinter_incl1 uspec_allRan by blast
  have b3: "\<forall>x\<in> inv Rev (uspecRevSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). uspecRan\<cdot>B = ufclRan\<cdot>x"
    using uspecinter_incl2 uspec_allRan by blast
  show ?thesis
    by (metis (no_types, lifting) Abs_cfun_inverse2 assms b0 b1 b2 b3 inv_rev_rev 
      not_uspec_consisten_empty_eq setrev_eqI uspecRevSet_def uspec_consist_f_ex uspecrevset_cont)
qed

section \<open>uspecFlatten\<close>

lemma uspec_filter_in_out_cont: "cont (\<lambda> uspecs. (setrevFilter (uspec_in_out_eq In Out)\<cdot>uspecs))"
  by simp

lemma uspec_set_filter_empty: "uspec_set_filter In Out\<cdot>(Rev {}) = Rev {}"
  apply (simp add: uspec_set_filter_def)
  apply (rule setrev_eqI)
  apply (simp add: inv_rev_rev)
  by (simp add: Set.filter_def inv_rev_rev setrevfilter_insert)

lemma uspecflatten_well: "uspecWell (Rev (setflat\<cdot>(Rep_rev_uspec ` (inv Rev (uspec_set_filter In Out\<cdot>uspecs))))) (Discr In) (Discr Out)"
  apply (cases "((Rep_rev_uspec ` (inv Rev (uspec_set_filter In Out\<cdot>uspecs)))) = {}")
   apply (simp_all add: uspec_set_filter_empty)
   apply (metis empty_iff setflat_empty)
proof (rule)
  fix f::'a
  assume a1: " inv Rev (uspec_set_filter In Out\<cdot>uspecs) \<noteq> {}"
  assume a2: "f \<in> setflat\<cdot>(Rep_rev_uspec ` inv Rev (uspec_set_filter In Out\<cdot>uspecs))"
  have f1: "\<forall> uspec \<in> inv Rev (uspec_set_filter In Out\<cdot>uspecs). uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out"
    by (metis (mono_tags, lifting) Cfun.cfun.Rep_cfun_inverse setrevfilter_condition uspec_set_filter_def)
  have f2: "\<forall> uspec_set \<in> (Rep_rev_uspec ` (inv Rev (uspec_set_filter In Out\<cdot>uspecs))). 
        uspecWell (Rev uspec_set) (Discr In) (Discr Out)"
    by (simp add: f1 uspec_allDom uspec_allRan uspecrevset_insert)
  obtain uspec_set where uspec_set_def: "f \<in> uspec_set" and uspec_set_def2: "uspec_set \<in> Rep_rev_uspec ` inv Rev (uspec_set_filter In Out\<cdot>uspecs)"
    by (metis a2 setflat_obtain)
  have f3: "uspecWell (Rev uspec_set) (Discr In) (Discr Out)"
    using f2 uspec_set_def2 by blast
  show "ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out"
    using f3 uspec_set_def by auto
qed


lemma uspecflatten_mono_h: "monofun (\<lambda> uspecs. Rev (setflat\<cdot>(Rep_rev_uspec ` (inv Rev (uspec_set_filter In Out\<cdot>uspecs)))))"
proof (rule rev_monoI)
  fix x::"'a uspec set rev" and y::"'a uspec set rev"
  assume a1: "x \<sqsubseteq> y"
  have "uspec_set_filter In Out\<cdot>x \<sqsubseteq> uspec_set_filter In Out\<cdot>y"
    by (simp add: a1 monofun_cfun_arg)
  then have " inv Rev (uspec_set_filter In Out\<cdot>y) \<sqsubseteq>  inv Rev (uspec_set_filter In Out\<cdot>x)"
    by (metis SetPcpo.less_set_def revBelowNeqSubset)
  then have "(Rep_rev_uspec ` inv Rev (uspec_set_filter In Out\<cdot>y)) \<sqsubseteq> (Rep_rev_uspec ` inv Rev (uspec_set_filter In Out\<cdot>x))"
    by (simp add: SetPcpo.less_set_def image_mono)
  thus "setflat\<cdot>(Rep_rev_uspec ` inv Rev (uspec_set_filter In Out\<cdot>y)) \<sqsubseteq> setflat\<cdot>(Rep_rev_uspec ` inv Rev (uspec_set_filter In Out\<cdot>x))"
    by (simp add: monofun_cfun_arg)
qed

lemma uspecflatten_dom: "uspecDom\<cdot>(uspecFlatten In Out uspecs) = In"
  apply (simp add: uspecDom_def uspecFlatten_def)
  by (metis fst_conv rep_abs_uspec snd_conv undiscr_Discr uspecflatten_well)

lemma uspecflatten_ran: "uspecRan\<cdot>(uspecFlatten In Out uspecs) = Out"
  apply (simp add: uspecRan_def uspecFlatten_def)
  by (metis rep_abs_uspec snd_conv undiscr_Discr uspecflatten_well)

lemma uspecflatten_monofun: "monofun (uspecFlatten In Out)"
  unfolding uspecFlatten_def
  apply (rule monofunI)
  apply (rule uspec_belowI)
    apply (metis uspecFlatten_def uspecflatten_dom)
   apply (metis uspecFlatten_def uspecflatten_ran)
  apply (simp add: uspecrevset_insert)
  apply (subst rep_abs_uspec)
  using uspecflatten_well apply blast
  apply (subst rep_abs_uspec)
  using uspecflatten_well apply blast
  apply simp
  by (metis SetPcpo.less_set_def image_mono monofun_cfun_arg revBelowNeqSubset)

subsection \<open>Forall Exists\<close>

lemma uspec_for_all_ex:
  assumes "uspecForall P S"
  assumes "uspecExists (\<lambda>x. True) S"
  shows "uspecExists P S"
  using assms(1) assms(2) setrev_for_all_ex uspecExists_def uspecForall_def by blast

lemma uspec_subsetforall: 
  assumes "uspecForall P S"
  and "inv Rev (uspecRevSet\<cdot>T) \<subseteq> inv Rev (uspecRevSet\<cdot>S)"
  shows "uspecForall P T"
  using assms(1) assms(2) setrev_subsetforall uspecForall_def by blast

lemma uspec_ballI: "(\<And>x. x \<in> inv Rev (uspecRevSet\<cdot>S) \<Longrightarrow> P x) \<Longrightarrow> uspecForall P S"
  by (simp add: setrev_ballI uspecForall_def)

lemma uspec_bexCI: "uspecForall (\<lambda>x. \<not> P x \<longrightarrow> P a) S \<Longrightarrow> a \<in> inv Rev (uspecRevSet\<cdot>S) \<Longrightarrow> uspecExists P S"
  apply (simp add: uspecExists_def uspecForall_def)
  apply (simp add: setrevExists_def setrevForall_def)
  by auto

lemma uspec_bex_triv_one_point1: "uspecExists (\<lambda>x. x = a) S \<longleftrightarrow> uspec_in a S"
  by (simp add: setrevExists_def uspecExists_def)

lemma uspec_bex_triv_one_point2: "uspecExists (\<lambda>x. a = x) S \<longleftrightarrow> uspec_in a S"
  by (simp add: setrevExists_def uspecExists_def)

lemma uspec_bex_one_point1: "uspecExists (\<lambda>x. x = a \<and> P x) S \<longleftrightarrow> uspec_in a S \<and> P a"
  by (simp add: setrevExists_def uspecExists_def)

lemma uspec_bex_one_point2: "uspecExists (\<lambda>x. a = x \<and> P x) S \<longleftrightarrow> uspec_in a S \<and> P a"
  by (simp add: setrevExists_def uspecExists_def)

lemma uspec_ball_one_point1: "uspecForall (\<lambda>x. x = a \<longrightarrow> P x) S \<longleftrightarrow> (uspec_in a S \<longrightarrow> P a)"
  by (simp add: setrevForall_def uspecForall_def uspec_ballI)

lemma uspec_ball_one_point2: "uspecForall (\<lambda>x. a = x \<longrightarrow> P x) S \<longleftrightarrow> (uspec_in a S \<longrightarrow> P a)"
  by (simp add: setrevForall_def uspecForall_def uspec_ballI)

lemma uspec_subset_eq: "inv Rev (uspecRevSet\<cdot>A) \<subseteq> inv Rev (uspecRevSet\<cdot>B) 
  \<longleftrightarrow> uspecForall (\<lambda>x. x \<in> inv Rev (uspecRevSet\<cdot>B)) A"
  by (simp add: uspecForall_def setrevForall_def subset_eq)

lemma uspec_allDom2: "uspecForall (\<lambda>X. ufclDom\<cdot>X = uspecDom\<cdot>S) S"
  by (simp add: uspec_allDom uspec_ballI)

lemma uspec_Ran2: "uspecForall (\<lambda>X. ufclRan\<cdot>X = uspecRan\<cdot>S) S"
  by (simp add: uspec_allRan uspec_ballI)

lemma uspec_union_forall: 
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
    shows "uspecForall P (uspecUnion\<cdot>A\<cdot>B) \<longleftrightarrow> (uspecForall P A \<and> uspecForall P B)"
  apply (simp add: uspecForall_def uspecUnion_def uspecRevSet_def)
  apply (simp add: setrevForall_def uspecUnion_general_def)
  using assms uspecrevset_cont uspecRevSet_def setrevUnion_gdw
  by (smt Abs_cfun_inverse2 setrevFilter_gdw setrevfilter_included sup_idem uspec_allDom uspec_allRan)

lemma uspec_union_exists:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
    shows "uspecExists P (uspecUnion\<cdot>A\<cdot>B) \<longleftrightarrow> uspecExists P A \<or> uspecExists P B"
  apply (simp add: uspecExists_def uspecUnion_def uspecRevSet_def)
  apply (simp add: setrevExists_def uspecUnion_general_def)
  using assms uspecrevset_cont uspecRevSet_def setrevUnion_gdw
  by (smt Abs_cfun_inverse2 setrevFilter_gdw setrevUnion_sym2 sup.idem uspec_allDom uspec_allRan)

(*
(*uspec_union_notfit needed for this*)
lemma uspec_inter_notfit_notex:
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "\<And>a. \<not>(uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B))"
*)

lemma uspec_union_l1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecExists (\<lambda>x. x = a) A \<or> uspecExists (\<lambda>x. x = a) B"
    shows "uspecExists (\<lambda>x. x = a) (uspecUnion\<cdot>A\<cdot>B)"
  using assms apply (simp add: uspecExists_def uspecUnion_def)
  apply (simp add: uspecunion_easy_def)
  by (smt Abs_cfun_inverse2 fst_conv rep_abs_uspec setrev_union_exists sup.idem 
    ucpecunion_fit_filtered uspecRevSet_def uspecUnion_general_well uspecrevset_cont)


lemma uspec_inter_forall_help1: 
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecForall P A \<and> uspecForall P B"
    shows "uspecForall P (uspecInter\<cdot>A\<cdot>B)"
  apply (rule uspecinter_rule1)
  apply (simp add: assms(1))
  apply (simp add: assms(2))
  apply (simp add: uspecForall_def uspecRevSet_def)
  by (metis (no_types, lifting) assms fst_conv inf.idem rep_abs_uspec setrev_inter_forall 
    uspecForall_def uspecInter_filtered uspecInter_general_well uspecrevset_insert)

lemma uspec_inter_forall_help2: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
    shows "uspecForall P (uspecInter\<cdot>A\<cdot>B)"
  by (metis assms empty_iff inv_rev_rev uspec_ballI uspec_inter_notfit)

lemma uspec_inter_forall: 
  assumes "uspecForall P A \<and> uspecForall P B"
    shows "uspecForall P (uspecInter\<cdot>A\<cdot>B)"
  using assms uspec_inter_forall_help1 uspec_inter_forall_help2 by blast

lemma uspec_inter_exists: 
  assumes "uspecExists P (uspecInter\<cdot>A\<cdot>B)"
  shows "uspecExists P A \<and> uspecExists P B"
  by (metis assms setrev_inter_exists uspecExists_def uspecInter_setrev)

lemma uspec_inter_notfit_notex:
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "\<And>a. \<not>(uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B))"
  using uspec_inter_notfit
  by (metis assms empty_iff inv_rev_rev setrevExists_def uspecExists_def)

lemma uspec_inter_l1_help1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecExists (\<lambda>x. x = a) A \<and> uspecExists (\<lambda>x. x = a) B"
    shows "uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B)"
  apply (rule uspecinter_rule1)
  apply (simp add: assms(1))
  apply (simp add: assms(2))
  apply (simp add: uspecForall_def uspecRevSet_def)
  by (smt Int_absorb assms fst_conv rep_abs_uspec setrevExists_def setrevInter_gdw setrevInter_sym2 
    uspecExists_def uspecInter_filtered uspecInter_general_well uspecrevset_insert)

lemma uspec_inter_l1_help2:
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
      and "uspecExists (\<lambda>x. x = a) A \<and> uspecExists (\<lambda>x. x = a) B"
    shows "uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B)"
  by (smt assms uspec_inter_notfit disjoint_iff_not_equal rev.inject setrevExists_def 
    setrevinter_insert uspecExists_def uspecInter_setrev)

lemma uspec_inter_l1:
  assumes "uspecExists (\<lambda>x. x = a) A \<and> uspecExists (\<lambda>x. x = a) B"
  shows "uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B)"
  by (metis assms uspec_inter_l1_help1 uspec_inter_l1_help2)

lemma uspec_filter_forall:
  "uspecForall P (uspecFilter P\<cdot>A)"
  apply (simp add: uspecfilter_insert uspecForall_def)
  by (metis setrev_filter_forall fst_conv rep_abs_uspec uspecFilter_general_def 
    uspecFilter_general_well uspecrevset_insert)

end