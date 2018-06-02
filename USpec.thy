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
"uspecUnion \<equiv> \<Lambda> S1 S2. let dom = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2;
                            ran = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2;
                            filtered = setrevFilter (\<lambda>f. ufclDom\<cdot>f = dom \<and> ufclRan\<cdot>f = ran)
                                                    \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2))
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


subsection \<open>uspecUnion\<close>

(* Eases the proofs (by removing a lot of the text) *)
definition uspecUnion_general:: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecUnion_general \<equiv> (\<lambda> S1 S2. Abs_uspec (
    (setrevFilter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)
                    \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))
                 \<cdot>(setrevUnion\<cdot>(uspecRevSet\<cdot>S1)\<cdot>(uspecRevSet\<cdot>S2))),
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)),
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))))"

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

lemma uspecUnion_sym: 
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

lemma uspecUnion_cont1: "\<And>S1. cont (uspecUnion_general S1)"
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

lemma uspecUnion_cont2: "cont ( \<lambda>S1. \<Lambda> S2. (uspecUnion_general S1 S2))"
  apply(rule cont2cont_LAM)
  apply(simp only: uspecUnion_cont1)
  apply(rule easy_cont)
  apply auto
  sorry
  using uspecUnion_cont1 by blast

(* TODO apply *)


end