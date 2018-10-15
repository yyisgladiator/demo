(*  Title:        USpec
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "universal specification" 
*)

theory USpec
  imports inc.UnivClasses
begin

default_sort ufuncl

(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
fun uspecWell :: "'m set \<Rightarrow> channel set discr \<Rightarrow> channel set discr \<Rightarrow> bool" where
"uspecWell  S (Discr csIn) (Discr csOut)  = (\<forall> f\<in>S . (ufclDom\<cdot>f = csIn \<and> ufclRan\<cdot>f=csOut) )"
(* define a Set of 'm SPF's. all SPS in a set must have the same In/Out channels *)


(* Every "empty" uspec is allowed *)
lemma uspecwell_exists: "uspecWell {} csIn csOut"
  using uspecWell.elims(3) by fastforce

(* Required for cpodef proof *)
lemma uspecwell_adm: "adm (\<lambda>x::'m set \<times> channel set discr \<times> channel set discr.
            x \<in> {(S::'m set, csIn::channel set discr, csOut::channel set discr). uspecWell S csIn csOut})"
proof(rule admI)
  fix Y::"nat \<Rightarrow> 'm set \<times> channel set discr \<times> channel set discr"
  assume chainY: "chain Y" and 
    allWell: "\<forall>i::nat. Y i \<in> {(S::'m set, csIn::channel set discr, csOut::channel set discr). uspecWell S csIn csOut}"

  obtain csIn where csIn_def: "\<forall>i::nat. (Discr csIn) = (fst (snd (Y i)))"
    by (metis chainY discr.exhaust discrete_cpo fst_conv is_ub_thelub old.prod.inject snd_conv snd_monofun surj_pair)
  obtain csOut where csOut_def: "\<forall>i::nat. (Discr csOut) = (snd (snd (Y i)))"
    by (metis chainY discr.exhaust discrete_cpo fst_conv is_ub_thelub old.prod.inject snd_conv snd_monofun surj_pair)

  have h1: "fst (Y 0 ) \<sqsubseteq> fst (\<Squnion>i::nat. Y i)"
    using chainY fst_monofun is_ub_thelub by blast
  show "(\<Squnion>i::nat. Y i) \<in> {(S::'m set, csIn::channel set discr, csOut::channel set discr). uspecWell S csIn csOut}"
    sorry
qed

lemma uspecwell_filter: "uspecWell S cIn cOut \<Longrightarrow> uspecWell (Set.filter P S) cIn cOut"
  using uspecWell.elims(3) by fastforce
  


cpodef 'm::ufuncl uspec = "{(S::'m set, csIn :: channel set discr, csOut::channel set discr). uspecWell S csIn csOut }"
  using uspecwell_exists apply blast
  using uspecwell_adm by blast

setup_lifting type_definition_uspec



lemma uspec_rep_cont[simp]:"cont Rep_uspec"
  using cont_Rep_uspec cont_id by blast

(****************************************************)
section\<open>Definitions\<close>
(****************************************************) 
  

(* Get the set of all ufuns in the uspec *)
lift_definition uspecSet :: "'m uspec \<rightarrow> 'm set" is
  "(\<lambda>uspec. (fst (Rep_uspec uspec)))"
  by(simp add: cfun_def)

(* The domain. Notice this also works on empty uspecs *)
lift_definition uspecDom :: "'m uspec \<rightarrow> channel set" is
"(\<lambda> S. undiscr (fst (snd (Rep_uspec S))))"
  apply(auto simp add: cfun_def)
  apply(rule contI2)
   apply(rule monofunI)
   apply (metis (mono_tags, lifting) below_uspec_def discrete_cpo eq_imp_below snd_monofun)
  apply auto
  by (smt below_uspec_def discrete_cpo is_ub_thelub lub_const lub_eq po_eq_conv snd_monofun)


(* The range. Notice this also works on empty uspecs *)
lift_definition uspecRan :: "'m uspec \<rightarrow> channel set" is
"\<lambda> S. undiscr (snd (snd (Rep_uspec S)))"
  apply(auto simp add: cfun_def)
  apply(rule contI2)
  apply (metis (mono_tags, lifting) below_uspec_def discrete_cpo monofunI po_eq_conv snd_monofun)
  by (smt below_lub below_refl below_uspec_def discrete_cpo po_class.chain_def snd_monofun)

(* Set of all uspecs with the given dom/ran *)
definition USPEC :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec set" where
"USPEC In Out = {spec. uspecDom\<cdot>spec = In \<and> uspecRan\<cdot>spec = Out}"

lift_definition uspecMax :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" is
"\<lambda>In Out. ((Set.filter (\<lambda>x. ufclDom\<cdot>x = In \<and> ufclRan\<cdot>x=Out) UNIV), Discr In, Discr Out)"
  by simp

lift_definition uspecLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" is
"\<lambda>In Out. ({}, Discr In, Discr Out)"
  by simp


definition uspecFilter_general :: "('m \<Rightarrow> bool) \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecFilter_general P S =  Abs_uspec (Set.filter P (uspecSet\<cdot>S), Discr (uspecDom\<cdot>S), Discr (uspecRan\<cdot>S))"

definition uspecFilter :: "('m \<Rightarrow> bool) \<Rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecFilter P \<equiv> \<Lambda> S. uspecFilter_general P S"



(* Eases the proofs (by removing a lot of the text) *)
definition uspecUnion_general:: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecUnion_general S1 S2 = Abs_uspec ((
    (Set.filter (\<lambda>f.  (uspecDom\<cdot>S1 = uspecDom\<cdot>S2)
                    \<and> (uspecRan\<cdot>S1 = uspecRan\<cdot>S2))
                 ((uspecSet\<cdot>S1) \<union> (uspecSet\<cdot>S2)))),
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)),
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)))"

definition uspecUnion :: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecUnion \<equiv> \<Lambda> S1 S2. uspecUnion_general S1 S2"


definition uspecInter_general :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> 'm uspec" where
"uspecInter_general \<equiv> \<lambda> S1 S2. Abs_uspec (
    (uspecSet\<cdot>S1) \<inter> (uspecSet\<cdot>S2),
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2)),
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)))"

definition uspecInter :: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecInter \<equiv> \<Lambda> S1 S2. uspecInter_general S1 S2"

definition uspecForall:: "('m::ufuncl \<Rightarrow> bool) \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspecForall P S \<equiv> (\<forall>f\<in>uspecSet\<cdot>S. P f)"

definition uspecExists:: "('m::ufuncl \<Rightarrow> bool) \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspecExists P S \<equiv> (\<exists>f\<in>uspecSet\<cdot>S. P f)"

(* Helper for uspecFlatten *)
definition uspec_set_filter:: "channel set \<Rightarrow> channel set \<Rightarrow> ('m uspec) set \<rightarrow> ('m uspec) set" where
"uspec_set_filter In Out = (\<Lambda> uspecs. (Set.filter (\<lambda> uspec. uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out) uspecs))"

(* Computes a big Union over all Elements *)
definition uspecFlatten:: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec set \<rightarrow> 'm uspec"
  where "uspecFlatten In Out = (\<Lambda> uspecs. Abs_uspec ((setflat\<cdot>((Rep_cfun uspecSet)  ` (uspec_set_filter In Out\<cdot>uspecs))), Discr In, Discr Out))"

definition uspecSize :: "'a uspec \<Rightarrow> lnat" where
 "uspecSize X = setSize (uspecSet\<cdot>X)"

(****************************************************)
section\<open>Predicates\<close>
(****************************************************) 

definition uspecIsConsistent :: "'m uspec \<Rightarrow> bool" where
"uspecIsConsistent S \<equiv> ((uspecSet\<cdot>S) \<noteq> {})"

(****************************************************)
section\<open>Lemmas\<close>
(****************************************************) 
subsection \<open>General Lemmas\<close>

lemma uspec_lub_in: assumes "chain Y" shows "(\<Squnion>i. ((Y i)::'m set, Discr In,Discr Out)) = (\<Squnion>i. Y i, Discr In, Discr Out)"
  by (smt Pair_below_iff assms below_refl fstI is_lub_prod lub_const lub_eq lub_eqI po_class.chain_def sndI)


lemma uspec_wellI: assumes "\<forall> f \<in> S. ufclDom\<cdot>f = In" and "\<forall> f \<in> S. ufclRan\<cdot>f = Out"
  shows "uspecWell (S) (Discr In) (Discr Out)"
  by (simp add: assms(1) assms(2))

(* rep abs subtitution  *)
lemma rep_abs_uspec [simp]: assumes "uspecWell S csIn csOut" 
  shows "Rep_uspec (Abs_uspec (S,csIn, csOut)) =  (S,csIn, csOut)"
  by (simp add: Abs_uspec_inverse assms)

(* rep_uspec is a monofun *)
lemma uspec_rep_mono [simp]: "monofun Rep_uspec"
  apply(rule monofunI)
  by (simp add: below_uspec_def)

(* rule to prove that below relation between uspecs  *)
lemma rep_uspec_belowI: assumes "S1 \<sqsubseteq> S2"
  shows "(Rep_uspec S1) \<sqsubseteq> (Rep_uspec S2)"
  by (meson assms below_uspec_def)

(*  *)
lemma abs_rep_simp[simp]: "Abs_uspec (Rep_uspec S1) = S1"
  by (simp add: Rep_uspec_inverse)

lemma uspec_obtain: 
  obtains S2 csIn csOut 
  where "Abs_uspec (S2, Discr csIn, Discr csOut) = S" and "uspecWell (S2) (Discr csIn) (Discr csOut)"
  by (metis (mono_tags, lifting) Rep_uspec Rep_uspec_inverse mem_Collect_eq old.prod.case uspecWell.cases)



subsection \<open>Dom\<close>

lemma uspecdom_insert: "uspecDom\<cdot>S = undiscr (fst (snd (Rep_uspec S)))"
  by (simp add: uspecDom.rep_eq)

(* dom of of two consitent uspec is eq  *)
lemma uspecdom_eq: assumes "S1\<sqsubseteq>S2"
  shows "uspecDom\<cdot>S1 = uspecDom\<cdot>S2"
  by (metis (mono_tags, lifting) assms discrete_cpo rep_uspec_belowI snd_monofun uspecdom_insert)

(* all element in uspec have the same dom  *)
lemma uspec_allDom [simp]: assumes "f\<in>(uspecSet\<cdot>S)"
  shows "ufclDom\<cdot>f=uspecDom\<cdot>S"
  by (metis (mono_tags, lifting) assms prod.sel(1) prod.sel(2) rep_abs_uspec undiscr_Discr uspecDom.rep_eq uspecSet.rep_eq uspecWell.simps uspec_obtain)

lemma uspecdom_chain: assumes "chain Y"
                        shows "\<And>i j. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Y j)"
  using assms is_ub_thelub uspecdom_eq by blast

lemma uspecdom_chain_lub: assumes "chain Y"
                            shows "\<And>i. uspecDom\<cdot>(Y i) = (\<Squnion>j. uspecDom\<cdot>(Y j))"
  using assms contlub_cfun_arg is_ub_thelub uspecdom_eq by blast

lemma uspecdom_lub_chain: assumes "chain Y"
                            shows "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(\<Squnion>j. Y j)"
  by (simp add: assms is_ub_thelub uspecdom_eq)





  subsection \<open>Ran\<close>


lemma uspecran_insert: "uspecRan\<cdot>S = undiscr (snd (snd (Rep_uspec S)))"
  by (simp add: uspecRan.rep_eq)

lemma uspecran_eq: assumes "S1\<sqsubseteq>S2"
  shows "uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
  by (metis (mono_tags, lifting) assms discrete_cpo rep_uspec_belowI snd_monofun uspecran_insert)

(* all element in uspec have the same Ran  *)
lemma uspec_allRan [simp]: assumes "f\<in>(uspecSet\<cdot>S)"
  shows "ufclRan\<cdot>f=uspecRan\<cdot>S"
  by (metis (mono_tags, hide_lams) assms prod.sel(1) prod.sel(2) rep_abs_uspec undiscr_Discr uspecRan.rep_eq uspecSet.rep_eq uspecWell.simps uspec_obtain)
  
lemma uspecran_chain: assumes "chain Y"
                        shows "\<And>i j. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Y j)"
  using assms is_ub_thelub uspecran_eq by blast

lemma uspecran_chain_lub: assumes "chain Y"
                            shows "\<And>i. uspecRan\<cdot>(Y i) = (\<Squnion>j. uspecRan\<cdot>(Y j))"
  using assms contlub_cfun_arg is_ub_thelub uspecran_eq by blast

lemma uspecran_lub_chain: assumes "chain Y"
                            shows "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(\<Squnion>j. Y j)"
  by (simp add: assms is_ub_thelub uspecran_eq)


subsection \<open>General Lemma 2\<close>

(* rule to prove the equality of uspec *)
lemma uspec_eqI: assumes "uspecSet\<cdot>S1 = uspecSet\<cdot>S2"
  and "uspecDom\<cdot>S1 = uspecDom\<cdot>S2"
  and "uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
shows "S1 = S2"
proof -
  obtain AA :: "'a uspec \<Rightarrow> 'a set" and CC :: "'a uspec \<Rightarrow> channel set" and CCa :: "'a uspec \<Rightarrow> channel set" where
    "\<And>u. uspecWell (AA u) (Discr (CC u)) (Discr (CCa u)) \<and> Abs_uspec (AA u, Discr (CC u), Discr (CCa u)) = u"
    by (meson uspec_obtain)
  then have "S2 = S1"
    by (metis (no_types) assms(1) assms(2) assms(3) prod.sel(1) prod.sel(2) rep_abs_uspec undiscr_Discr uspecDom.rep_eq uspecRan.rep_eq uspecSet.rep_eq)
  then show ?thesis
    by meson
qed
  
lemma uspec_eqI2: assumes "uspecSet\<cdot>S1 = uspecSet\<cdot>S2"
  and "uspecIsConsistent S1"
  shows "S1 = S2"
  by (metis (full_types) assms(1) assms(2) neq_emptyD uspecIsConsistent_def uspec_allDom uspec_allRan uspec_eqI)

(* if the upper uspec is consistent then the lower uspec is also consistent  *)
lemma uspec_isconsistent_below: assumes "S1\<sqsubseteq>S2" and "uspecIsConsistent S1"
  shows "uspecIsConsistent S2"
  by (metis assms(1) assms(2) eq_bottom_iff monofun_cfun_arg set_cpo_simps(3) uspecIsConsistent_def)


lemma uspec_belowI: assumes "uspecDom\<cdot>x = uspecDom\<cdot>y"
                        and "uspecRan\<cdot>x = uspecRan\<cdot>y"
                        and "uspecSet\<cdot>x \<sqsubseteq> uspecSet\<cdot>y"
                      shows "x \<sqsubseteq> y"
  proof -
    obtain x1 x2 x3 where x_def: "Rep_uspec x = (x1,x2,x3)"
      by (metis  surjective_pairing)
    obtain y1 y2 y3 where y_def: "Rep_uspec y = (y1,y2,y3)"
      by (metis  surjective_pairing)
    show ?thesis
      apply(simp add: below_uspec_def x_def y_def)
      by (metis SetPcpo.less_set_def assms(1) assms(2) assms(3) empty_iff fst_conv member_filter po_eq_conv snd_conv subset_eq undiscr_Discr uspecSet.rep_eq uspecWell.elims(2) uspecWell.elims(3) uspecdom_insert uspecran_insert x_def y_def)
   qed

lemma uspec_min:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecSet\<cdot>A = {}"
    shows "A \<sqsubseteq> B"
  by (simp add: SetPcpo.less_set_def assms(1) assms(2) assms(3) uspec_belowI)

lemma uspecset_insert: "uspecSet\<cdot>S = (fst (Rep_uspec S))"
  by (metis uspecSet.rep_eq)

lemma uspec_abs_set:
  assumes "uspecWell X Y Z"
  shows "uspecSet\<cdot>(Abs_uspec(X,Y,Z)) = X"
  by (simp add: assms uspecset_insert)

subsection \<open>USPEC\<close>

lemma uspec_dom[simp]: "s\<in>USPEC In Out \<Longrightarrow> uspecDom\<cdot>s = In"
  by (simp add: USPEC_def)

lemma uspec_ran[simp]: "s\<in>USPEC In Out \<Longrightarrow> uspecRan\<cdot>s= Out"
  by (metis (mono_tags) USPEC_def mem_Collect_eq)

subsection \<open>uspecLeast\<close>

lemma uspecleast_dom[simp]: "uspecDom\<cdot>(uspecLeast In Out) = In"
  by (simp add: uspecdom_insert uspecLeast.rep_eq)

lemma uspecleast_ran[simp]: "uspecRan\<cdot>(uspecLeast In Out) = Out"
  by (simp add: uspecran_insert uspecLeast.rep_eq)

lemma uspecleast_least: assumes "spec \<in> USPEC In Out"
  shows "uspecLeast In Out \<sqsubseteq> spec"
  apply(rule uspec_belowI)
  using assms uspec_dom uspecleast_dom apply blast
  using assms uspec_ran uspecleast_ran apply blast
  apply(simp add: uspecSet_def uspecLeast.rep_eq)
  by (simp add: SetPcpo.less_set_def)


subsection \<open>uspecMax\<close>

lemma uspecmax_dom[simp]: "uspecDom\<cdot>(uspecMax In Out) = In"
  by (simp add: uspecdom_insert uspecMax.rep_eq)

lemma uspecmax_ran[simp]: "uspecRan\<cdot>(uspecMax In Out) = Out"
  by (simp add: uspecran_insert uspecMax.rep_eq)

lemma uspecmax_max: assumes "spec \<in> USPEC In Out"
  shows "spec \<sqsubseteq> uspecMax In Out"
  apply(rule uspec_belowI)
  apply (metis (no_types) assms uspecdom_eq uspecleast_dom uspecleast_least uspecmax_dom)
   apply (metis (no_types) assms uspecleast_least uspecleast_ran uspecmax_ran uspecran_eq)
  apply(simp add: uspecMax.rep_eq uspecSet_def)
  by (metis (mono_tags, lifting) SetPcpo.less_set_def UNIV_I assms member_filter subsetI uspecSet.rep_eq uspec_allDom uspec_allRan uspec_dom uspec_ran)


lemma uspecleast_consistent: "(uspec \<noteq> uspecLeast (uspecDom\<cdot>uspec) (uspecRan\<cdot>uspec)) \<longleftrightarrow> uspecIsConsistent uspec"
  apply(simp add: uspecMax_def uspecIsConsistent_def)
  by (metis prod.sel(1) uspecLeast.rep_eq uspecSet.rep_eq uspec_eqI uspecleast_dom uspecleast_ran)




lemma uspec_exists[simp]: "USPEC In Out \<noteq> {}"
  unfolding USPEC_def
  by (metis (mono_tags, lifting) Collect_empty_eq_bot bot_empty_eq empty_iff uspecmax_dom uspecmax_ran)




subsection \<open>uspecUnion\<close>

thm uspecUnion_general_def
thm uspecFilter_def

lemma uspecUnion_general_well[simp]: "uspecWell
    (
    (Set.filter (\<lambda>f.  (uspecDom\<cdot>S1 = uspecDom\<cdot>S2)
                    \<and> (uspecRan\<cdot>S1 = uspecRan\<cdot>S2))
                 ((uspecSet\<cdot>S1) \<union> (uspecSet\<cdot>S2))))
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2))
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))"
  by auto

lemma uspecUnion_lub_well[simp]:
assumes "chain Y"
  shows "\<And>S1. uspecWell
    (Set.filter (\<lambda>f. ufclDom\<cdot>f = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>(Lub Y))
                     \<and> ufclRan\<cdot>f = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>(Lub Y)))
                   ((uspecSet\<cdot>S1) \<union> (uspecSet\<cdot>(Lub Y))))
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>(Lub Y)))
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>(Lub Y)))"
  by simp

(* Dom and ran for general (non cont) function *)                             
lemma uspecUnion_general_dom [simp]: "uspecDom\<cdot>(uspecUnion_general S1 S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  apply(simp add: uspecUnion_general_def)
  apply (simp add: uspecdom_insert)
  by (smt Un_iff member_filter prod.collapse prod.simps(1) rep_abs_uspec sup.idem sup_commute 
    undiscr_Discr uspecWell.elims(3) uspec_allDom uspec_allRan uspecdom_insert)

lemma uspecUnion_general_ran [simp]: "uspecRan\<cdot>(uspecUnion_general S1 S2) = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"
  apply(simp add: uspecUnion_general_def)
  apply (simp add: uspecran_insert)
  by (smt Un_iff member_filter prod.collapse prod.simps(1) rep_abs_uspec sup.idem sup_commute 
    undiscr_Discr uspecWell.elims(3) uspec_allDom uspec_allRan uspecran_insert)

lemma uspecUnion_general_sym: 
"uspecUnion_general = (\<lambda> S1 S2. (uspecUnion_general S2 S1))"
  apply (simp add: uspecUnion_general_def)
proof -
  have b0: "\<And>S1 S2. uspecDom\<cdot>S2 \<union> uspecDom\<cdot>S1 = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
    by (simp add: sup_commute)
  have b1: "\<And>S1 S2. (\<lambda>f. uspecDom\<cdot>S2 = uspecDom\<cdot>S1 \<and> uspecRan\<cdot>S2 = uspecRan\<cdot>S1)
    = (\<lambda>f. uspecDom\<cdot>S1 = uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>S2)"
    by auto
  show "uspecUnion_general =
    (\<lambda>S1 S2.
        Abs_uspec
         (Set.filter (\<lambda>f. uspecDom\<cdot>S2 = uspecDom\<cdot>S1 \<and> uspecRan\<cdot>S2 = uspecRan\<cdot>S1) (uspecSet\<cdot>S2 \<union> uspecSet\<cdot>S1),
          Discr (uspecDom\<cdot>S2 \<union> uspecDom\<cdot>S1), Discr (uspecRan\<cdot>S2 \<union> uspecRan\<cdot>S1)))"
    apply (subst b0)
    apply (subst b1)
  proof -
    have "\<forall>u ua. uspecUnion_general (u::'b uspec) ua = Abs_uspec (Set.filter (\<lambda>b. uspecDom\<cdot>u = 
      uspecDom\<cdot>ua \<and> uspecRan\<cdot>u = uspecRan\<cdot>ua) (uspecSet\<cdot>ua \<union> uspecSet\<cdot>u), Discr (uspecDom\<cdot>u \<union> uspecDom\<cdot>ua), 
      Discr (uspecRan\<cdot>ua \<union> uspecRan\<cdot>u))"
      by (simp add: sup_commute uspecUnion_general_def)
    then show "uspecUnion_general = (\<lambda>u ua. Abs_uspec (Set.filter (\<lambda>b. uspecDom\<cdot>(u::'b uspec) = 
      uspecDom\<cdot>ua \<and> uspecRan\<cdot>u = uspecRan\<cdot>ua) (uspecSet\<cdot>ua \<union> uspecSet\<cdot>u), Discr (uspecDom\<cdot>u \<union> uspecDom\<cdot>ua), 
      Discr (uspecRan\<cdot>ua \<union> uspecRan\<cdot>u)))"
      by meson
  qed
qed

lemma uspecUnion_mono[simp]: "\<And>S1. monofun (uspecUnion_general S1)"
  apply(rule monofunI, rule uspec_belowI)
    apply (simp add: uspecdom_eq, simp add: uspecran_eq)
  by (smt SetPcpo.less_set_def Un_iff fst_conv fst_monofun member_filter rep_abs_uspec rep_uspec_belowI subset_iff uspecSet.rep_eq uspecUnion_general_def uspecUnion_general_well uspecdom_eq uspecran_eq)

lemma uspecUnion_chain:
  assumes "chain Y"
   shows "\<And>S1. chain (\<lambda>i. (uspecUnion_general S1 (Y i)))"
  using ch2ch_monofun assms uspecUnion_mono by blast  

lemma ucpecunion_fit_filtered:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
    shows "Set.filter (\<lambda>f. (uspecDom\<cdot>A = uspecDom\<cdot>B)
                    \<and> (uspecRan\<cdot>A = uspecRan\<cdot>B))
                 ((uspecSet\<cdot>A)\<union>(uspecSet\<cdot>B)) =
                 (uspecSet\<cdot>A) \<union> (uspecSet\<cdot>B)"
  using assms by fastforce

lemma uspecUnion_general_easy:
  assumes "uspecDom\<cdot>S1 = uspecDom\<cdot>S2"
      and "uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
    shows "uspecUnion_general S1 S2 =  Abs_uspec ((
      ((uspecSet\<cdot>S1) \<union> (uspecSet\<cdot>S2))),
      (Discr (uspecDom\<cdot>S2)),
      (Discr (uspecRan\<cdot>S2)))"
  by (metis assms(1) assms(2) sup.idem ucpecunion_fit_filtered uspecUnion_general_def)

lemma uspec_union_general_notfit: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "uspecSet\<cdot>(uspecUnion_general A B) = {}"
  by (metis (mono_tags, lifting) Collect_empty_eq Set.filter_def assms prod.sel(1) rep_abs_uspec 
    uspecSet.rep_eq uspecUnion_general_def uspecUnion_general_well)

lemma uspecUnion_cont1[simp]: "\<And>S1. cont (uspecUnion_general S1)"
  apply(rule contI2)
  apply simp
  apply(rule allI, rule impI)
  proof -
    fix S1::"'a uspec" and Y::"nat \<Rightarrow> 'a uspec"
    assume a1: "chain Y"
    have h0: "chain (\<lambda>i. uspecUnion_general S1 (Y i))"
      by (simp add: a1 uspecUnion_chain)
    then have h1: "fst (Rep_uspec (\<Squnion>i::nat. uspecUnion_general S1 (Y i)))
                 = fst (\<Squnion>i::nat. Rep_uspec (uspecUnion_general S1 (Y i)))"
      by (metis cont2contlubE uspec_rep_cont)
    have h00: "chain (\<lambda>i. Rep_uspec (uspecUnion_general S1 (Y i)))"
      using a1 uspecUnion_chain ch2ch_monofun uspec_rep_mono by blast
    then have h2: "fst (\<Squnion>i::nat. Rep_uspec (uspecUnion_general S1 (Y i)))
                 = (\<Squnion>i::nat. fst (Rep_uspec (uspecUnion_general S1 (Y i))))"
      using lub_prod by fastforce
    have h3: "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Lub Y)"
      by (simp add: a1 uspecdom_lub_chain)
    have h4: "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Lub Y)"
      by (simp add: a1 uspecran_lub_chain)
    have h5: "\<And>A B. uspecDom\<cdot>A = uspecDom\<cdot>B \<and> uspecRan\<cdot>A = uspecRan\<cdot>B
      \<Longrightarrow> uspecWell (uspecSet\<cdot>A \<union> uspecSet\<cdot>B) (Discr (uspecDom\<cdot>B)) (Discr (uspecRan\<cdot>B))"
      using Un_iff by force
    have h6:  "\<And>A B. uspecDom\<cdot>A = uspecDom\<cdot>B \<and> uspecRan\<cdot>A = uspecRan\<cdot>B
  \<Longrightarrow> fst (Rep_uspec (Abs_uspec (uspecSet\<cdot>A \<union> uspecSet\<cdot>B, Discr (uspecDom\<cdot>B), Discr (uspecRan\<cdot>B))))
  = uspecSet\<cdot>A \<union> uspecSet\<cdot>B"
      using h5 by (metis fstI rep_abs_uspec)
    have h7:  "\<And>i. uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> fst (Rep_uspec (Abs_uspec (uspecSet\<cdot>S1 \<union> uspecSet\<cdot>(Y i), 
      Discr (uspecDom\<cdot>(Lub Y)), Discr (uspecRan\<cdot>(Lub Y)))))
      = uspecSet\<cdot>S1 \<union> uspecSet\<cdot>(Y i)"
      by (metis (full_types) h3 h4 h6)
    have h8: "uspecSet\<cdot>(Lub Y) = (\<Union>i. uspecSet\<cdot>(Y i))"
      by (metis a1 contlub_cfun_arg lub_eq_Union)
    have h9: "uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y) \<Longrightarrow>
    uspecSet\<cdot>(Lub Y) \<subseteq> (\<Union>i. uspecSet\<cdot>S1 \<union> uspecSet\<cdot>(Y i))"
      apply (subst h8)
      by blast
    have h10: "uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y) \<Longrightarrow>
    uspecSet\<cdot>S1 \<union> uspecSet\<cdot>(Lub Y) \<sqsubseteq> (\<Squnion>i. uspecSet\<cdot>S1 \<union> uspecSet\<cdot>(Y i))"
      using h9
      by (simp add: SetPcpo.less_set_def lub_eq_Union)
    have h11: "uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecUnion_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecUnion_general S1 (Y i))"
      apply(rule uspec_belowI)
      apply(simp add: uspecUnion_general_dom)
      using a1 uspecUnion_chain uspecUnion_general_dom uspecdom_lub_chain apply blast
      apply(simp add: uspecUnion_general_ran)
      using a1 uspecUnion_chain uspecUnion_general_ran uspecran_lub_chain apply blast
      apply(simp add: uspecSet_def)
      apply(simp add: h1)
      apply(simp add: h2)
      apply (simp add: uspecUnion_general_def)
      apply(subst h3, subst h4)
      apply(subst h3, subst h4)
      apply (simp add: setfilter_easy)
      apply (simp add: h6 h7)
      by (simp add: h10)
    have h12:  "uspecDom\<cdot>S1 \<noteq> uspecDom\<cdot>(Lub Y) \<or> uspecRan\<cdot>S1 \<noteq> uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecSet\<cdot>(uspecUnion_general S1 (\<Squnion>i. Y i)) = {}"
      using uspec_union_general_notfit by blast
    have h13: "uspecDom\<cdot>(uspecUnion_general S1 (\<Squnion>i. Y i)) = uspecDom\<cdot>(\<Squnion>i. uspecUnion_general S1 (Y i))"
      by (metis h0 h3 uspecUnion_general_dom uspecdom_lub_chain)
    have h14: "uspecRan\<cdot>(uspecUnion_general S1 (\<Squnion>i. Y i)) = uspecRan\<cdot>(\<Squnion>i. uspecUnion_general S1 (Y i))"
      by (metis h0 h4 uspecUnion_general_ran uspecran_lub_chain)
    have h15: "uspecDom\<cdot>S1 \<noteq> uspecDom\<cdot>(Lub Y) \<or> uspecRan\<cdot>S1 \<noteq> uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecUnion_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecUnion_general S1 (Y i))"
      apply (rule uspec_min)
      using a1 h0 uspecUnion_general_dom uspecdom_lub_chain
      using h13 apply blast
      using h14 apply blast
      using h12 by linarith
    show "uspecUnion_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecUnion_general S1 (Y i))"
      using h11 h15 by blast
  qed

lemma uspecUnion_cont2[simp]: "cont ( \<lambda>S1. \<Lambda> S2. (uspecUnion_general S1 S2))"
  apply(rule cont2cont_LAM)
  apply(simp only: uspecUnion_cont1)
  apply(subst uspecUnion_general_sym)
  by simp

lemma uspecUnion_apply: "\<And>A B. (\<Lambda> S1 S2. uspecUnion_general S1 S2)\<cdot>A\<cdot>B = (uspecUnion_general A B)"
  by (simp add: uspecUnion_def)

lemma uspecUnion_dom: "\<And>S1 S2. uspecDom\<cdot>(uspecUnion\<cdot>S1\<cdot>S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  by (simp add: uspecUnion_def)

lemma uspecUnion_ran: "\<And>S1 S2. uspecRan\<cdot>(uspecUnion\<cdot>S1\<cdot>S2) = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"
  by (simp add: uspecUnion_def)

lemma uspecUnion_set: 
"\<And>S1 S2. uspecSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2) = (Set.filter (\<lambda>f. (uspecDom\<cdot>S1 = uspecDom\<cdot>S2)
                                                      \<and> (uspecRan\<cdot>S1 = uspecRan\<cdot>S2))
                                         ((uspecSet\<cdot>S1) \<union> (uspecSet\<cdot>S2)))"
  apply(simp add: uspecUnion_def)
  apply(simp add: uspecUnion_general_def)
  unfolding uspecset_insert
  apply (subst rep_abs_uspec)
  apply (metis (no_types) uspecSet.rep_eq uspecUnion_general_well)
  by simp

lemma uspecUnion_set_condition: "\<And>S1 S2 x. x \<in> (uspecSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2))
                                 \<longleftrightarrow> ((x \<in> (uspecSet\<cdot>S1) \<or> x \<in> (uspecSet\<cdot>S2))
                                  \<and> uspecDom\<cdot>S1 = uspecDom\<cdot>S2
                                  \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>S2)"
  by (simp add: uspecUnion_set)

lemma uspecUnion_setrev_condition2:
  "\<And>S1 S2 x. x \<in> (uspecSet\<cdot>(uspecUnion\<cdot>S1\<cdot>S2))
         \<longleftrightarrow> (x \<in> (uspecSet\<cdot>S1) \<and> uspecDom\<cdot>S1 = uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>S2 
            \<or> x \<in> (uspecSet\<cdot>S2) \<and> uspecDom\<cdot>S1 = uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>S2)"
  using uspecUnion_set_condition by blast

lemma uspecUnion_commutative:
  assumes "uspecDom\<cdot>S1 = uspecDom\<cdot>S2 \<and> uspecDom\<cdot>S1 = uspecDom\<cdot>S3 \<and> uspecDom\<cdot>S2 = uspecDom\<cdot>S3"
      and "uspecRan\<cdot>S1 = uspecRan\<cdot>S2 \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>S3 \<and> uspecRan\<cdot>S2 = uspecRan\<cdot>S3"
    shows "uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3) = uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3"
  proof -
    have h1: "uspecDom\<cdot>(uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3)) = uspecDom\<cdot>(uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3)"
      by (simp add: sup_assoc uspecUnion_dom)
    have h2: "uspecRan\<cdot>(uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3)) = uspecRan\<cdot>(uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3)"
      by (simp add: sup_assoc uspecUnion_ran)
    have h3: "uspecSet\<cdot>(uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3)) = uspecSet\<cdot>(uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3)"
      apply auto
      apply (simp add: uspecUnion_setrev_condition2 uspecUnion_dom uspecUnion_ran)
      apply (simp add: assms(1) assms(2))
      by (simp add: assms(1) assms(2) uspecUnion_dom uspecUnion_ran uspecUnion_set_condition)
    show "uspecUnion\<cdot>S1\<cdot>(uspecUnion\<cdot>S2\<cdot>S3) = uspecUnion\<cdot>(uspecUnion\<cdot>S1\<cdot>S2)\<cdot>S3"
      by (metis h1 h2 h3 uspec_eqI)
  qed

lemma uspecUnion_sym: "\<And>S1 S2. uspecUnion\<cdot>S1\<cdot>S2 = uspecUnion\<cdot>S2\<cdot>S1"
  by (metis uspecUnion_apply uspecUnion_def uspecUnion_general_sym)

lemma uspecUnion_consistent: assumes "uspecIsConsistent S1 \<or> uspecIsConsistent S2"
                                  and "uspecDom\<cdot>S1 = uspecDom\<cdot>S2 \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
                                shows "uspecIsConsistent (uspecUnion\<cdot>S1\<cdot>S2)"
  apply (insert assms)
  apply (simp add: uspecIsConsistent_def)
  by (metis Un_empty ucpecunion_fit_filtered uspecUnion_set)
 
lemma uspecunion_rule1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "P (Abs_uspec ((uspecSet\<cdot>A) \<union> (uspecSet\<cdot>B),
          Discr (uspecDom\<cdot>A), Discr (uspecRan\<cdot>A)))"
    shows "P (uspecUnion\<cdot>A\<cdot>B)"
  apply (simp add: uspecUnion_def)
  using assms by (simp add: uspecUnion_general_easy)

lemma uspec_union_notfit: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "uspecSet\<cdot>(uspecUnion\<cdot>A\<cdot>B) = {}"
  by (metis assms uspecUnion_apply uspecUnion_def uspec_union_general_notfit)


subsection \<open>uspecFilter\<close> 

lemma uspecFilterSubset: 
"\<And>S::'a uspec. \<forall>f::'a \<in> (Set.filter P (uspecSet\<cdot>S)). f \<in> (uspecSet\<cdot>S)"
  by simp

lemma uspecFilter_general_well[simp]: "\<And>S P. uspecWell (Set.filter P (uspecSet\<cdot>S))
    (Discr (uspecDom\<cdot>S)) (Discr (uspecRan\<cdot>S))"
  by auto
        
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
      by (simp add: a1 uspecdom_eq)
    have h2: "uspecRan\<cdot>x = uspecRan\<cdot>y"
      by (simp add: a1 uspecran_eq)
    have h3: "fst (Rep_uspec x) \<subseteq> fst (Rep_uspec y)"
      by (metis SetPcpo.less_set_def a1 fst_monofun rep_uspec_belowI)
    show "uspecFilter_general P x \<sqsubseteq> uspecFilter_general P y"
      apply (rule uspec_belowI)
      apply (simp add: h1 uspecFilter_general_dom)
      apply (simp add: h2 uspecFilter_general_ran)
      unfolding SetPcpo.less_set_def
      apply (simp add: uspecFilter_general_def)
      apply (simp add: uspecset_insert)
      using h3 by auto
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
    have h0: "chain (\<lambda>i. uspecFilter_general P (Y i))"
      by (meson a1 monofunE po_class.chain_def uspecFilter_mono)
    then have h1: "fst (Rep_uspec (\<Squnion>i::nat. uspecFilter_general P (Y i)))
                 = fst (\<Squnion>i::nat. Rep_uspec (uspecFilter_general P (Y i)))"
      by (metis cont2contlubE uspec_rep_cont)
    have h00: "chain (\<lambda>i. Rep_uspec (uspecFilter_general P (Y i)))"
      using a1 uspecFilter_chain ch2ch_monofun uspec_rep_mono by blast
    then have h2: "fst (\<Squnion>i::nat. Rep_uspec (uspecFilter_general P (Y i)))
                 = (\<Squnion>i::nat. fst (Rep_uspec (uspecFilter_general P (Y i))))"
      using lub_prod by fastforce
    have h3: "(uspecSet\<cdot>(Lub Y)) \<subseteq> (\<Union>i.(uspecSet\<cdot>(Y i)))"
      by (simp add: a1 contlub_cfun_arg lub_eq_Union)
    show "uspecFilter_general P (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecFilter_general P (Y i))"
      apply(rule uspec_belowI)
      apply(simp add: uspecFilter_general_dom)
      using a1 uspecFilter_chain uspecFilter_general_dom uspecdom_lub_chain apply blast
      apply(simp add: uspecFilter_general_ran)
      using a1 uspecFilter_chain uspecFilter_general_ran uspecran_lub_chain apply blast
      apply(simp add: uspecSet_def)
      apply(simp add: h1)
      apply(simp add: h2)
      apply (simp add: uspecFilter_general_def)
      unfolding SetPcpo.less_set_def
      unfolding SetPcpo.lub_eq_Union
      using h3 subsetI by fastforce
  qed

lemma uspecfilter_insert: "uspecFilter P\<cdot>S = uspecFilter_general P S"
  by (simp add: uspecFilter_def)

lemma uspecfilter_condition: "\<And>x. x \<in> uspecSet\<cdot>(uspecFilter P\<cdot>A) \<Longrightarrow> P x"
  by (simp add: uspecFilter_general_def uspecfilter_insert uspecset_insert)

lemma uspecfilter_included: "\<And>x.  x \<in> uspecSet\<cdot>(uspecFilter P\<cdot>A) \<Longrightarrow> x \<in> uspecSet\<cdot>A"
  by (simp add: uspecFilter_general_def uspecSet.rep_eq uspecfilter_insert)


subsection \<open>uspecInter\<close> 

lemma uspecInter_general_well[simp]: "\<And>S1 S2. uspecWell    
    ((uspecSet\<cdot>S1) \<inter> (uspecSet\<cdot>S2))
    (Discr (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2))
    (Discr (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2))"
  by (metis (no_types, hide_lams) Int_iff sup.idem undiscr_Discr uspecWell.elims(3) uspec_allDom uspec_allRan)

lemma uspecInter_general_sym: 
"uspecInter_general = (\<lambda> S1 S2. (uspecInter_general S2 S1))"
  apply (simp add: uspecInter_general_def inf_commute)
  by (simp add: sup_commute)
        
(* Dom and ran for general (non cont) function *)                             
lemma uspecInter_general_dom: "uspecDom\<cdot>(uspecInter_general S1 S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  apply(simp add: uspecInter_general_def)
  by (metis fstI prod.sel(2) rep_abs_uspec undiscr_Discr uspecInter_general_well uspecdom_insert)

lemma uspecInter_general_ran: "uspecRan\<cdot>(uspecInter_general S1 S2) = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"
  apply(simp add: uspecInter_general_def)
  by (metis prod.sel(2) rep_abs_uspec undiscr_Discr uspecInter_general_well uspecran_insert)

lemma uspecInter_mono[simp]: "\<And>S1. monofun (uspecInter_general S1)"
  proof (rule monofunI)
    fix S1::"'a uspec" and x::"'a uspec" and y::"'a uspec"
    assume a1: "x \<sqsubseteq> y"
    have h1: "uspecDom\<cdot>x = uspecDom\<cdot>y"
      by (simp add: a1 uspecdom_eq)
    have h2: "uspecRan\<cdot>x = uspecRan\<cdot>y"
      by (simp add: a1 uspecran_eq)
    have h3: " (uspecSet\<cdot>S1) \<inter> (uspecSet\<cdot>x)
            \<sqsubseteq> (uspecSet\<cdot>S1) \<inter> (uspecSet\<cdot>y)"
      unfolding SetPcpo.less_set_def
      by (metis SetPcpo.less_set_def a1 inf.idem inf_le2 inf_mono monofun_cfun_arg)
    show "(uspecInter_general S1 x) \<sqsubseteq> (uspecInter_general S1 y)"
      apply(rule uspec_belowI)
      apply(simp add: uspecInter_general_dom)
      apply(simp only: h1)
      apply(simp add: uspecInter_general_ran)
      apply(simp only: h2)
      apply(simp add: uspecInter_general_def)
      apply (simp add: uspecset_insert)
      by (metis fstI h3 rep_abs_uspec uspecInter_general_well uspecSet.rep_eq)
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
    have h0: "chain (\<lambda>i. uspecInter_general S1 (Y i))"
      by (simp add: a1 uspecInter_chain)
    then have h1: "fst (Rep_uspec (\<Squnion>i::nat. uspecInter_general S1 (Y i)))
                 = fst (\<Squnion>i::nat. Rep_uspec (uspecInter_general S1 (Y i)))"
      by (metis cont2contlubE uspec_rep_cont)
    have h00: "chain (\<lambda>i. Rep_uspec (uspecInter_general S1 (Y i)))"
      using a1 uspecInter_chain ch2ch_monofun uspec_rep_mono by blast
    then have h2: "fst (\<Squnion>i::nat. Rep_uspec (uspecInter_general S1 (Y i)))
                 = (\<Squnion>i::nat. fst (Rep_uspec (uspecInter_general S1 (Y i))))"
      using lub_prod by fastforce
    have h3: "\<And>i. uspecDom\<cdot>(Y i) = uspecDom\<cdot>(Lub Y)"
      by (simp add: a1 uspecdom_lub_chain)
    have h4: "\<And>i. uspecRan\<cdot>(Y i) = uspecRan\<cdot>(Lub Y)"
      by (simp add: a1 uspecran_lub_chain)
    have h5: "\<And>A B. uspecDom\<cdot>A = uspecDom\<cdot>B \<and> uspecRan\<cdot>A = uspecRan\<cdot>B
      \<Longrightarrow> uspecWell (uspecSet\<cdot>A \<inter> uspecSet\<cdot>B) (Discr (uspecDom\<cdot>B)) (Discr (uspecRan\<cdot>B))"
      using Un_iff by force
    have h6:  "\<And>A B. uspecDom\<cdot>A = uspecDom\<cdot>B \<and> uspecRan\<cdot>A = uspecRan\<cdot>B
  \<Longrightarrow> fst (Rep_uspec (Abs_uspec (uspecSet\<cdot>A \<inter> uspecSet\<cdot>B, Discr (uspecDom\<cdot>B), Discr (uspecRan\<cdot>B))))
  = uspecSet\<cdot>A \<inter> uspecSet\<cdot>B"
      using h5 by (metis fstI rep_abs_uspec)
    have h7:  "\<And>i. uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> fst (Rep_uspec (Abs_uspec (uspecSet\<cdot>S1 \<inter> uspecSet\<cdot>(Y i), 
      Discr (uspecDom\<cdot>(Lub Y)), Discr (uspecRan\<cdot>(Lub Y)))))
      = uspecSet\<cdot>S1 \<inter> uspecSet\<cdot>(Y i)"
      by (metis (full_types) h3 h4 h6)
    have h8: "uspecSet\<cdot>(Lub Y) = (\<Union>i. uspecSet\<cdot>(Y i))"
      by (metis a1 contlub_cfun_arg lub_eq_Union)
    have h9: "uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y) \<Longrightarrow>
     uspecSet\<cdot>S1 \<inter> uspecSet\<cdot>(Lub Y) \<subseteq> (\<Squnion>i. uspecSet\<cdot>S1 \<inter> uspecSet\<cdot>(Y i))"
      apply (subst h8)
      unfolding SetPcpo.lub_eq_Union
      by blast
    have h10: "uspecDom\<cdot>S1 = uspecDom\<cdot>(Lub Y) \<and> uspecRan\<cdot>S1 = uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecInter_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecInter_general S1 (Y i))"
      apply(rule uspec_belowI)
      apply(simp add: uspecInter_general_dom)
      using a1 uspecInter_chain uspecInter_general_dom uspecdom_lub_chain apply blast
      apply(simp add: uspecInter_general_ran)
      using a1 uspecInter_chain uspecInter_general_ran uspecran_lub_chain apply blast
      apply(simp add: uspecSet_def)
      apply(simp add: h1)
      apply(simp add: h2)
      apply (simp add: uspecInter_general_def)
      apply(subst h3, subst h4)
      apply (simp add: setfilter_easy)
      apply (simp add: h6 h7)
      unfolding SetPcpo.less_set_def
      by (simp add: h9)
    have h11: "uspecDom\<cdot>S1 \<noteq> uspecDom\<cdot>(Lub Y) \<or> uspecRan\<cdot>S1 \<noteq> uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecSet\<cdot>(uspecInter_general S1 (Lub Y)) = {}"
      by (metis (no_types, lifting) disjoint_iff_not_equal fst_conv rep_abs_uspec uspecInter_general_def 
        uspecInter_general_well uspecSet.rep_eq uspec_allDom uspec_allRan)
    have h12:  "uspecDom\<cdot>S1 \<noteq> uspecDom\<cdot>(Lub Y) \<or> uspecRan\<cdot>S1 \<noteq> uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecSet\<cdot>(uspecInter_general S1 (\<Squnion>i. Y i)) = {}"
      using h11 by blast
    have h13: "uspecDom\<cdot>(uspecInter_general S1 (\<Squnion>i. Y i)) = uspecDom\<cdot>(\<Squnion>i. uspecInter_general S1 (Y i))"
      by (metis h0 h3 uspecInter_general_dom uspecdom_lub_chain)
    have h14: "uspecRan\<cdot>(uspecInter_general S1 (\<Squnion>i. Y i)) = uspecRan\<cdot>(\<Squnion>i. uspecInter_general S1 (Y i))"
      by (metis h0 h4 uspecInter_general_ran uspecran_lub_chain)
    have h15: "uspecDom\<cdot>S1 \<noteq> uspecDom\<cdot>(Lub Y) \<or> uspecRan\<cdot>S1 \<noteq> uspecRan\<cdot>(Lub Y)
      \<Longrightarrow> uspecInter_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecInter_general S1 (Y i))"
      apply (rule uspec_min)
      using a1 h0 uspecInter_general_dom uspecdom_lub_chain
      using h13 apply blast
      using h14 apply blast
      using h12 by linarith
    show "uspecInter_general S1 (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. uspecInter_general S1 (Y i))"
      using h10 h15 by blast
  qed

lemma uspecInter_cont2[simp]: "cont ( \<lambda>S1. \<Lambda> S2. (uspecInter_general S1 S2))"
  apply(rule cont2cont_LAM)
  apply(simp only: uspecInter_cont1)
  apply(subst uspecInter_general_sym)
  by simp

lemma uspecInter_insert: "uspecInter\<cdot>S1\<cdot>S2 = uspecInter_general S1 S2"
  by (simp add: uspecInter_def)

lemma uspecInter_apply: "\<And>A B. (\<Lambda> S1 S2. uspecInter_general S1 S2)\<cdot>A\<cdot>B = uspecInter_general A B"
  by simp

lemma uspecInter_dom: "\<And>S1 S2. uspecDom\<cdot>(uspecInter\<cdot>S1\<cdot>S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  by (simp add: uspecInter_def uspecInter_general_dom)

lemma uspecInter_ran: "\<And>S1 S2. uspecRan\<cdot>(uspecInter\<cdot>S1\<cdot>S2) = (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)"
  by (simp add: uspecInter_def uspecInter_general_ran)

lemma uspecInter_set: 
"\<And>S1 S2. uspecSet\<cdot>(uspecInter\<cdot>S1\<cdot>S2) = ((uspecSet\<cdot>S1) \<inter> (uspecSet\<cdot>S2))"
  apply(simp add: uspecInter_def)
  apply(simp add: uspecInter_general_def)
  by (metis fst_conv rep_abs_uspec uspecInter_general_well uspecset_insert)

lemma uspecinter_rule1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
     and  "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "P (Abs_uspec ((uspecSet\<cdot>A) \<inter> (uspecSet\<cdot>B),
          Discr (uspecDom\<cdot>A), Discr (uspecRan\<cdot>A)))"
    shows "P (uspecInter\<cdot>A\<cdot>B)"
 apply (simp add: uspecInter_insert uspecInter_general_def)
 using assms(1) assms(2) assms(3) by auto

lemma uspecinter_incl1: "\<forall>x\<in> (uspecSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). x \<in> (uspecSet\<cdot>A)"
  by (simp add: uspecInter_set)

lemma uspecinter_incl2: "\<forall>x\<in> (uspecSet\<cdot>(uspecInter\<cdot>A\<cdot>B)). x \<in> (uspecSet\<cdot>B)"
  by (simp add: uspecInter_set)

lemma uspec_inter_notfit: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "uspecSet\<cdot>(uspecInter\<cdot>A\<cdot>B) = {}"
  by (metis Int_emptyI assms uspecInter_set uspec_allDom uspec_allRan)


subsection \<open>uspecFlatten\<close>

lemma uspec_set_filter_empty: "uspec_set_filter In Out\<cdot>({}) = {}"
  apply (simp add: uspec_set_filter_def)
proof -
  have f1: "Abs_cfun (Set.filter (\<lambda>u. uspecDom\<cdot>(u::'a uspec) = In \<and> uspecRan\<cdot>u = Out))\<cdot> (Collect bot) 
    = Set.filter (\<lambda>u. uspecDom\<cdot>u = In \<and> uspecRan\<cdot>u = Out) (Collect bot)"
    by (meson beta_cfun setfilter_cont)
have "{u. (u::'a uspec) \<in> Collect bot \<and> uspecDom\<cdot>u = In \<and> uspecRan\<cdot>u = Out} = {}"
  by blast
  then show "(\<Lambda> U. Set.filter (\<lambda>u. uspecDom\<cdot>(u::'a uspec) = In \<and> uspecRan\<cdot>u = Out) U)\<cdot> {} = {}"
    using f1 by (metis (no_types) Set.filter_def bot_set_def)
qed

lemma uspec_filter_insert: 
  "(\<Lambda> uspecs. Set.filter (\<lambda>uspec. uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out) uspecs)\<cdot>uspecs
    =  Set.filter (\<lambda>uspec. uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out) uspecs"
  by (simp add: setfilter_cont)

lemma uspecflatten_well:
 "uspecWell 
  (setflat\<cdot>((Rep_cfun uspecSet)  ` (uspec_set_filter In Out\<cdot>uspecs)))
  (Discr In) (Discr Out)"
proof -
  have b0: "\<And>f g. f \<in> uspecSet\<cdot>g \<Longrightarrow>
      g \<in> Set.filter (\<lambda>uspec. uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out) uspecs
      \<Longrightarrow> uspecDom\<cdot>g = In \<and> uspecRan\<cdot>g = Out"
    by simp
  have b1: "\<And>f g. f \<in> uspecSet\<cdot>g \<Longrightarrow> g \<in> (uspec_set_filter In Out\<cdot>uspecs) \<Longrightarrow> ufclDom\<cdot>f = In
    \<and> ufclRan\<cdot>f = Out"
    apply(simp add: uspec_set_filter_def)
    using b0 uspec_filter_insert by blast
  show ?thesis 
    using b1 setflat_obtain by fastforce
qed

lemma uspecflatten_dom_help : "uspecDom\<cdot>(Abs_uspec 
  ((setflat\<cdot>((Rep_cfun uspecSet)  ` (uspec_set_filter In Out\<cdot>uspecs))), Discr In, Discr Out)) = In"
  apply (simp add: uspecDom_def uspecFlatten_def)
  by (metis (no_types) fst_conv rep_abs_uspec snd_conv undiscr_Discr uspecDom.abs_eq uspecdom_insert uspecflatten_well)

lemma uspecflatten_ran_help : "uspecRan\<cdot>(Abs_uspec 
  ((setflat\<cdot>((Rep_cfun uspecSet)  ` (uspec_set_filter In Out\<cdot>uspecs))), Discr In, Discr Out)) = Out"
  apply (simp add: uspecRan_def uspecFlatten_def)
  by (metis (no_types) rep_abs_uspec snd_conv undiscr_Discr uspecRan.abs_eq uspecran_insert uspecflatten_well)

lemma uspecflatten_monofun: "monofun (\<lambda> uspecs. Abs_uspec 
  ((setflat\<cdot>((Rep_cfun uspecSet)  ` (uspec_set_filter In Out\<cdot>uspecs))), Discr In, Discr Out))"
  apply (rule monofunI)
  apply (rule uspec_belowI)
  apply (simp add: uspecflatten_dom_help)
  apply (simp add: uspecflatten_ran_help)
  by (metis cont_pref_eq1I fst_conv image_mono rep_abs_uspec set_cpo_simps(1) uspecflatten_well uspecset_insert)

lemma uspec_abs_chain: "\<And>x y.  chain Y \<Longrightarrow> (\<forall>i. uspecWell (Y i) In Out) \<Longrightarrow> uspecWell (\<Squnion>i. Y i) In Out \<Longrightarrow>
         chain (\<lambda>i. Abs_uspec (Y i, In, Out)) \<Longrightarrow> Abs_uspec (\<Squnion>i. Y i, In, Out) \<sqsubseteq> (\<Squnion>i. Abs_uspec (Y i, In, Out))"
proof -
  fix x :: 'a and y :: 'b
  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i. Abs_uspec (Y i, In, Out))"
  assume a3: "\<forall>i. uspecWell (Y i) In Out"
  assume a4: "uspecWell (\<Squnion>i. Y i) In Out"
  obtain nn :: "'c set \<Rightarrow> (nat \<Rightarrow> 'c set) \<Rightarrow> nat" where
    f5: "\<forall>f C. (\<not> chain f \<or> f (nn C f) \<notsqsubseteq> C) \<or> Lub f \<sqsubseteq> C"
    by (meson lub_below)
  have f6: "\<forall>f n. \<not> chain f \<or> (f n::'c uspec) \<sqsubseteq> Lub f"
    by (meson is_ub_thelub)
  have f7: "\<forall>C d da. \<not> uspecWell (C::'c set) d da \<or> Rep_uspec (Abs_uspec (C, d, da)) = (C, d, da)"
    by (meson rep_abs_uspec)
  have f8: "\<forall>u. \<exists>C Ca Cb. Abs_uspec (C::'c set, Discr Ca, Discr Cb) = u \<and> uspecWell C (Discr Ca) (Discr Cb)"
    by (meson uspec_obtain)
  have "\<forall>x0. (Abs_uspec (v1_2 (x0::'c uspec), Discr (v2_1 x0), Discr (v3_0 x0)) = x0 \<and> uspecWell (v1_2 x0) (Discr (v2_1 x0)) (Discr (v3_0 x0))) = (Abs_uspec (v1_2 x0, Discr (v2_1 x0), Discr (v3_0 x0)) = x0 \<and> uspecWell (v1_2 x0) (Discr (v2_1 x0)) (Discr (v3_0 x0)))"
    by force
  then obtain CC :: "'c uspec \<Rightarrow> 'c set" and CCa :: "'c uspec \<Rightarrow> channel set" and CCb :: "'c uspec \<Rightarrow> channel set" where
    f9: "(CC (\<Squnion>n. Abs_uspec (Y n, In, Out)), Discr (CCa (\<Squnion>n. Abs_uspec (Y n, In, Out))), Discr (CCb (\<Squnion>n. Abs_uspec (Y n, In, Out)))) = Rep_uspec (\<Squnion>n. Abs_uspec (Y n, In, Out))"
    using f8 f7 by metis
  then have f10: "(Y elem_13, In, Out) \<sqsubseteq> (CC (\<Squnion>n. Abs_uspec (Y n, In, Out)), Discr (CCa (\<Squnion>n. Abs_uspec (Y n, In, Out))), Discr (CCb (\<Squnion>n. Abs_uspec (Y n, In, Out))))"
    using f7 f6 a3 a2 by (metis below_uspec_def)
  have "Abs_uspec (Y (nn (CC (\<Squnion>n. Abs_uspec (Y n, In, Out))) Y), In, Out) \<sqsubseteq> (\<Squnion>n. Abs_uspec (Y n, In, Out))"
    using f6 a2 by meson
  then have "(Y (nn (CC (\<Squnion>n. Abs_uspec (Y n, In, Out))) Y), In, Out) \<sqsubseteq> (CC (\<Squnion>n. Abs_uspec (Y n, In, Out)), Discr (CCa (\<Squnion>n. Abs_uspec (Y n, In, Out))), Discr (CCb (\<Squnion>n. Abs_uspec (Y n, In, Out))))"
    using f9 a3 by (simp add: below_uspec_def)
  then have "Lub Y \<sqsubseteq> CC (\<Squnion>n. Abs_uspec (Y n, In, Out))"
    using f5 a1 by (meson Pair_below_iff)
  then have "(Lub Y, In, Out) \<sqsubseteq> (CC (\<Squnion>n. Abs_uspec (Y n, In, Out)), Discr (CCa (\<Squnion>n. Abs_uspec (Y n, In, Out))), Discr (CCb (\<Squnion>n. Abs_uspec (Y n, In, Out))))"
    using f10 by (meson Pair_below_iff)
  then show "Abs_uspec (\<Squnion>n. Y n, In, Out) \<sqsubseteq> (\<Squnion>n. Abs_uspec (Y n, In, Out))"
    using f9 a4 by (simp add: below_uspec_def)
qed

lemma uspecflatten_cont: "cont (\<lambda> uspecs. Abs_uspec 
  ((setflat\<cdot>((Rep_cfun uspecSet) ` (uspec_set_filter In Out\<cdot>uspecs))), Discr In, Discr Out))"
  apply (rule Cont.contI2)
  apply (simp add: uspecflatten_monofun)
  proof -
    fix Y::"nat \<Rightarrow> 'a uspec set"
    assume a1: "chain Y"
    have b0: "Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(\<Squnion>i. Y i)), Discr In, Discr Out)
     = Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` (\<Squnion>i. uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out)"
      by (simp add: a1 contlub_cfun_arg)
    have b1: "Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` (\<Squnion>i. uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out)
     = Abs_uspec (setflat\<cdot>(\<Squnion>i. Rep_cfun uspecSet ` ( uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out)"
      by (metis image_UN lub_eq_Union)
    have "chain (\<lambda>n. uspec_set_filter In Out\<cdot>(Y n))"
      by (meson a1 monofun_cfun_arg po_class.chain_def)
    then have b2: "Abs_uspec (setflat\<cdot>(\<Squnion>i. Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out)
     = Abs_uspec (\<Squnion>i. setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out)"
      by (simp add: SetPcpo.less_set_def contlub_cfun_arg image_mono po_class.chain_def)
    have b3: "\<And>i. uspecWell (setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>(Y i)))) (Discr In) (Discr Out)"
      using uspecflatten_well by blast
    have b4: "uspecWell (\<Squnion>i. setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>(Y i)))) (Discr In) (Discr Out)"
      unfolding lub_eq_Union
      using b3 by auto
    have b5:  "Abs_uspec (\<Squnion>i. setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out)
     \<sqsubseteq> (\<Squnion>i. Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>(Y i))), Discr In, Discr Out))"
      apply (rule uspec_abs_chain)
      apply (metis (no_types, lifting) SetPcpo.less_set_def a1 image_mono monofun_cfun_arg 
        po_class.chainE po_class.chain_def)
      using b3 apply blast
      using b4 apply blast
    proof -
  have f1: "\<forall>A Aa c. (A::'a set set) \<notsqsubseteq> Aa \<or> (c\<cdot>A::'a set) \<sqsubseteq> c\<cdot>Aa"
      using cont_pref_eq1I by blast
  obtain nn :: "(nat \<Rightarrow> 'a uspec) \<Rightarrow> nat" where
    f2: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
  using po_class.chain_def by moura
  have f3: "setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot> (Y (nn (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out))))) = fst (Rep_uspec (Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot> (Y (nn (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out))))), Discr In, Discr Out)))"
    by (metis fst_conv rep_abs_uspec uspecflatten_well)
  have f4: "setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot> (Y (Suc (nn (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out)))))) = fst (Rep_uspec (Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot> (Y (Suc (nn (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out)))))), Discr In, Discr Out)))"
    by (metis fst_conv rep_abs_uspec uspecflatten_well)
  have "\<forall>n. uspec_set_filter In Out\<cdot>(Y n) \<sqsubseteq> uspec_set_filter In Out\<cdot>(Y (Suc n))"
    by (metis (no_types) \<open>chain (\<lambda>n. uspec_set_filter In Out\<cdot>(Y n))\<close> po_class.chain_def)
  then have "Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot> (Y (nn (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out))))), Discr In, Discr Out) \<sqsubseteq> Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot> (Y (Suc (nn (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out)))))), Discr In, Discr Out)"
    using f4 f3 f1 by (simp add: SetPcpo.less_set_def image_mono uspec_belowI uspecflatten_dom_help uspecflatten_ran_help uspecset_insert)
  then show "chain (\<lambda>n. Abs_uspec (setflat\<cdot> (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y n)), Discr In, Discr Out))"
    using f2 by meson
qed
    show "chain (\<lambda>i. Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y i)), Discr In, Discr Out)) \<Longrightarrow>
         Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(\<Squnion>i. Y i)), Discr In, Discr Out) \<sqsubseteq>
         (\<Squnion>i. Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>(Y i)), Discr In, Discr Out))"
      by (simp add: b0 b1 b2 b5)
  qed

lemma uspecflatten_insert: "uspecFlatten In Out\<cdot>uspecs = 
  Abs_uspec ((setflat\<cdot>((Rep_cfun uspecSet)  ` (uspec_set_filter In Out\<cdot>uspecs))), Discr In, Discr Out)"
  by (simp add: uspecFlatten_def uspecflatten_cont)

lemma uspecflatten_dom [simp]: "uspecDom\<cdot>(uspecFlatten In Out\<cdot>uspecs) = In"
  by (simp add: uspecFlatten_def uspecflatten_cont uspecflatten_dom_help)

lemma uspecflatten_ran [simp]: "uspecRan\<cdot>(uspecFlatten In Out\<cdot>uspecs) = Out"
  by (simp add: uspecFlatten_def uspecflatten_cont uspecflatten_ran_help)

(* Every Element in S1 has a LARGER element in S2 *)
lemma uspecflatten_mono2: assumes "\<And>b. b \<in> S1 \<Longrightarrow> (\<exists>c. c \<in> S2 \<and> b\<sqsubseteq>c)"
  shows "uspecFlatten In Out\<cdot>S1 \<sqsubseteq> uspecFlatten In Out\<cdot>S2"
proof (rule uspec_belowI) 
  have "(\<And>b. b\<in>(uspec_set_filter In Out\<cdot>S1) \<Longrightarrow>( \<exists>c. c\<in>(uspec_set_filter In Out\<cdot>S2) \<and> b\<sqsubseteq>c))"
    by (metis (no_types, lifting) assms member_filter uspec_filter_insert uspec_set_filter_def uspecdom_eq uspecran_eq)  
  hence "(\<And>b. b\<in>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>S1)) \<Longrightarrow>( \<exists>c. c\<in> ((Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>S2))) \<and> b \<subseteq> c))"
    by (smt SetPcpo.less_set_def imageE image_eqI monofun_cfun_arg)
  hence "(setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>S1))) \<subseteq> (setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>S2)))"
    by (simp add: setflatten_mono2)   
  hence "(Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>S1), Discr In, Discr Out)) \<sqsubseteq>
   (Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>S2), Discr In, Discr Out))"
    by (metis SetPcpo.less_set_def below_uspec_def fstI fst_below_iff rep_abs_uspec snd_conv uspecflatten_well)
  thus "uspecSet\<cdot>(uspecFlatten In Out\<cdot>S1) \<sqsubseteq> uspecSet\<cdot>(uspecFlatten In Out\<cdot>S2)"
    unfolding uspecFlatten_def 
    by (simp add: monofun_cfun_arg uspecflatten_cont)
  show "uspecDom\<cdot>(uspecFlatten In Out\<cdot>S1) = uspecDom\<cdot>(uspecFlatten In Out\<cdot>S2)" by simp
  show "uspecRan\<cdot>(uspecFlatten In Out\<cdot>S1) = uspecRan\<cdot>(uspecFlatten In Out\<cdot>S2)" by simp
qed

lemma uspecflatten_image_monofun: 
  shows  "monofun(\<lambda> f. uspecFlatten In Out\<cdot>(f ` S))" (is "monofun ?f")
proof(rule monofunI)
  fix x y :: "'a \<Rightarrow> 'b uspec"
  assume "x \<sqsubseteq> y"
  hence "\<And> b. b \<in> (y ` S) \<Longrightarrow>  \<exists>c. c\<in> (x ` S) \<and> c\<sqsubseteq>b"
    by (metis fun_below_iff imageE image_eqI)
  thus "?f x \<sqsubseteq> ?f y"
    by (metis (no_types, lifting) \<open>x \<sqsubseteq> y\<close> f_inv_into_f fun_below_iff image_eqI inv_into_into uspecflatten_mono2)
qed

lemma uspecflatten_elen: assumes "f \<in> uspecSet\<cdot>(uspecFlatten In Out\<cdot>H)"
  obtains h where "h \<in> H" and  "f \<in> uspecSet\<cdot>h"
proof -
  have f1: "uspecFlatten In Out\<cdot>H \<noteq> uspecLeast In Out"
    by (metis assms empty_iff prod.sel(1) uspecLeast.rep_eq uspecSet.rep_eq)
  have f2: "uspecSet\<cdot>(uspecFlatten In Out\<cdot>H) = setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>H))"
    by (metis (no_types, lifting) Abs_cfun_inverse2 prod.sel(1) rep_abs_uspec uspecFlatten_def 
    uspecSet.rep_eq uspecflatten_cont uspecflatten_well)
  have f3: "f \<in>  (setflat\<cdot>(Rep_cfun uspecSet ` (uspec_set_filter In Out\<cdot>H)))"
    using assms f2 by auto
  then show ?thesis
proof -
  obtain AA :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
"\<forall>x0 x1. (\<exists>v2. v2 \<in> x0 \<and> x1 \<in> v2) = (AA x0 x1 \<in> x0 \<and> x1 \<in> AA x0 x1)"
    by moura
  then have f1: "\<forall>a A. a \<notin> setflat\<cdot>A \<or> AA A a \<in> A \<and> a \<in> AA A a"
  by (meson setflat_obtain)
  then have "inv_into (uspec_set_filter In Out\<cdot>H) (Rep_cfun uspecSet) (AA (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>H) f) \<in> uspec_set_filter In Out\<cdot>H"
    by (simp add: f3 inv_into_into)
  then have "inv_into (uspec_set_filter In Out\<cdot>H) (Rep_cfun uspecSet) (AA (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>H) f) \<in> Set.filter (\<lambda>u. uspecDom\<cdot>u = In \<and> uspecRan\<cdot>u = Out) H"
    by (metis (no_types) uspec_filter_insert uspec_set_filter_def)
  then have "inv_into (uspec_set_filter In Out\<cdot>H) (Rep_cfun uspecSet) (AA (Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>H) f) \<in> H"
    by (meson member_filter)
  then show ?thesis
    using f1 by (simp add: f3 f_inv_into_f that)
qed
qed

lemma uspecflatten_ele2:  "\<And> Z. Z \<in> H \<Longrightarrow> uspecDom\<cdot>Z = In \<Longrightarrow>
  uspecRan\<cdot>Z = Out \<Longrightarrow> \<forall>f.  f \<in> uspecSet\<cdot>Z \<longrightarrow> f \<in> uspecSet\<cdot>(uspecFlatten In Out\<cdot>H)"
proof -
  fix Z ::"'a uspec"
  assume a1: "Z \<in> H" and a2: "uspecDom\<cdot>Z = In"
and a3: "uspecRan\<cdot>Z = Out"
  have f1: "Z \<in> (uspec_set_filter In Out\<cdot>H)"
    by (simp add: a1 a2 a3 uspec_filter_insert uspec_set_filter_def)
  show "\<forall>f.  f \<in> uspecSet\<cdot>Z \<longrightarrow> f \<in> uspecSet\<cdot>(uspecFlatten In Out\<cdot>H)"
  proof (auto)
    fix f:: 'a 
    assume b1: "f \<in> uspecSet\<cdot>Z"         
    have b2: "f \<in> uspecSet\<cdot>(Abs_uspec
           (({uu. \<exists>Z. uu \<in> Z \<and> Z \<in> (Rep_cfun uspecSet ` Set.filter (\<lambda>uspec. uspecDom\<cdot>uspec = In \<and> uspecRan\<cdot>uspec = Out) H)}),
            Discr In, Discr Out))"
       apply (subst uspec_abs_set)
       apply force
       using a1 a2 a3 b1 image_eqI mem_Collect_eq by auto
    have b3: "f \<in> uspecSet\<cdot>
         (Abs_uspec (setflat\<cdot>(Rep_cfun uspecSet ` uspec_set_filter In Out\<cdot>H), Discr In, Discr Out))"
      apply (simp add: uspec_set_filter_def)
      apply (subst uspec_filter_insert)
      apply (simp add: setflat_insert)
      using b2 by blast
    show "f \<in> uspecSet\<cdot>(uspecFlatten In Out\<cdot>H)"
      apply (simp add: uspecflatten_insert)
      by (simp add: b3)
  qed
qed

lemma uspecflatten_not_max: assumes "SET \<noteq> Rev {}" 
and "\<And>set. set \<in> inv Rev SET \<Longrightarrow>  (uspecDom\<cdot>set) = In \<and>  (uspecRan\<cdot>set) = Out"
and "\<And>set. set \<in> inv Rev SET \<Longrightarrow>   set \<noteq> uspecMax In Out"
shows "uspecFlatten In Out SET \<noteq> uspecMax In Out"
proof -
  obtain da_set where da_set_def: "da_set \<in> inv Rev SET"
    by (metis all_not_in_conv assms(1) rev_inv_rev)
  have set_dom_ran: "(uspecDom\<cdot>da_set) = In \<and>  (uspecRan\<cdot>da_set) = Out"
    using assms(2) da_set_def by auto
  have da_set_in_filter: "da_set \<in> inv Rev (uspec_set_filter In Out\<cdot>SET)"
    by (simp add: da_set_def set_dom_ran setrevfilter_reversed uspec_set_filter_def)
  have da_set_not_empty: "da_set \<noteq> uspecMax In Out"
    by (simp add: assms(3) da_set_def)
  show ?thesis
    apply (simp add: uspecFlatten_def)
    by (metis (mono_tags, lifting) da_set_def da_set_not_empty empty_iff fstI inv_rev_rev set_dom_ran uspecFlatten_def uspecMax.rep_eq uspec_consist_f_ex uspecflatten_ele2 uspecmax_consistent uspecrevset_insert)
qed

subsection \<open>Forall Exists\<close>

lemma uspec_for_all_ex:
  assumes "uspecForall P S"
  assumes "uspecExists (\<lambda>x. True) S"
  shows "uspecExists P S"
  by (meson assms(1) assms(2) uspecExists_def uspecForall_def)

lemma uspec_subsetforall: 
  assumes "uspecForall P S"
  and "uspecSet\<cdot>T \<subseteq> uspecSet\<cdot>S"
shows "uspecForall P T"
  by (meson assms(1) assms(2) subsetCE uspecForall_def)

lemma uspec_ballI: "(\<And>x. x \<in> uspecSet\<cdot>S \<Longrightarrow> P x) \<Longrightarrow> uspecForall P S"
  using uspecForall_def by blast

lemma uspec_bexCI: "uspecForall (\<lambda>x. \<not> P x \<longrightarrow> P a) S \<Longrightarrow> a \<in> uspecSet\<cdot>S \<Longrightarrow> uspecExists P S"
  apply (simp add: uspecExists_def uspecForall_def)
  by auto

lemma uspec_bex_triv_one_point1: "uspecExists (\<lambda>x. x = a) S \<longleftrightarrow> a \<in> uspecSet\<cdot>S"
  by (simp add: uspecExists_def)

lemma uspec_bex_triv_one_point2: "uspecExists (\<lambda>x. a = x) S \<longleftrightarrow> a \<in> uspecSet\<cdot>S"
  by (simp add:  uspecExists_def)

lemma uspec_bex_one_point1: "uspecExists (\<lambda>x. x = a \<and> P x) S \<longleftrightarrow> a \<in> uspecSet\<cdot>S \<and> P a"
  by (simp add: uspecExists_def)

lemma uspec_bex_one_point2: "uspecExists (\<lambda>x. a = x \<and> P x) S \<longleftrightarrow> a \<in> uspecSet\<cdot>S \<and> P a"
  by (simp add:  uspecExists_def)

lemma uspec_ball_one_point1: "uspecForall (\<lambda>x. x = a \<longrightarrow> P x) S \<longleftrightarrow> (a \<in> uspecSet\<cdot>S \<longrightarrow> P a)"
  by (simp add: uspecForall_def uspec_ballI)

lemma uspec_ball_one_point2: "uspecForall (\<lambda>x. a = x \<longrightarrow> P x) S \<longleftrightarrow> (a \<in> uspecSet\<cdot>S \<longrightarrow> P a)"
  by (simp add: uspecForall_def uspec_ballI)

lemma uspec_subset_eq: "uspecSet\<cdot>A \<subseteq> uspecSet\<cdot>B 
  \<longleftrightarrow> uspecForall (\<lambda>x. x \<in> uspecSet\<cdot>B) A"
  by (simp add: uspecForall_def subset_eq)

lemma uspec_allDom2: "uspecForall (\<lambda>X. ufclDom\<cdot>X = uspecDom\<cdot>S) S"
  by (simp add: uspec_allDom uspec_ballI)

lemma uspec_Ran2: "uspecForall (\<lambda>X. ufclRan\<cdot>X = uspecRan\<cdot>S) S"
  by (simp add: uspec_allRan uspec_ballI)

lemma uspec_union_forall: 
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
    shows "uspecForall P (uspecUnion\<cdot>A\<cdot>B) \<longleftrightarrow> (uspecForall P A \<and> uspecForall P B)"
  apply (simp add: uspecForall_def uspecUnion_def uspecSet_def)
  apply (simp add: uspecUnion_general_def)
  using assms uspecset_insert
  by (smt Collect_cong Set.filter_def Un_iff fstI rep_abs_uspec sup_Un_eq sup_set_def uspecUnion_general_well)

lemma uspec_union_exists:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
    shows "uspecExists P (uspecUnion\<cdot>A\<cdot>B) \<longleftrightarrow> uspecExists P A \<or> uspecExists P B"
  apply (simp add: uspecExists_def uspecUnion_def)
  apply (simp add: uspecUnion_general_def)
  apply (subst uspec_abs_set)
  using uspecUnion_general_well apply blast
  using Un_iff assms(1) assms(2) by auto

lemma uspec_union_notfit_notex:
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "\<And>a. \<not>(uspecExists (\<lambda>x. x = a) (uspecUnion\<cdot>A\<cdot>B))"
  by (meson assms uspecExists_def uspecUnion_set_condition)

lemma uspec_union_l1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecExists (\<lambda>x. x = a) A \<or> uspecExists (\<lambda>x. x = a) B"
    shows "uspecExists (\<lambda>x. x = a) (uspecUnion\<cdot>A\<cdot>B)"
  using assms apply (simp add: uspecExists_def uspecUnion_def)
  apply (subst uspecUnion_general_easy)
  apply auto[1]
  apply auto[1]
  by (metis Un_iff fstI rep_abs_uspec sup.idem ucpecunion_fit_filtered uspecUnion_general_well uspecset_insert)

lemma uspec_inter_forall_help1: 
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecForall P A \<and> uspecForall P B"
    shows "uspecForall P (uspecInter\<cdot>A\<cdot>B)"
  apply (rule uspecinter_rule1)
  apply (simp add: assms(1))
  apply (simp add: assms(2))
  apply (simp add: uspecForall_def uspecSet_def)
  by (metis (no_types) IntD2 assms(3) uspecForall_def uspecset_insert)

lemma uspec_inter_forall_help2: 
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
    shows "uspecForall P (uspecInter\<cdot>A\<cdot>B)"
  by (metis assms empty_iff uspecForall_def uspec_inter_notfit)

lemma uspec_inter_forall: 
  assumes "uspecForall P A \<and> uspecForall P B"
    shows "uspecForall P (uspecInter\<cdot>A\<cdot>B)"
  using assms uspec_inter_forall_help1 uspec_inter_forall_help2 by blast

lemma uspec_inter_exists: 
  assumes "uspecExists P (uspecInter\<cdot>A\<cdot>B)"
  shows "uspecExists P A \<and> uspecExists P B"
  by (meson assms uspecExists_def uspecinter_incl1 uspecinter_incl2)

lemma uspec_inter_notfit_notex:
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
  shows "\<And>a. \<not>(uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B))"
  using uspec_inter_notfit
  by (metis assms empty_iff uspecExists_def)

lemma uspec_inter_l1_help1:
  assumes "uspecDom\<cdot>A = uspecDom\<cdot>B"
      and "uspecRan\<cdot>A = uspecRan\<cdot>B"
      and "uspecExists (\<lambda>x. x = a) A \<and> uspecExists (\<lambda>x. x = a) B"
    shows "uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B)"
  apply (rule uspecinter_rule1)
  apply (simp add: assms(1))
  apply (simp add: assms(2))
  apply (simp add: uspecSet_def)
  apply (simp add: uspecExists_def)
  apply (subst uspec_abs_set)
  apply (simp add: uspecset_insert)
  by (metis (mono_tags, lifting) Int_iff assms(3) uspecExists_def uspecset_insert)

lemma uspec_inter_l1_help2:
  assumes "uspecDom\<cdot>A \<noteq> uspecDom\<cdot>B \<or> uspecRan\<cdot>A \<noteq> uspecRan\<cdot>B"
      and "uspecExists (\<lambda>x. x = a) A \<and> uspecExists (\<lambda>x. x = a) B"
    shows "uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B)"
  apply (simp add: uspecExists_def)
  apply (subst uspec_inter_notfit)
  using assms(1) apply blast
  by (metis (mono_tags, lifting) assms(1) assms(2) uspecExists_def uspec_allDom uspec_allRan)

lemma uspec_inter_l1:
  assumes "uspecExists (\<lambda>x. x = a) A \<and> uspecExists (\<lambda>x. x = a) B"
  shows "uspecExists (\<lambda>x. x = a) (uspecInter\<cdot>A\<cdot>B)"
  by (metis assms uspec_inter_l1_help1 uspec_inter_l1_help2)

lemma uspec_filter_forall:
  "uspecForall P (uspecFilter P\<cdot>A)"
  apply (simp add: uspecfilter_insert uspecForall_def)
  apply (simp add: uspecFilter_general_def)
  apply (subst uspec_abs_set)
  apply (metis uspecFilter_general_well)
  by simp


section \<open>instance div_pcpo\<close>

(*
lemma uspec_ub: "S\<noteq>{} \<Longrightarrow>S \<subseteq> USPEC In Out \<Longrightarrow> S <| x \<Longrightarrow> x\<in>USPEC In Out"
  unfolding USPEC_def
  unfolding is_ub_def
  by (metis (mono_tags, lifting) bot.extremum_uniqueI contra_subsetD mem_Collect_eq subset_emptyI uspecdom_eq uspecran_eq)

lemma uspec_cpo: assumes  "S \<subseteq> USPEC In Out" and "S\<noteq>{}"
  shows "\<exists>x\<in>USPEC In Out. S <<| x"
proof -
  let ?A = "(Rep_rev_uspec ` S)"
  let ?lub = "(Rev (\<Inter>?A), Discr In, Discr Out)"
  have "\<And>a. a\<in>(\<Inter>?A) \<Longrightarrow> ufclDom\<cdot>a = In"
    by (metis (mono_tags) INT_E assms(1) assms(2) contra_subsetD ex_in_conv uspec_allDom uspec_dom uspecrevset_insert)
  moreover have "\<And>a. a\<in>(\<Inter>?A) \<Longrightarrow> ufclRan\<cdot>a = Out"
    using assms(1) assms(2) rep_rev_revset uspec_allRan by fastforce
  ultimately have "uspecWell (Rev (\<Inter>?A)) (Discr In) (Discr Out)" by(simp)
  hence lub_rep_abs: "Rep_uspec (Abs_uspec ?lub) = ?lub"
    using rep_abs_uspec by blast
  have "\<And>s. s\<in>S \<Longrightarrow> s\<sqsubseteq>(Abs_uspec ?lub)"
    apply(rule uspec_belowI)
    apply(simp_all add: uspecdom_insert uspecran_insert lub_rep_abs uspecrevset_insert)
    using assms uspec_dom uspecdom_insert apply fastforce
    using assms uspec_ran uspecran_insert apply fastforce
    by (metis INF_lower inv_rev_rev revBelowNeqSubset)
  hence "S <| Abs_uspec ?lub"
    using is_ubI by blast
  moreover have "\<And>u. S <| u \<Longrightarrow> (Abs_uspec ?lub) \<sqsubseteq> u"
    apply(rule uspec_belowI)
    apply(simp_all add: uspecdom_insert uspecran_insert lub_rep_abs uspecrevset_insert)
    apply (metis assms(1) assms(2) uspec_dom uspec_ub uspecdom_insert)
    apply (metis (full_types) assms(1) assms(2) uspec_ran uspec_ub uspecran_insert)
    by (metis (no_types, lifting) INF_greatest fst_monofun inv_rev_rev is_ubD rep_uspec_belowI revBelowNeqSubset)
  ultimately show ?thesis
    using assms is_lubI uspec_ub by blast
qed


lemma uspec_chain_field: assumes "longChain S"
  and "a\<in>S" and "b\<in>S"
shows "uspecDom\<cdot>a = uspecDom\<cdot>b" and "uspecRan\<cdot>a = uspecRan\<cdot>b"
  apply (metis assms(1) assms(2) assms(3) longChain_def uspecdom_eq)
  by (metis (no_types) assms(1) assms(2) assms(3) longChain_def uspecran_eq)

lemma uspec_chain_field2: assumes "longChain S" 
  shows "\<exists>In Out. S \<subseteq> USPEC In Out"
  apply(cases "S={}")
  apply simp
proof (rule ccontr)
  assume "S\<noteq>{}" and "\<nexists>(In::channel set) Out::channel set. S \<subseteq> USPEC In Out"
  from this obtain a b where "a\<in>S" and "b\<in>S" and "uspecDom\<cdot>a\<noteq>uspecDom\<cdot>b \<or> uspecRan\<cdot>a\<noteq>uspecRan\<cdot>b"
    by (smt USPEC_def assms mem_Collect_eq order_refl subsetI subset_emptyI uspec_chain_field(1) uspec_chain_field(2))
  thus False
    by (meson assms(1) uspec_chain_field(1) uspec_chain_field(2)) 
qed

lemma uspec_cpo2: fixes S :: "'m::ufuncl uspec set"
  assumes "longChain S"
  shows "\<exists>x. S <<| x"
  by (metis assms empty_iff finite.simps lc_finite_lub uspec_chain_field2 uspec_cpo)

instantiation uspec:: (ufuncl) div_pcpo
begin
definition DIV_uspec_def: "DIV_uspec \<equiv> { USPEC In Out | In Out . True  }"
instance
  apply(intro_classes)
  apply(auto simp add: DIV_uspec_def)
  apply (simp add: uspec_exists)
  apply (simp add: infinite_imp_nonempty uspec_cpo)
  by (metis (mono_tags, lifting) USPEC_def mem_Collect_eq uspecleast_dom uspecleast_least uspecleast_ran)
end

*)


subsection \<open>Size\<close>

lemma uspec_size_empty: 
  assumes "\<not> uspecIsConsistent X"
  shows "uspecSize X = Fin 0"
  using assms
  apply (simp add: uspecIsConsistent_def uspecSize_def)
  by (simp add: setSizeEmpty)

lemma uspec_size_singleton: 
  assumes "uspecSet\<cdot>X = {x}"
  shows "uspecSize X = lnsuc\<cdot>(Fin 0)"
  using assms
  by (simp add: setSizeSingleton uspecSize_def)

lemma uspec_size_union: 
  assumes "uspecDom\<cdot>X = uspecDom\<cdot>Y"
      and "uspecRan\<cdot>X = uspecRan\<cdot>Y"
    shows "uspecSize (uspecUnion\<cdot>X\<cdot>Y) + uspecSize (uspecInter\<cdot>X\<cdot>Y) = uspecSize X + uspecSize Y"
  apply (simp add: uspecUnion_def uspecInter_def uspecSize_def)
  apply (simp add: uspecUnion_general_def uspecInter_general_def)
  apply (subst ucpecunion_fit_filtered)
  apply (simp add: assms)
  apply (simp add: assms)
  apply (subst uspec_abs_set)
  apply (metis assms(1) assms(2) ucpecunion_fit_filtered uspecUnion_general_well)
  apply (subst uspec_abs_set)
  using uspecInter_general_well apply blast
  using setsize_union by auto

lemma uspec_size_union_disjoint: 
  assumes "uspecDom\<cdot>X = uspecDom\<cdot>Y"
      and "uspecRan\<cdot>X = uspecRan\<cdot>Y"
      and "uspecSet\<cdot>(uspecInter\<cdot>X\<cdot>Y) = {}"
    shows "uspecSize (uspecUnion\<cdot>X\<cdot>Y) = uspecSize X + uspecSize Y"
proof -
  have b0: "Fin 0 = uspecSize (uspecInter\<cdot>X\<cdot>Y)"
    by (simp add: assms setSizeEmpty uspecSize_def)
  have b1: "uspecSize (uspecUnion\<cdot>X\<cdot>Y) + Fin 0 = uspecSize X + uspecSize Y"
    apply (subst b0)
    using assms(1) assms(2) uspec_size_union by blast
  show ?thesis
    using b1 by auto
qed

lemma uspec_size_mono_union: 
  assumes "uspecDom\<cdot>X = uspecDom\<cdot>Y"
      and "uspecRan\<cdot>X = uspecRan\<cdot>Y"
    shows "uspecSize X \<le> uspecSize (uspecUnion\<cdot>X\<cdot>Y)"
  apply (simp add: uspecUnion_def uspecSize_def)
  apply (simp add: uspecUnion_general_def)
  apply (subst ucpecunion_fit_filtered)
  apply (simp add: assms)
  apply (simp add: assms)
  apply (subst uspec_abs_set)
  apply (metis assms(1) assms(2) ucpecunion_fit_filtered uspecUnion_general_well)
  by (simp add: setsize_mono_union)

lemma uspec_size_mono: 
  assumes "F \<sqsubseteq> G"
  shows "uspecSize F \<le> uspecSize G"
  apply (simp add: uspecSize_def)
  by (metis SetPcpo.less_set_def assms monofun_cfun_arg setsize_mono)

lift_definition uspecConst:: "'f::ufuncl_comp \<Rightarrow> 'f uspec" is
"\<lambda> f. ({f}, Discr (ufclDom\<cdot>f), Discr (ufclRan\<cdot>f))"
  by auto

lemma uspecconst_dom [simp]: "uspecDom\<cdot>(uspecConst f ) = (ufclDom\<cdot>f)"
  apply (simp add: uspecConst_def)
  by (simp add: uspecdom_insert)

lemma uspecconst_ran [simp]: "uspecRan\<cdot>(uspecConst f ) = (ufclRan\<cdot>f)"
  apply (simp add: uspecConst_def)
  by (simp add: uspecran_insert)

lemma uspecconst_consistent [simp]: "uspecIsConsistent (uspecConst f)"
  by (simp add: uspecConst.rep_eq uspecIsConsistent_def uspecset_insert)

lemma uspecconst_set [simp]: "uspecSet\<cdot>(uspecConst f) = {f}"
  by (simp add: uspecConst.rep_eq uspecset_insert)

end
