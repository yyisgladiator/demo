theory SPS

imports fun.SPF USpec_Comp USpec_UFunComp

begin

default_sort message

type_synonym ('m,'n) SPS = "('m,'n) SPF uspec"

section \<open>Definition\<close>

definition uspecConstOut:: "channel set \<Rightarrow> 'n::message SB  \<Rightarrow> ('m,'n) SPF uspec" where
"uspecConstOut \<equiv> \<lambda> In sb. uspecConst (ufConst In\<cdot>sb)"

definition spsConcOut:: "'n SB \<Rightarrow> ('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsConcOut sb = (uspecImageC (spfConcOut sb))"

definition spsConcIn:: "'m SB \<Rightarrow> ('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsConcIn sb = uspecImageC (spfConcIn sb)"

definition spsRtIn:: "('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsRtIn = uspecImageC spfRtIn"

definition spsComplete :: "('m::ubcl \<Rrightarrow> 'n::ubcl) uspec \<Rightarrow> ('m::ubcl \<Rrightarrow> 'n::ubcl) uspec" where
"spsComplete sps = Abs_uspec ({spf | spf . ufDom\<cdot>spf = uspecDom\<cdot>sps \<and> ufRan\<cdot>spf = uspecRan\<cdot>sps
                                            \<and> (\<forall>sb. ubclDom\<cdot>sb = uspecDom\<cdot>sps \<longrightarrow> (\<exists>spf2\<in>(uspecSet\<cdot>sps). spf\<rightleftharpoons>sb = spf2\<rightleftharpoons>sb))},
                             (Discr (uspecDom\<cdot>sps)), (Discr (uspecRan\<cdot>sps)))"

section \<open>Lemma\<close>

(* ----------------------------------------------------------------------- *)
subsection \<open>uspecConstOut\<close>
(* ----------------------------------------------------------------------- *)
lemma uspecconstout_insert: "uspecConstOut In sb = uspecConst (ufConst In\<cdot>sb)"
  by (simp add: uspecConstOut_def)

lemma uspecconstout_dom[simp]: "uspecDom\<cdot>(uspecConstOut In sb) = In"
  apply (simp add: uspecconstout_insert)
  by (simp add: ufclDom_ufun_def uspecconst_dom)

lemma uspecconstout_ran[simp]: "uspecRan\<cdot>(uspecConstOut In sb) = ubclDom\<cdot>sb"
  apply (simp add: uspecconstout_insert)
  by (simp add: ufclRan_ufun_def uspecconst_ran)

lemma uspecconstout_set[simp]: "uspecSet\<cdot>(uspecConstOut In sb) = {ufConst In\<cdot>sb}"
  by (simp add: uspecconstout_insert)

(* ----------------------------------------------------------------------- *)
subsection \<open>spsConcOut\<close>
(* ----------------------------------------------------------------------- *)

lemma spsconcout_mono: "monofun (uspecImage (Rep_cfun (spfConcOut sb)))"
  apply (rule uspecimage_mono)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)


lemma spsconcout_dom [simp]: 
  "uspecDom\<cdot>(spsConcOut sb\<cdot>sps) = uspecDom\<cdot>sps"
  apply (simp add: spsConcOut_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def uspecimagec_insert)

lemma spsconcout_ran [simp]: 
  "uspecRan\<cdot>(spsConcOut sb\<cdot>sps) = uspecRan\<cdot>sps"
  apply (simp add: spsConcOut_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def uspecimagec_insert)

lemma spsconcout_obtain: assumes "g \<in> uspecSet\<cdot>(spsConcOut sb\<cdot>sps)"
  shows "\<exists> f. f\<in>(uspecSet\<cdot>sps) \<and> g = spfConcOut sb\<cdot>f"
  by (metis (no_types, lifting) assms image_iff spsConcOut_def uspecimagec_set)

lemma spsconcout_const[simp]: "spsConcOut sb\<cdot>(uspecConst f) = uspecConst (spfConcOut sb\<cdot>f)"
  by(simp add: spsConcOut_def)

lemma spsconcout_consistentI: assumes "uspecIsConsistent S" 
  shows "uspecIsConsistent (spsConcOut sb\<cdot>S)"
  by (simp add: assms spsConcOut_def)

lemma spsconcout_set:  "uspecSet\<cdot>(spsConcOut Out\<cdot>sps) = (Rep_cfun (spfConcOut Out)) ` (uspecSet\<cdot>sps)"
  by (simp add: spsConcOut_def uspecimagec_set)

(* ----------------------------------------------------------------------- *)
subsection \<open>spsConcIn\<close>
(* ----------------------------------------------------------------------- *)

lemma spsconcin_dom[simp]: "uspecDom\<cdot>(spsConcIn sb\<cdot>sps) = uspecDom\<cdot>sps"
  by (simp add: spfconcin_uspec_iamge_well spsConcIn_def ufuncldom_least_dom uspecimagec_dom)

lemma spsconcin_ran[simp]:  "uspecRan\<cdot>(spsConcIn sb\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: spfconcin_uspec_iamge_well spsConcIn_def ufclRan_ufun_def uspecimagec_insert)

lemma spsconcin_const[simp]: "spsConcIn sb\<cdot>(uspecConst f) = uspecConst (spfConcIn sb\<cdot>f)"
  by(simp add: spsConcIn_def)

lemma spsconcin_set:  "uspecSet\<cdot>(spsConcIn In\<cdot>sps) = (Rep_cfun (spfConcIn In)) ` (uspecSet\<cdot>sps)"
  by (simp add: spsConcIn_def uspecimagec_set)


(* ----------------------------------------------------------------------- *)
subsection \<open>spsRtIn\<close>
(* ----------------------------------------------------------------------- *)

lemma spsrtin_dom [simp]: "uspecDom\<cdot>(spsRtIn\<cdot>sps) = uspecDom\<cdot>sps"
  by (metis spfRtIn_dom spsRtIn_def ufclDom_ufun_def ufuncldom_least_dom uspecimagec_dom)

lemma spsrtin_ran [simp]: "uspecRan\<cdot>(spsRtIn\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: spsRtIn_def ufclDom_ufun_def ufclRan_ufun_def uspecimagec_insert)



subsection \<open>spsComplete\<close>

lemma spscomplete_well [simp]: "uspecWell {spf | spf . ufDom\<cdot>spf = uspecDom\<cdot>sps \<and> ufRan\<cdot>spf = uspecRan\<cdot>sps
                                            \<and> (\<forall>sb. ubclDom\<cdot>sb = uspecDom\<cdot>sps \<longrightarrow> (\<exists>spf2\<in>(uspecSet\<cdot>sps). spf\<rightleftharpoons>sb = spf2\<rightleftharpoons>sb))}
                      (Discr (uspecDom\<cdot>sps))  (Discr (uspecRan\<cdot>sps))"
  apply(simp)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spscomplete_set: "uspecSet\<cdot>(spsComplete sps) = {spf | spf . ufDom\<cdot>spf = uspecDom\<cdot>sps \<and> ufRan\<cdot>spf = uspecRan\<cdot>sps
                                            \<and> (\<forall>sb. ubclDom\<cdot>sb = uspecDom\<cdot>sps \<longrightarrow> (\<exists>spf2\<in>(uspecSet\<cdot>sps). spf\<rightleftharpoons>sb = spf2\<rightleftharpoons>sb))}"
  unfolding uspecSet_def spsComplete_def
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spscomplete_dom [simp]: "uspecDom\<cdot>(spsComplete sps) = uspecDom\<cdot>sps"
  by (smt prod.sel(1) prod.sel(2) rep_abs_uspec spsComplete_def spscomplete_well undiscr_Discr uspecdom_insert)

lemma spscomplete_ran [simp]: "uspecRan\<cdot>(spsComplete sps) = uspecRan\<cdot>sps"
  by (metis (mono_tags, lifting) Discr_undiscr prod.sel(2) rep_abs_uspec spsComplete_def spscomplete_well uspecran_insert)

lemma spscomplete_belowI: assumes "uspecDom\<cdot>S1 = uspecDom\<cdot>S2"
  and "uspecRan\<cdot>S1 = uspecRan\<cdot>S2"
  and "(\<And>spf sb. spf\<in>uspecSet\<cdot>S1 \<Longrightarrow> ubclDom\<cdot>sb = uspecDom\<cdot>S1 \<Longrightarrow> (\<exists>spf2\<in>(uspecSet\<cdot>S2). spf\<rightleftharpoons>sb = spf2\<rightleftharpoons>sb))"
shows "S1 \<sqsubseteq> spsComplete S2"
  apply(rule uspec_belowI)
  apply (simp_all add: assms)
  by (smt SetPcpo.less_set_def assms(1) assms(2) assms(3) mem_Collect_eq spscomplete_set subsetI ufclDom_ufun_def ufclRan_ufun_def uspec_allDom uspec_allRan)

lemma spscomplete_below: "sps \<sqsubseteq> (spsComplete sps)"
  apply(rule uspec_belowI)
    apply auto
  apply(simp add: spscomplete_set less_set_def)
  apply auto
  by (metis ufclDom_ufun_def uspec_allDom ufclRan_ufun_def uspec_allRan)+

lemma spscomplete_exists: assumes "spf\<in>(uspecSet\<cdot>(spsComplete sps))" and "ubclDom\<cdot>sb = uspecDom\<cdot>sps"
  shows "\<exists>spf2. spf2\<in>uspecSet\<cdot>sps \<and> spf\<rightleftharpoons>sb = spf2\<rightleftharpoons>sb"
  using assms by(auto simp add: spscomplete_set)

lemma spscomplete_complete_h: "uspecSet\<cdot>(spsComplete (spsComplete sps)) \<subseteq> uspecSet\<cdot>(spsComplete sps)"
  unfolding spscomplete_set
  by auto

lemma spscomplete_complete [simp]: "spsComplete (spsComplete sps) = spsComplete sps"
  by (simp add: SetPcpo.less_set_def below_antisym spscomplete_below spscomplete_complete_h uspec_belowI)

lemma spscomplete_mono: assumes "uspec1 \<sqsubseteq> uspec2"
  shows "spsComplete uspec1 \<sqsubseteq> spsComplete uspec2"
  apply(rule uspec_belowI)
  apply (simp add: assms uspecdom_eq)
  apply (simp add: assms uspecran_eq)
  by (smt Collect_mono_iff SetPcpo.less_set_def assms monofun_Rep_cfun2 monofun_def spscomplete_set subset_eq uspecdom_eq uspecran_eq)

lemma spscomplete_same_behaviour: assumes "ubclDom\<cdot>sb = uspecDom\<cdot>sps"
  shows "{spf \<rightleftharpoons> sb | spf. spf\<in>uspecSet\<cdot>(spsComplete sps)} = {spf \<rightleftharpoons> sb | spf. spf\<in>uspecSet\<cdot>sps}"
  apply auto
  using assms spscomplete_exists apply blast
  by (metis SetPcpo.less_set_def contra_subsetD monofun_cfun_arg spscomplete_below)

lemma assumes "uspec_compwell uspec1 uspec2"
  shows "((spsComplete uspec1) \<Otimes> (spsComplete uspec2)) \<sqsubseteq> spsComplete (uspec1 \<Otimes> uspec2)"
  apply(subgoal_tac "uspec_compwell (spsComplete uspec1) (spsComplete uspec2)")
  apply(rule spscomplete_belowI) 
     apply (simp add: assms uspec_comp_dom)
    apply (simp add: assms uspec_comp_ran)
  defer
  oops

lemma assumes "uspec_compwell uspec1 uspec2"
  shows "spsComplete (uspec1 \<Otimes> uspec2) \<sqsubseteq> ((spsComplete uspec1) \<Otimes> (spsComplete uspec2))"
  oops

end