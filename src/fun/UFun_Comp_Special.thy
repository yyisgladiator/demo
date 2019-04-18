theory UFun_Comp_Special
  imports UFun_Comp
begin

default_sort ubcl_comp  

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   

subsection\<open>definitions\<close>  

abbreviation parcomp_well :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> bool" where
"parcomp_well f1 f2 \<equiv> (ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"


definition ufParComp :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> ('in,'out) ufun" (infixl "\<parallel>" 50) where
"ufParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))))"


abbreviation sercomp_well :: "('in,'m) ufun \<Rightarrow> ('m,'out) ufun \<Rightarrow> bool" where
"sercomp_well f1 f2 \<equiv>  (ufRan\<cdot>f1 = ufDom\<cdot>f2) 
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                        \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})"

definition ufSerComp :: "('in,'m) ufun \<Rightarrow> ('m,'out) ufun \<Rightarrow> ('in,'out) ufun" (infixl "\<circ>" 50) where
"ufSerComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"

abbreviation serparcomp_well :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> bool" where
"serparcomp_well f1 f2 \<equiv>  (ufRan\<cdot>f1 \<inter> ufDom\<cdot>f2 \<noteq> {}) 
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                        \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})\<and>ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}\<and>ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"


definition ufSerParComp :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun" (infixl "\<circ>\<parallel>" 50) where
"ufSerParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x =  ufCompI f1 f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 ))))"

definition ufFeedH:: "('m,'m) ufun \<Rightarrow> 'm \<Rightarrow> 'm  \<rightarrow> 'm" where
"ufFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"

definition ufFeedbackComp :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun" where
"ufFeedbackComp f \<equiv>
let I  = ufDom\<cdot>f - ufRan\<cdot>f;
    C  = ufRan\<cdot>f
in Abs_ufun (Abs_cfun (\<lambda> sb. (ubclDom\<cdot>sb = I) \<leadsto>
    (ubFix (ufFeedH f sb) C)))"  

abbreviation sercomp_in_well :: "('in,'m) ufun \<Rightarrow> ('m,'out) ufun \<Rightarrow> bool" where
"sercomp_in_well f1 f2 \<equiv>  (ufRan\<cdot>f1 \<subseteq> ufDom\<cdot>f2) 
                                \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                                \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})
                                \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"

(*definition ufSerComp_In :: "('in,'m) ufun \<Rightarrow> ('m,'out) ufun \<Rightarrow> ('in,'out) ufun" (infixl "\<circ>\<^sub>i\<^sub>n" 50) where
"ufSerComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"*)


(* parcomp *)
subsection\<open>Parallel Composition\<close>


lemma parcomp_well_h1: assumes "parcomp_well f1 f2"
  shows "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {}" and "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {}"
  apply (metis (no_types, hide_lams) Int_Un_distrib2 assms bot_eq_sup_iff inf_sup_aci(1) ufCompL_def)
  using assms ufCompL_def by fastforce

lemma parcomp_well_h2: assumes "parcomp_well f1 f2"
  shows "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f1 = {}"
proof -
  have "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> ufRan\<cdot>f2 \<union> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> ufRan\<cdot>f1 = {}"
    by (metis (no_types) Int_Un_distrib assms inf_sup_aci(5) ufCompL_def)
  then show "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
    by blast
next
  show "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f1 = {}"
    by (metis (no_types, lifting) Int_Un_distrib UFun_Comp.ufran_least Un_empty assms inf_sup_distrib1 inf_sup_distrib2 sup_eq_bot_iff ufCompL_def)
qed

lemma ufParComp_cont: "cont (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) 
                                      \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))))"
proof -
  have "cont (\<lambda> s. (Rep_cfun (Rep_ufun f1))\<rightharpoonup>(s\<bar>ufDom\<cdot>f1))" 
    using cont_Rep_cfun2 cont_compose by force

  moreover have "cont (\<lambda> s. (Rep_cfun (Rep_ufun f2))\<rightharpoonup>(s\<bar>ufDom\<cdot>f2))"
    using cont_Rep_cfun2 cont_compose by force

  ultimately have "cont (\<lambda> s. ((Rep_cfun (Rep_ufun f1))\<rightharpoonup>(s\<bar>ufDom\<cdot>f1)) \<uplus> ((Rep_cfun (Rep_ufun f2))\<rightharpoonup>(s\<bar>ufDom\<cdot>f2)))"
    using cont2cont_APP cont_Rep_cfun2 cont_compose by blast

  hence "cont (\<lambda> s. (f1\<rightleftharpoons>(s \<bar> ufDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(s \<bar> ufDom\<cdot>f2)))"
    by simp

  thus ?thesis
    using ufun_contI2 by blast
   (* by(simp add: if_then_cont)*) (*alternative*)
qed

lemma ufParComp_well:  assumes "parcomp_well f1 f2"
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 )\<leadsto>((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))))"

  apply(simp add: ufWell_def)
  apply rule
  apply (rule_tac x="ufDom\<cdot>f1 \<union> ufDom\<cdot>f2" in exI)
   apply (simp add: domIff2 ufParComp_cont)

  apply(simp add: ufParComp_cont)
  apply (rule_tac x="ufRan\<cdot>f1 \<union> ufRan\<cdot>f2" in exI)
  by (smt inf_commute inf_sup_absorb option.sel option.simps(3) ran2exists sup_commute ubclrestrict_ubcldom ubclunion_ubcldom ufran_2_ubcldom2)
(*proof-
  have f1: "\<forall>b::'a. b \<in> ran ((\<lambda> (x::'a). (ubclDom\<cdot>x = UFun.ufDom\<cdot>f1 \<union> UFun.ufDom\<cdot>f2)\<leadsto>(f1 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f2))) \<longrightarrow> ubclDom\<cdot>b = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    by (smt Int_absorb1 inf.idem inf_sup_absorb inf_sup_aci(3) option.sel option.simps(3) ran2exists sup_ge2 ubclrestrict_ubcldom ubclunion_ubcldom ufran_2_ubcldom2)
......
*)

lemma ufParComp_repAbs: assumes "parcomp_well f1 f2"
  shows "Rep_cufun (ufParComp f1 f2) = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) 
                                      \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))))"
  apply(simp add: ufParComp_def, subst rep_abs_cufun)
  apply (simp add: ufParComp_cont)
  apply (simp add: assms ufParComp_well)
  by auto

lemma ufParComp_dom: assumes "parcomp_well f1 f2"
  shows "ufDom\<cdot>(ufParComp f1 f2) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2)"
  apply (subst ufDom_def, simp add:ufParComp_def)
  apply (subst rep_abs_cufun, simp add: ufParComp_cont)
  apply (simp add: assms ufParComp_well)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)

lemma ufParComp_apply: assumes "parcomp_well f1 f2" and "ubclDom\<cdot>x = ufDom\<cdot>(ufParComp f1 f2)"
  shows "(ufParComp f1 f2)\<rightleftharpoons>x = ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))"
  apply (subst ufParComp_repAbs)
  using assms(1) apply blast
  using assms(1) assms(2) ufParComp_dom by auto

lemma ufParComp_ran: assumes "parcomp_well f1 f2"
  shows "ufRan\<cdot>(ufParComp f1 f2) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
proof-
  obtain b where b_def: "b \<in> (ran (Rep_cufun (ufParComp f1 f2)))"
    using ufran_not_empty by blast

  have f2: "ufRan\<cdot>(ufParComp f1 f2) = ubclDom\<cdot>b"
    by (meson ran2exists ufran_2_ubcldom b_def)

  have f3_1: "\<And>x. ubclDom\<cdot>x = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<Longrightarrow>
                             ubclDom\<cdot>((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2)) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    by (simp add: Int_absorb1 ubclrestrict_ubcldom ubclunion_ubcldom ufran_2_ubcldom2)

  have f3: " ubclDom\<cdot>b = ( ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
    by (metis (no_types, lifting) assms f2 option.sel ubcldom_least_cs f3_1 ufParComp_dom ufParComp_repAbs ufran_least)

  show ?thesis
    by (simp add: f2 f3)
qed

lemma parcomp_func_h: assumes "parcomp_well f1 f2"
                   and "ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<subseteq> ubclDom\<cdot>ub"
               shows "((ufParComp f1 f2) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(ufParComp f1 f2))) = (f1 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f2)"
proof -
  have f3: "((ub\<bar>ufDom\<cdot>(ufParComp f1 f2))\<bar>ufDom\<cdot>f1) = (ub\<bar>ufDom\<cdot>f1)"
    by (simp add: assms(1) inf_sup_aci(1) ubclrestrict_twice ufParComp_dom)

  have f4: "(ub\<bar>ufDom\<cdot>(ufParComp f1 f2))\<bar>ufDom\<cdot>f2 = (ub\<bar>ufDom\<cdot>f2)"
    by (simp add: Int_absorb1 assms(1) ubclrestrict_twice ufParComp_dom)

  have f1: "ufDom\<cdot>(ufParComp f1 f2) = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
    by (simp add: assms(1) ufParComp_dom)
  have f2: "ubclDom\<cdot>(ub\<bar>ufDom\<cdot>(ufParComp f1 f2)) = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
    by (metis Int_absorb1 assms(2) f1 ubclrestrict_ubcldom)

  have f5: "(Rep_cufun (ufParComp f1 f2)) = ((\<lambda>t. (ubclDom\<cdot>t = ufDom\<cdot>f1 \<union> ufDom\<cdot> f2)\<leadsto>((f1 \<rightleftharpoons> t \<bar> ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> t \<bar> ufDom\<cdot>f2))))"
    by (simp add: assms(1) ufParComp_repAbs)

  then have "Rep_cufun (ufParComp f1 f2) (ub \<bar> ufDom\<cdot>(ufParComp f1 f2)) = 
    Some ((f1 \<rightleftharpoons> (ub \<bar> ufDom\<cdot>(ufParComp f1 f2)) \<bar> ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (ub \<bar> ufDom\<cdot>(ufParComp f1 f2)) \<bar> ufDom\<cdot>f2))"
    by (simp add: f2)

  then show ?thesis
    by (metis f3 f4 option.sel)
qed

lemma parcomp_func_h2: assumes "parcomp_well f1 f2"
                   and "ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 = ubclDom\<cdot>ub"
               shows "((ufParComp f1 f2) \<rightleftharpoons> ub) = (f1 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f2)"
  by (metis assms(1) assms(2) inf_idem inf_le2 parcomp_func_h ubclrestrict_dom_id ufParComp_dom)  

lemma ufParCompWell_associativity: assumes "parcomp_well f1 f2"
                                   and "parcomp_well f2 f3"
                                   and "parcomp_well f1 f3"                                  
                                 shows "parcomp_well f1 (ufParComp f2 f3)"
   apply (simp add: ufCompL_def)
   apply (simp_all add: ufParComp_dom ufParComp_ran assms)
  apply (simp_all add: Int_Un_distrib2 Int_Un_distrib)
  by (meson assms(1) assms(2) assms(3) parcomp_well_h1(1) parcomp_well_h1(2) parcomp_well_h2(1) parcomp_well_h2(2))

lemma ufParComp_asso: assumes "parcomp_well f1 f2"
                                   and "parcomp_well f2 f3"
                                   and "parcomp_well f1 f3"                                  
                                 shows "(ufParComp (ufParComp f1 f2) f3) = (ufParComp f1 (ufParComp f2 f3))"
proof-
  have f1: "\<forall>ub. (ubclDom\<cdot>ub \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<or>
            (((ufParComp f1 f2) \<rightleftharpoons> (ub \<bar>ufDom\<cdot>(ufParComp f1 f2))) \<uplus> (f3 \<rightleftharpoons> (ub\<bar>ufDom\<cdot>f3)))
          = ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f3)))"
    by (simp add: assms(1) parcomp_func_h)

  have f2: "\<forall>ub. (ubclDom\<cdot>ub \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<or>
            ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> ((ufParComp f2 f3) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(ufParComp f2 f3))))
          = ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f3)))"
    using ubclunion_asso
    by (smt assms(1) assms(2) assms(3) le_sup_iff parcomp_func_h sup_ge1 sup_ge2 ubrestrict_dom2 ufran_2_ubcldom2)

  have f3: "\<forall>ub. (ubclDom\<cdot>ub \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<or>
            (((ufParComp f1 f2) \<rightleftharpoons> (ub \<bar>ufDom\<cdot>(ufParComp f1 f2))) \<uplus> (f3 \<rightleftharpoons> (ub\<bar>ufDom\<cdot>f3))) 
          = ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> ((ufParComp f2 f3) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(ufParComp f2 f3))))"
    using f1 f2 by auto

  have f4: "(\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(ufParComp f1 f2) \<union> ufDom\<cdot>f3) \<leadsto> (((ufParComp f1 f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(ufParComp f1 f2))) \<uplus> (f3 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f3))))
          = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>(ufParComp f2 f3)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((ufParComp f2 f3) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufParComp f2 f3)))))"
    by (metis (no_types, hide_lams) Un_assoc assms(1) assms(2) f3 ufParComp_dom)

  then have f5:"Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(ufParComp f1 f2) \<union> ufDom\<cdot>f3) \<leadsto> (((ufParComp f1 f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(ufParComp f1 f2))) \<uplus> (f3 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f3))))
              = Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>(ufParComp f2 f3)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((ufParComp f2 f3) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufParComp f2 f3)))))"
    by auto

  then show ?thesis
    by (metis(no_types) ufParComp_def)
qed

lemma ufParComp_commutativity: assumes "parcomp_well f1 f2"
                                 shows "ufParComp f1 f2 = ufParComp f2 f1"
proof-
  have finp: "ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 = ufDom\<cdot>f2 \<union> ufDom\<cdot>f1"
    by (simp add: sup_commute)

  have test: "\<forall>x . ubclDom\<cdot>x \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<or>
                                  (ubclDom\<cdot>(f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1))) \<inter> (ubclDom\<cdot>(f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))) = {}"
    apply (rule, simp)
    by (metis assms finp inf_commute inf_sup_absorb ubclrestrict_ubcldom ufran_2_ubcldom2)

  show ?thesis
    apply (simp add: ufParComp_def)
    by (metis (no_types, hide_lams) sup_commute test ubclunion_commu)
qed

(********* benoetigt??? *********)
lemma parcomp_dom_ran_empty: assumes "ufCompL f1 f2 = {}"
  shows "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) = {}"
    using assms ufCompL_def by fastforce

lemma parcomp_dom_i_below: assumes "ufCompL f1 f2 = {}"
  shows "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) = ufCompI f1 f2"
  using assms ufCompI_def ufCompL_def by fastforce

lemma parcomp_cInOc: assumes "ufCompL f1 f2 = {}"
                    and "c \<in> ufRan\<cdot>f1"
                  shows "c \<in> ufCompO f1 f2"
  by (simp add: assms(2) ufCompO_def)

lemma parcomp_domranf1: assumes "ufCompL f1 f2 = {}"
                        and "ubclDom\<cdot>ub = ufCompI f1 f2"
                      shows "(ubclDom\<cdot>(f1\<rightleftharpoons>(ub\<bar>ufDom\<cdot>f1))) = ufRan\<cdot>f1"
  by (metis assms(1) assms(2) inf_commute inf_sup_absorb parcomp_dom_i_below ubclrestrict_ubcldom ufran_2_ubcldom2)

lemma ufhide_parcompwell: assumes "parcomp_well f1 f2"
  shows "parcomp_well (f1 \<h> cs) (f2 \<h> cs)"
  apply(simp add: ufCompL_def ufhide_dom ufhide_ran)
  by (metis (no_types) Int_Diff Un_Diff assms empty_Diff inf_commute ufCompL_def)


(* sercomp *)
subsection\<open>Serial Composition\<close>
 
lemma ufSerComp_cont: "cont (\<lambda> x. (ubclDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
proof - 
  have "cont (\<lambda>x. (f1 \<rightleftharpoons> x))"
    by (metis cont_Rep_cfun2 cont_compose op_the_cont)
  moreover have "cont (\<lambda>x. (f2 \<rightleftharpoons> x))"
    by (metis cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately have "cont (\<lambda>x. (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
    using cont_compose by blast
  thus ?thesis
    by (simp add: if_then_cont)
qed

lemma ufSerComp_well: assumes "ufRan\<cdot>f1 = ufDom\<cdot>f2" shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  apply(simp add: ufWell_def)
  apply rule
   apply (rule_tac x="ufDom\<cdot>f1" in exI)
   apply rule
  apply (simp add: domIff ufSerComp_cont)
proof -
  have f1: "\<forall>b::'c. b \<in> ran (\<lambda>x::'a. (ubclDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)) \<longrightarrow> ubclDom\<cdot>b = ufRan\<cdot>f2"
    by (smt CollectD assms option.distinct(1) option.sel ran_def ufran_2_ubcldom2)
  show "\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun (\<Lambda> (x::'a). (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))) \<longrightarrow> (ubclDom\<cdot>b = Out)"
    apply(simp add: ufSerComp_cont)
    by (simp add: f1)
qed

lemma ufSerComp_dom: assumes "sercomp_well f1 f2"
  shows "ufDom\<cdot>(ufSerComp f1 f2) = ufDom\<cdot>f1"
  apply(subst ufDom_def, simp add: ufSerComp_def)
  apply(subst rep_abs_cufun, simp add: ufSerComp_cont)
   apply (simp add: assms ufSerComp_well)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)

lemma ufSerComp_repAbs: assumes "sercomp_well f1 f2"
  shows "Rep_cufun (ufSerComp f1 f2) = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  apply(simp add: ufSerComp_def, subst rep_abs_cufun)
    apply (simp add: ufSerComp_cont)
   apply (simp add: assms ufSerComp_well)
  by auto 

lemma ufSerComp_apply: assumes "sercomp_well f1 f2" and "ubclDom\<cdot>x = ufDom\<cdot>(ufSerComp f1 f2)"
  shows "(ufSerComp f1 f2)\<rightleftharpoons>x = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
  apply (subst ufSerComp_repAbs)
  using assms(1) apply blast
  using assms(1) assms(2) ufSerComp_dom by auto

lemma ufSerComp_ran: assumes "sercomp_well f1 f2"
  shows "ufRan\<cdot>(ufSerComp f1 f2) = ufRan\<cdot>f2"
  apply (simp add: ufran_least)
  apply (subst ufSerComp_apply)
  using assms apply blast
   apply (simp add: ubcldom_least_cs)
  by (metis UFun_Comp.ufran_least assms ufSerComp_dom ufran_2_ubcldom2)
    
(*
lemma ufSerCompWell_asso: assumes "sercomp_well f1 f2" and "sercomp_well f2 f3" 
  shows "sercomp_well f1 (ufSerComp f2 f3) \<and> sercomp_well (ufSerComp f1 f2) f3"
  sorry
*)

lemma ufSerComp_asso: assumes "sercomp_well f1 f2" and "sercomp_well f2 f3"
  shows "(ufSerComp f1 (ufSerComp f2 f3)) = (ufSerComp (ufSerComp f1 f2) f3)"
proof -  
  have f25: "\<forall> sb. (ubclDom\<cdot>sb \<noteq> ufDom\<cdot>f1) \<or> (f3 \<rightleftharpoons> ((ufSerComp f1 f2) \<rightleftharpoons> sb)) = ((ufSerComp f2 f3) \<rightleftharpoons> (f1 \<rightleftharpoons> sb))"
  proof -
    have f1: "ufDom\<cdot>(ufSerComp f1 f2) = ufDom\<cdot>f1"
      by (metis (no_types) assms(1) ufSerComp_dom)
    have f2: "\<forall>a u. ubclDom\<cdot>(a::'a) \<noteq> ufDom\<cdot>u \<or> ubclDom\<cdot>(u \<rightleftharpoons> a) = ufRan\<cdot>u"
      by (meson ufran_2_ubcldom2)
    have "ufDom\<cdot>(ufSerComp f2 f3) = ufRan\<cdot>f1"
      by (metis (full_types) assms(1) assms(2) ufSerComp_dom)
    then show ?thesis
      using f2 f1 by (metis (no_types) assms(1) assms(2) ufSerComp_apply)
  qed
  then have f29: "(\<lambda>x. (ubclDom\<cdot>x =  ufDom\<cdot>(ufSerComp f1 f2))\<leadsto>f3 \<rightleftharpoons> ((ufSerComp f1 f2) \<rightleftharpoons> x))
              =  (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(ufSerComp f2 f3) \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    by (metis (no_types, hide_lams) assms(1) assms(2) ufSerComp_dom)
  then have f30: "Abs_cufun (\<lambda>x. (ubclDom\<cdot>x =  ufDom\<cdot>(ufSerComp f1 f2))\<leadsto>f3 \<rightleftharpoons> ((ufSerComp f1 f2) \<rightleftharpoons> x))
              =  Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(ufSerComp f2 f3) \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    by simp
  then show ?thesis
      by (metis (no_types) f30 ufSerComp_def)
  qed

(*
proof -
  have f1: "sercomp_well f1 (ufSerComp f2 f3)" and f2: "sercomp_well (ufSerComp f1 f2) f3"
    by (metis assms(1) assms(2) assms(3) ufSerComp_dom ufSerComp_ran) +
  have f3: "ufDom\<cdot>(f1\<circ>(f2\<circ>f3)) = ufDom\<cdot>((ufSerComp f1 f2)\<circ>f3)"
    by (metis assms(1) f1 f2 ufSerComp_dom)
  have f4: "ufDom\<cdot>(f1\<circ>(f2\<circ>f3)) = ufDom\<cdot>f1"
    using f1 ufSerComp_dom by auto
  have f5: "\<And> x. ubclDom\<cdot>x \<noteq> ufDom\<cdot>f1 \<or> (f1\<circ>(f2\<circ>f3)) \<rightleftharpoons> x = f3 \<rightleftharpoons> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    by (metis assms(2) f1 f4 ufSerComp_apply ufran_2_ubcldom2)
  show ?thesis
    apply (rule ufun_eqI)
     apply (metis assms(1) f1 f2 ufSerComp_dom)
    by (metis assms(1) f1 f2 f5 ufSerComp_apply ufSerComp_dom)
qed
*)

lemma sercomp_well_ufsercomp_ufsercomp: 
  assumes "sercomp_well f1 f2"
      and "ufRan\<cdot>f2 = ufDom\<cdot>f3"
      and "ufDom\<cdot>(f1 \<circ> f2) \<inter> ufRan\<cdot>(f1 \<circ> f2) = {}" 
      and "ufDom\<cdot>f3 \<inter> ufRan\<cdot>f3 = {}"
    shows "sercomp_well (ufSerComp f1 f2) f3"
  apply rule
  apply (subst ufSerComp_ran)
  using assms(1) apply blast
  apply (simp add: assms(2))
  by (simp add: assms(3) assms(4))

lemma sercomp_well_ufsercomp_ufsercomp2: 
  assumes "sercomp_well f2 f3"
      and "ufRan\<cdot>f1 = ufDom\<cdot>(ufSerComp f2 f3)"
      and "ufDom\<cdot>(f2 \<circ> f3) \<inter> ufRan\<cdot>(f2 \<circ> f3) = {}" 
      and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {}"
    shows "sercomp_well f1 (ufSerComp f2 f3)"
  apply rule
  apply (subst ufSerComp_dom)
  using assms(1) apply blast
  apply (simp add: assms(2))
  apply (subst ufSerComp_dom)
  using assms(1) apply blast
  apply simp
  by (simp add: assms(3) assms(4))

lemma sercomp_well_asso: 
  assumes "sercomp_well f1 f2"
      and "sercomp_well f2 f3"
      and "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f3 = {}"
    shows "sercomp_well f1 (ufSerComp f2 f3)"
  apply rule
  apply (subst ufSerComp_dom)
  using assms(2) apply blast
  apply (simp add: assms(1))
  apply (subst ufSerComp_dom)
  using assms(2) apply blast
  apply (subst ufSerComp_ran)
  using assms(2) apply blast
  apply rule
  using assms(1) apply blast
  by (simp add: assms(3))


subsection \<open>Serial Parallel Composition\<close>   


lemma ufSerParComp_cont: "cont (\<lambda> x. (ubclDom\<cdot>x =  ufCompI f1 f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 )))"
proof-
  have a1:" cont (\<lambda>x. (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))"
    using cont_compose by force
  have a2:" cont (\<lambda>x. (x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1))))"
    by (simp add: a1)
  have a3:"cont (\<lambda>x. (f2 \<rightleftharpoons> x))"
    by (metis cont_Rep_cfun2 cont_compose op_the_cont)
  have a4:"cont(\<lambda>x.(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1))))) "
    using a2 a3 cont_compose by blast
  have a5:"cont (\<lambda>a. Rep_cufun f2 (a \<uplus> (f1 \<rightleftharpoons> a\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))"
    by (simp add: a2)
  have a6:"cont(\<lambda>x.(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 ))"
    using a5 cont_compose op_the_cont by blast
  have a7:"cont(\<lambda>x. ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 )))"
    by (simp add: a1 a6)
  thus ?thesis
    by simp
qed

lemma ufSerParComp_well: assumes "ufRan\<cdot>f1 \<inter> ufDom\<cdot>f2 \<noteq> {}" and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {}" and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"and  "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufWell (\<Lambda> x  . (ubclDom\<cdot>x =  ufCompI f1 f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 )))" 
  apply(simp add: ufWell_def)
  apply rule
  apply (rule_tac x="ufCompI f1 f2" in exI)
  apply rule
  apply (simp add: domIff ufSerParComp_cont)
proof -
  have b1:"ufDom\<cdot>f1 \<subseteq> ufCompI f1 f2"
    by (smt Int_Un_distrib Int_assoc Int_empty_right Un_Diff_Int assms(2) assms(3) inf.absorb_iff2 inf_commute inf_sup_absorb sup_inf_absorb ufCompI_def)
  have b2:"ufDom\<cdot>f2 - ufRan\<cdot>f1 \<subseteq> ufCompI f1 f2"
    using Int_Diff assms(4) ufCompI_def by fastforce
  have a1:"\<forall>b. b \<in> ran (\<lambda> x::'a. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)) \<longrightarrow>ubclDom\<cdot>b = ufRan\<cdot>f1 "
    by (smt b1 option.discI option.sel ran2exists ufRanRestrict)
  have a2:"\<forall>b. b \<in> ran (\<lambda> x::'a. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 )) \<longrightarrow>ubclDom\<cdot>b = ufRan\<cdot>f2"
    by (smt Diff_subset_conv Un_commute b1 b2 option.discI option.sel ran2exists ubclunion_ubcldom ufun_ubclrestrict_ubcldom ufran_2_ubcldom2)
  have a3:" \<forall>b. b \<in> ran (\<lambda> x::'a. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 )))\<longrightarrow>ubclDom\<cdot>b= ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 "
    using a1 a2 ubclunion_ubcldom assms
    by (smt Diff_subset_conv Un_commute b1 b2 inf.absorb_iff2 option.discI option.sel ran2exists ubclrestrict_ubcldom ufran_2_ubcldom2)
  show "\<exists>Out. \<forall>b. b \<in> ran (Rep_cfun (\<Lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))) \<longrightarrow>
              ubclDom\<cdot>b = Out "
    apply(simp add: ufSerParComp_cont)
    by (simp add: a3)
qed

lemma ufSerParComp_dom: assumes " serparcomp_well f1 f2"
  shows "ufDom\<cdot>(ufSerParComp f1 f2) = ufCompI f1 f2"
  apply(subst ufDom_def, simp add: ufSerParComp_def)
  apply(subst rep_abs_cufun, simp add: ufSerParComp_cont)
  apply (simp add: assms ufSerParComp_well)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)

lemma ufSerParComp_repAbs: assumes "serparcomp_well f1 f2"
  shows "Rep_cufun (ufSerParComp f1 f2) = (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 )))"
  apply(simp add: ufSerParComp_def, subst rep_abs_cufun)
  apply (simp add: ufSerParComp_cont)
  apply (simp add: assms ufSerParComp_well)
  by auto

lemma ufSerParComp_apply: assumes "serparcomp_well f1 f2" and "ubclDom\<cdot>x = ufDom\<cdot>(ufSerParComp f1 f2)"
  shows "(ufSerParComp f1 f2)\<rightleftharpoons>x = ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 ))"
  apply (subst ufSerParComp_repAbs)
  using assms(1) apply blast
  using assms(1) assms(2) ufSerParComp_dom by auto

lemma ufSerParComp_ran: assumes "serparcomp_well f1 f2"
  shows "ufRan\<cdot>(ufSerParComp f1 f2) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
  apply (simp add: ufran_least)
  apply (subst ufSerParComp_apply)
  using assms apply blast
  apply (simp add: ubcldom_least_cs)
proof-
  have b1:"ufDom\<cdot>f1 \<subseteq> ufCompI f1 f2"
    by (smt Diff_Un Int_Diff Un_Diff_Int assms inf.absorb_iff2 inf_commute inf_sup_absorb sup_bot.right_neutral ufCompI_def)
  have b2:" ufDom\<cdot>(f1 \<circ>\<parallel> f2) = ufCompI f1 f2"
    using assms ufSerParComp_dom by blast
  have b3:"ufDom\<cdot>f2 - ufRan\<cdot>f1 \<subseteq> ufCompI f1 f2"
    by (smt Diff_subset_conv Un_Diff_Int Un_Diff_cancel2 Un_commute assms le_supI1 sup_bot.right_neutral sup_ge2 sup_left_commute ufCompI_def)
  have a1:" ubclDom\<cdot>(f1 \<rightleftharpoons> ubclLeast (ufDom\<cdot>(f1 \<circ>\<parallel> f2))\<bar>ufDom\<cdot>f1) = ubclDom\<cdot>(f1 \<rightleftharpoons> ubclLeast (ufDom\<cdot>f1)) "
    by (simp add: UFun_Comp.ufran_least b1 b2 ubcldom_least_cs)
  have a2:" ubclDom\<cdot>(f2 \<rightleftharpoons> ubclLeast (ufDom\<cdot>(f1 \<circ>\<parallel> f2)) \<uplus> (f1 \<rightleftharpoons> ubclLeast (ufDom\<cdot>(f1 \<circ>\<parallel> f2))\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2) = ubclDom\<cdot>(f2 \<rightleftharpoons> ubclLeast (ufDom\<cdot>f2)) "
    by (metis Int_lower1 UFun_Comp.ufran_least Un_Diff_Int Un_mono a1 b2 b3 inf_commute ubcldom_least_cs ubclunion_ubcldom ufRanRestrict)
  show "ubclDom\<cdot>((f1 \<rightleftharpoons> ubclLeast (ufDom\<cdot>(f1 \<circ>\<parallel> f2))\<bar>ufDom\<cdot>f1) \<uplus>(f2 \<rightleftharpoons> ubclLeast (ufDom\<cdot>(f1 \<circ>\<parallel> f2)) \<uplus> (f1 \<rightleftharpoons> ubclLeast (ufDom\<cdot>(f1 \<circ>\<parallel> f2))\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2)) =ubclDom\<cdot>(f1 \<rightleftharpoons> ubclLeast (ufDom\<cdot>f1)) \<union> ubclDom\<cdot>(f2 \<rightleftharpoons> ubclLeast (ufDom\<cdot>f2)) "
    using a1 a2 ubclunion_ubcldom by blast
qed


subsection \<open>Serial Restricted Composition\<close>    
(*coming soon*)

subsection \<open>Feedback\<close>    

lemma ufFeedH_cont2: "cont (\<lambda>x. (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f)))))"
  apply(subst cont2cont_LAM)
    apply (simp_all add: ufFeedH_cont1)
  using cont_compose by force

lemma ufFeedH_cont: "cont (ufFeedH f)"
proof - 
  have f1: "ufFeedH f = (\<lambda>x. (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f)))))"
    using ufFeedH_def by auto
  have f2: "cont (\<lambda>x. (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f)))))"
    by(simp add: ufFeedH_cont2)
  show ?thesis
    apply(subst f1)
    by(simp add: f2)
qed

(* (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f)))) *)
lemma ufFeedH_insert: "(ufFeedH f tb)\<cdot>x = (f\<rightleftharpoons>((tb \<uplus> x)\<bar> (ufDom\<cdot>f)))"
  by (simp add: ufFeedH_cont1 ufFeedH_def)

lemma ufFeedH_dom [simp]: assumes "ubclDom\<cdot>x = ufDom\<cdot>f - ufRan\<cdot>f" 
                           and "ubclDom\<cdot>sb = ufRan\<cdot>f"
shows "ubclDom\<cdot>((ufFeedH f x)\<cdot>sb) = (ufRan\<cdot>f)"
  apply(simp add: ufFeedH_def ufFeedH_cont1)
  by (simp add: Int_commute assms(1) assms(2) ubclrestrict_dom ubclunion_dom ufran_2_ubcldom2)

lemma ufFeedbackComp_cont: "cont (\<lambda> sb. (ubclDom\<cdot>sb = (ufDom\<cdot>f - ufRan\<cdot>f)) \<leadsto> (ubFix (ufFeedH f sb) (ufRan\<cdot>f)))"
  apply(rule ubfix_contI2)
   apply (simp add: ufFeedH_cont)
   apply (simp add: ubcldom_least_cs)
    by simp
    
lemma ufFeedbackComp_well: "ufWell (\<Lambda> sb. (ubclDom\<cdot>sb = (ufDom\<cdot>f - ufRan\<cdot>f)) \<leadsto> (ubFix (ufFeedH f sb) (ufRan\<cdot>f)))"
  apply (rule ufun_wellI)
    apply (simp_all add: ufFeedbackComp_cont domIff2)
  apply (rule ubfix_dom)
  by (simp add: ubcldom_least_cs)

lemma ufFeedbackComp_dom: "ufDom\<cdot>(ufFeedbackComp f) = ufDom\<cdot>f - ufRan\<cdot>f"
  apply(subst ufDom_def , simp add:ufFeedbackComp_def)
  apply(subst rep_abs_cufun, simp add: ufFeedbackComp_cont)
   apply(simp add: ufFeedbackComp_well)
  by (simp add: domIff2 ubclDom_h)

lemma ufFeedbackComp_ran: "ufRan\<cdot>(ufFeedbackComp f) = ufRan\<cdot>f"
  apply (simp add: ufran_least)
  apply (simp add: ufFeedbackComp_dom)
  apply (simp add: ufFeedbackComp_def ufFeedbackComp_cont ufFeedbackComp_well)
  by (simp add: UFun_Comp.ufran_least ubcldom_least_cs ubfix_dom)

subsection \<open>Equality\<close>

subsubsection \<open>ufSerComp\<close>
(* ufcomp ufsercomp  *)

lemma sercomp_dom_f1: assumes "sercomp_well f1 f2"
                      and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                      and "ubclDom\<cdot>tb = ufCompI f1 f2"
                    shows "ubclDom\<cdot>(f1\<rightleftharpoons>(tb\<bar>(ufDom\<cdot>f1))) = ufRan\<cdot>f1"
proof -
  have "ufDom\<cdot>f1 = ufCompI f1 f2"
  proof -
    have "ufDom\<cdot>f1 = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
      using assms(1) assms(2) by blast
    then show ?thesis
      using ufCompI_def by blast
  qed
  then show ?thesis
    by (simp add: assms(3) ubclrestrict_ubcldom ufran_2_ubcldom2)
qed

lemma sercomp_dom_f12: assumes "sercomp_well f1 f2"
                       and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  shows "ufDom\<cdot>f1 \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) = {}"
  using assms by blast

lemma sercomp_iter_serial_res_f1: assumes "sercomp_well f1 f2"
                                  and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                                  and "ubclDom\<cdot>x = ufCompI f1 f2"
                                shows "(iter_ufCompH f1 f2 (Suc (Suc i)) x) \<bar> (ufRan\<cdot>f1) = (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1))"
  by (smt assms(1) assms(2) assms(3) inf_sup_absorb inf_sup_aci(1) iter_ufCompH_dom iterate_Suc 
          sercomp_dom_f1 sercomp_dom_f12 ubclrestrict_twice ubclunion_restrict_R ubclunion_restrict2 
          ubclunion_restrict3 ufran_2_ubcldom2 ufcomph_insert ubclrestrict_dom)

lemma sercomp_iter_serial: assumes "sercomp_well f1 f2"
                              and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                              and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ufCompH f1 f2 (Suc (Suc (Suc i))) x) = 
    (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))"
proof -
  have "ubclDom\<cdot>(f1 \<rightleftharpoons> ubclLeast (UFun.ufDom\<cdot>f1)) \<inter> UFun.ufDom\<cdot>f1 = UFun.ufDom\<cdot>f1 \<inter> UFun.ufRan\<cdot>f1"
    by (simp add: inf_commute ufran_least)
then have f1: "ubclDom\<cdot>(f1 \<rightleftharpoons> ubclLeast (UFun.ufDom\<cdot>f1)) \<inter> UFun.ufDom\<cdot>f1 = {}"
by (metis assms(1))
  have f2: "ubclDom\<cdot>(f2 \<rightleftharpoons> ubclLeast (UFun.ufDom\<cdot>f2)) \<inter> UFun.ufDom\<cdot>f2 = UFun.ufDom\<cdot>f2 \<inter> UFun.ufRan\<cdot>f2"
    by (simp add: inf_commute ufran_least)
  have "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc i))) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x\<bar>UFun.ufRan\<cdot>f1 = f1 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f1"
    using assms(1) assms(2) assms(3) sercomp_iter_serial_res_f1 by blast
  then show ?thesis
    by (smt assms(1) assms(2) assms(3) inf_sup_aci(1) iter_ufCompH_dom iterate_Suc sercomp_dom_f1 sercomp_dom_f12 sercomp_iter_serial_res_f1 ubclrestrict_twice
          ubclrestrict_dom ubclunion_restrict2 ubclunion_restrict_R ufcomph_insert)
qed

lemma sercomp_iter_max_in_chain: assumes "sercomp_well f1 f2"
                                 and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                                 and "ubclDom\<cdot>x = ufCompI f1 f2"
                               shows "max_in_chain (Suc (Suc (Suc 0))) (\<lambda>i. iter_ufCompH f1 f2 i x)"
proof (rule max_in_chainI)
  fix j
  assume a1: "Suc (Suc (Suc 0)) \<le> j"
  have f1: "ufDom\<cdot>f1 \<inter> ufDom\<cdot>f2 = {}"
    using assms(1) by blast
  obtain k where o1: "j = Suc (Suc (Suc k))"
    by (metis (no_types) Suc_leD Suc_n_not_le_n a1 not0_implies_Suc)  
  show "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc 0))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x =
     iter_ubfix2 (ufCompH f1 f2) j (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x"
    apply (subst o1)
    by (metis assms(1) assms(2) assms(3) sercomp_iter_serial)
  qed

lemma ufcomp_sercomp_lub_const1: assumes "sercomp_well f1 f2"
                                   and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                                   and "ubclDom\<cdot>x = ufCompI f1 f2"
                                 shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = iter_ufCompH f1 f2 (Suc (Suc (Suc 0))) x"  
  using assms(1) assms(2) assms(3) iter_ufCompH_chain maxinch_is_thelub sercomp_iter_max_in_chain by blast

lemma ufcomp_sercomp_lub_const2: assumes "sercomp_well f1 f2"
                                   and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                                   and "ubclDom\<cdot>x = ufCompI f1 f2"
                                 shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))"
  by (metis assms(1) assms(2) assms(3) sercomp_iter_serial ufcomp_sercomp_lub_const1)

lemma ufcomp_serial_iterconst_eq: assumes "sercomp_well f1 f2"
                                  and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  shows "(\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> (\<Squnion>i. iter_ufCompH f1 f2 i x) )
        = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))))"
proof -
  have f1: " ufCompI f1 f2 = ufDom\<cdot>f1"
    using assms ufCompI_def by blast
  have  "\<forall>x. (ubclDom\<cdot>x \<noteq> ufCompI f1 f2)  \<or> 
        (Some ((\<Squnion>i. iter_ufCompH f1 f2 i x))
        = Some ((f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))))"
      by (metis assms ufcomp_sercomp_lub_const2)
    then show ?thesis
      using f1 by auto
qed

lemma uf_eq: assumes "\<And>b. Rep_cufun f1 b = Rep_cufun f2 b"
  shows "f1 = f2"
  using assms
  using Rep_ufun_inject cfun_eqI by blast

lemma ufcomp_serial_eq_h1: "cont (\<lambda>x::'a. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))"
  proof -
    have "cont (\<lambda>x. (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))"
      using cont_compose by force
    moreover have "cont (\<lambda>x. (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)))"
      by (metis cont_Rep_cfun2 cont_compose op_the_cont)
    ultimately have "cont (\<lambda>x. (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)))"
      by simp
    then show ?thesis
      using if_then_cont by blast
  qed

lemma ufcomp_serial_eq_h2:
  assumes "sercomp_well f1 f2"
      and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
    shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)))" 
  apply(simp add: ufWell_def ufcomp_serial_eq_h1)
  apply rule
  apply(rule_tac x="ufDom\<cdot>f1" in exI)
  apply (simp add: domIff2)
  apply(rule_tac x="ufRan\<cdot>f1 \<union> ufRan\<cdot>f2" in exI)
  by (smt assms(1) option.distinct(1) option.sel ran2exists ubclrestrict_dom_id ubclunion_ubcldom ufran_2_ubcldom2)

lemma ufcomp_serial_eq: assumes "sercomp_well f1 f2"
                            and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
                          shows "ufHide (ufComp f1 f2) (ufRan\<cdot>f1) = (ufSerComp f1 f2)"  
proof - 
  have f1: "cont (\<lambda>x::'a. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)))"
    by (simp add: ufcomp_serial_eq_h1)
  have f2: "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)))" 
    apply (subst ufcomp_serial_eq_h2)
    using assms by auto
  have f3: "cont (\<lambda>x::'a. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    by (simp add: ufSerComp_cont)
  have f4: "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    using assms(1) ufSerComp_well by blast
  have f5: "ufRan\<cdot>(Abs_cufun (\<lambda>x::'a. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)))) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    by (smt UFun_Comp.ufran_least assms(1) domIff f1 f2 option.sel rep_abs_cufun ubclrestrict_dom_idI ubclunion_ubcldom ufran_2_ubcldom2 ufunLeastIDom)
  show ?thesis
    apply(subst (4) uf_eq, simp_all)
    apply(simp only: ufComp_def ufSerComp_def ubFix_def)
    apply(simp add: )
    apply(subst ufcomp_serial_iterconst_eq)
    using assms(1) apply blast
    using assms(2) apply auto[1]
    apply(subst uf_eq, simp_all)
     apply(simp add: ufHide_def ufhide_cont ufhide_well f1 f2 f3 f4)
    apply(case_tac "ubclDom\<cdot>b = ufDom\<cdot>f1")
     defer
    apply (simp add: f1 f2 ufun_ufdom_abs)
    apply (simp add: f5)
    by (smt Diff_disjoint Un_Diff Un_Diff_Int Un_commute assms(1) domIff f1 f2 inf_sup_absorb inf_sup_aci(1) rep_abs_cufun ubclrestrict_dom_idI ubclunion_restrict2 ufdom_2ufundom ufran_2_ubcldom2 ufunLeastIDom)
qed

lemma ufcomp2sercomp_apply: 
  assumes "sercomp_well f1 f2"
    and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
    and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(f1 \<otimes> f2) \<rightleftharpoons> x = (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))"
  apply (subst ufcomp_repabs)
  apply (simp add: assms)
  apply (simp only: ubFix_def)
  apply (subst ufcomp_sercomp_lub_const2, simp_all add: assms)
  using assms(1) by blast

subsubsection \<open>ufParComp\<close>
(* ufcomp ufparcomp  *)

(*  *)
lemma ufComp_parallel :assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ubfix2 (ufCompH f1 f2) (Suc (Suc i)) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x)
                  =(f1\<rightleftharpoons>(x \<bar>ufDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>ufDom\<cdot>f2))" (is "?L = ?R")
proof (induction i)
  have f28: "ubclDom\<cdot>(f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2) = ufRan\<cdot>f2"
    apply (rule ufran_2_ubcldom2)
    by (metis Un_upper2 assms(1) assms(2) parcomp_dom_i_below ubrestrict_dom2)
  have f29: "ubclDom\<cdot>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) = ufRan\<cdot>f1"
    apply (rule ufran_2_ubcldom2)
    by (metis assms(1) assms(2) inf_sup_absorb inf_sup_aci(1) parcomp_dom_i_below ubclrestrict_ubcldom)
  have f30: "x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f2 = x\<bar>ufDom\<cdot>f2"
    apply (rule ubclunion_restrict_R)
    apply (simp add: ubclunion_ubcldom)
    apply (simp add: f29 f28)
    by (metis (no_types, lifting) assms(1) inf_commute inf_sup_aci(1) inf_sup_distrib1 parcomp_well_h1(2) parcomp_well_h2(2)  sup_bot_right)
  have f40: "x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f1 = x\<bar>ufDom\<cdot>f1"
    apply (rule ubclunion_restrict_R)
    apply (simp add: ubclunion_ubcldom)
    apply (simp add: f29 f28)
    by (metis (mono_tags, lifting) assms(1) inf_commute inf_sup_distrib1 parcomp_well_h1(1) parcomp_well_h2(1) sup_bot_right)
  have f20: "x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<bar>ufDom\<cdot>f1 = x\<bar>ufDom\<cdot>f1"
    apply (rule ubclunion_restrict_R)
    apply (simp add: ubcldom_least_cs)
    by (metis (no_types, lifting) assms(1) inf_commute inf_sup_aci(1) 
          inf_sup_distrib1 parcomp_well_h1(1) parcomp_well_h2(1) sup_idem)
  have f21: "x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<bar>ufDom\<cdot>f2 = x\<bar>ufDom\<cdot>f2"
    apply (rule ubclunion_restrict_R)
    apply (simp add: ubcldom_least_cs)
    by (metis (no_types, lifting) Int_commute assms(1) inf_bot_right inf_sup_distrib1 
        parcomp_well_h1(2) parcomp_well_h2(2) sup_inf_absorb)
  have f3: "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc 0)) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2)"
    apply (simp add: ufCompH_def)
    apply (simp add: f20 f21)
    by (simp add: f30 f40)
  then show "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (0::nat))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2)"
    by blast
  show "\<And>i::nat. iter_ubfix2 (ufCompH f1 f2) (Suc (Suc i)) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2) \<Longrightarrow>
              iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc i))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2)" 
  proof -
    fix i::nat
    assume a1: "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc i)) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2)"
    have f1: "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc i))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = 
        ufCompH f1 f2 x\<cdot>(iter_ubfix2 (ufCompH f1 f2) (Suc (Suc i)) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)"
      by (simp)
    show "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc i))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>ufDom\<cdot>f2)"
    apply (subst f1)
    apply (subst a1)
    apply (simp add: ufCompH_def)
    by (simp add: f30 f40)
  qed
qed

(* the third iteration returns the fixpoint  *)
lemma ufComp_parallel_max: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
shows "max_in_chain (Suc (Suc 0)) (\<lambda>i. iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
  by (metis (no_types, lifting) Suc_le_D Suc_le_lessD assms(1) assms(2) le_simps(2) max_in_chainI ufComp_parallel)

(* the lub of ubFix is the parcomp *)
lemma ufComp_parallel_itconst1: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
shows "(\<Squnion> i. iter_ubfix2 (ufCompH f1 f2) i (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x) = ((f1\<rightleftharpoons>(x \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> ufDom\<cdot>f2)))"
proof -
  have "(\<Squnion> i. iter_ubfix2 (ufCompH f1 f2) i (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x) = 
      (iter_ubfix2 (ufCompH f1 f2) (Suc (Suc 0)) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x)"
    using assms(1) assms(2) maxinch_is_thelub ufComp_parallel_max iter_ufCompH_chain by blast 
  thus ?thesis
    by (metis assms(1) assms(2) ufComp_parallel)
qed

(* eq proof between ufComp and ufParComp*)
lemma parallelOperatorEq: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  shows "ufComp f1 f2 = ufParComp f1 f2" (is "?F1 = ?F2")
proof -
  have f1: "ufCompI f1 f2 = UFun.ufDom\<cdot>f1 \<union> UFun.ufDom\<cdot>f2"
    apply (simp add: ufCompI_def)
    using assms ufCompL_def by fastforce
  have f2: "ufDom\<cdot>(ufComp f1 f2) = ufDom\<cdot>(ufParComp f1 f2)"
    by (simp add: assms f1 ufParComp_dom ufcomp_dom)  
  have "\<And> ub. ubclDom\<cdot>ub \<noteq> UFun.ufDom\<cdot>f1 \<union> UFun.ufDom\<cdot>f2 \<or> ubFix (ufCompH f1 f2 ub) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) =
    (f1 \<rightleftharpoons> ub\<bar>UFun.ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> ub\<bar>UFun.ufDom\<cdot>f2)"
    by (simp add: assms f1 ubFix_def ufComp_parallel_itconst1)
  then have "(\<lambda>x::'a. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)) =
    (\<lambda>x::'a. (ubclDom\<cdot>x = UFun.ufDom\<cdot>f1 \<union> UFun.ufDom\<cdot>f2)\<leadsto>(f1 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f2))"
    using f1 by auto
  then show ?thesis
    by (simp add: ufComp_def ufParComp_def)
qed

lemma ufcomp_parcomp_apply:
  assumes "parcomp_well f1 f2" 
  and "ubclDom\<cdot>ub = ufCompI f1 f2"
  shows "(f1 \<otimes> f2) \<rightleftharpoons> ub = ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>ub)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>ub)))"
  by (metis assms(1) assms(2) parallelOperatorEq ufParComp_apply ufcomp_dom)

subsubsection \<open>ufSerParComp\<close>
(* ufcomp ufserparcomp  *)

lemma ufcomp_serialparallel_eq: 
  assumes "serparcomp_well f1 f2"
  shows "ufComp f1 f2 = ufSerParComp f1 f2"  
proof-
  have a1:"ufDom\<cdot>(ufComp f1 f2) = ufDom\<cdot>(ufSerParComp f1 f2) "
    by (simp add: assms ufSerParComp_dom ufcomp_dom)
  have b1:"ufDom\<cdot>(ufComp f1 f2) = (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ) " 
    by (simp add: a1 assms ufCompI_def ufSerParComp_dom)
  have b2:" ufDom\<cdot>(ufSerParComp f1 f2) =(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 )"
    using a1 b1 by blast
  have b3:"(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<inter>  ufDom\<cdot>f1=  {}"
    using assms by blast
  have a2_0:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>((ufComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufComp f1 f2) =ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    by (metis a1 assms ubclrestrict_dom_id ufCompI_def ufSerParComp_dom ufcomp_insert)
  have a2_1:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>((ufSerParComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp f1 f2) = ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 ))) "
    by (metis assms ubclrestrict_dom_id ufCompI_def ufSerParComp_apply ufSerParComp_dom)
  have a2_20: "\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>((ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) = (f1 \<rightleftharpoons> ((x \<uplus> (ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))  \<bar> ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> ((x \<uplus> (ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))  \<bar> ufDom\<cdot>f2)))"
    by (smt assms ubfix_eq ufCompH_dom ufCompI_def ufCompO_def ufcomp_well_h ufcomph_insert ufcomp_fix uflift_ran_h)
  have a2_21: "\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>(ubclDom\<cdot>(ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) =  (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ) )"
    by (simp add: assms ufCompI_def ufCompO_def ufcomp_well_h)
  have a2_22:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>(((x \<uplus> (ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))\<bar> ufDom\<cdot>f1) =  x \<bar> ufDom\<cdot>f1  )"
   by (metis a2_21 b3 ubclunion_restrict_R)
  have a2_23:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>(((ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))\<bar> ufDom\<cdot>f2 = ((ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))\<bar> (ufRan\<cdot>f1  \<inter>  ufDom\<cdot>f2) )"
    by (smt a2_21 assms inf_commute inf_sup_distrib2 ubclrestrict_dom_id ubclrestrict_twice ubclrestrict_ubcldom)
  have a2_2:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>(ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) = ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 ))) "
    by (smt a2_20 assms ufCompI_def ufcomp_insert comp_well_def ufCompI_def ufcomp_fix_f1 a2_22 a2_23 ubclrestrict_twice ubclunion_ubclrestrict)
  have a2:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 ))\<or>((ufComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufComp f1 f2) =(ufSerParComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp f1 f2))"
    using a2_0 a2_1 a2_2 by auto
  have a3: "(\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(ufComp f1 f2) ) \<leadsto> ((ufComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufComp f1 f2)))= (\<lambda> x. (ubclDom\<cdot>x =ufDom\<cdot>(ufSerParComp f1 f2)) \<leadsto> ((ufSerParComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp f1 f2)))" 
    using a2 b1 b2 ubclrestrict_dom_id by auto
  then have a4: "Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(ufComp f1 f2) ) \<leadsto> ((ufComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufComp f1 f2)))= Abs_cufun (\<lambda> x. (ubclDom\<cdot>x =ufDom\<cdot>(ufSerParComp f1 f2)) \<leadsto> ((ufSerParComp f1 f2) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp f1 f2)))"
    by auto
  then show ?thesis    
    by (metis (no_types, lifting) a1 a2 assms ubclrestrict_dom_id ufCompI_def ufSerParComp_dom ufun_eqI)
qed

lemma ufcomp_serialparallel_eq: 
  assumes "serparcomp_well f1 f2"
  shows "ufComp f1 f2 = ufSerParComp f1 f2"  
  oops


subsubsection \<open>ufSercomp_in\<close>
(* ufcomp ufsercomp_in  *)

lemma sercomp_in_dom_f12: assumes "sercomp_in_well f1 f2"
  shows "ufDom\<cdot>f1 \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) = {}"
  using assms by blast

lemma sercomp_in_dom_f1: assumes "sercomp_in_well f1 f2"
                      and "ubclDom\<cdot>ub = ufCompI f1 f2"
                    shows "ubclDom\<cdot>(f1\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>f1)\<cdot>ub)) = ufRan\<cdot>f1"
  apply (subst ufran_2_ubcldom2)
  apply (simp add: ubclrestrict_ubcldom assms(2) ufCompI_def)
  using assms(1) apply blast
  by simp

lemma sercomp_in_f1_ufdom_subseteq:
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ufDom\<cdot>f1 \<subseteq> ubclDom\<cdot>x"
  apply (simp add: assms(2) ufCompI_def)
  using assms sercomp_in_dom_f12 by blast

lemma sercomp_in_f2_ufdom_subseteq:
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ufDom\<cdot>f2 \<subseteq> ubclDom\<cdot>x \<union> (ufRan\<cdot>f1)"
  apply (simp add: assms(2) ufCompI_def)
  using assms(1) by blast

lemma sercomp_in_f1_ubcldom_eq:
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>(f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) = ufRan\<cdot>f1"
  apply (rule ufun_ubclrestrict_ubcldom)
  using sercomp_in_f1_ufdom_subseteq assms by blast

lemma sercomp_in_f2_ubcldom_eq:
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>(f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1)))) = ufRan\<cdot>f2"
  apply (rule ufun_ubclrestrict_ubcldom)
  apply (simp add: ubclunion_dom ubcldom_least_cs)
  using sercomp_in_f2_ufdom_subseteq assms by blast

lemma sercomp_in_f1_ubcldom_union_eq:
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1))))) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
  apply (simp add: ubclunion_ubcldom)
  using assms sercomp_in_f1_ubcldom_eq sercomp_in_f2_ubcldom_eq
  by (metis (no_types, hide_lams))

lemma sercomp_in_ubleast_f1_f2_l: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) = (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)"
  by (metis sercomp_in_dom_f12 assms(1) inf_commute ubcldom_least_cs ubclunion_restrict_R)

lemma sercomp_in_f1_f2_l: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  and "ubclDom\<cdot>y = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
  shows "(ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> y)) = (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)"
  by (metis sercomp_in_dom_f12 assms(1) assms(3) inf_commute ubclunion_restrict_R)

lemma sercomp_in_ubleast_f1_f2_r: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) = (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1)))"
  by (smt Int_Un_distrib2 assms(1) inf.strict_order_iff inf_commute sup_bot.right_neutral ubclrestrict_ubclleast_inter ubclunion_ubclrestrict)

lemma sercomp_in_f1_f2_r: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  and "ubclDom\<cdot>y = ufRan\<cdot>f2"
  and "ubclDom\<cdot>z = ufRan\<cdot>f1"
  shows "(ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (z \<uplus> y))) = (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> z))"
  by (metis (no_types, hide_lams) assms(1) assms(3) inf_commute ubclunion_restrict_R ubclunion_ubclrestrict)

lemma sercomp_in_iter_serial_zero: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ufCompH f1 f2 (Suc (Suc (Suc 0))) x) = 
         (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"
  apply (simp add: ufcomph_insert)
  using sercomp_in_f1_ubcldom_union_eq sercomp_in_f2_ubcldom_eq sercomp_in_f1_ubcldom_eq sercomp_in_f1_f2_l sercomp_in_f1_f2_r
  by (smt assms(1) assms(2) sercomp_in_f2_ufdom_subseteq sercomp_in_ubleast_f1_f2_l sercomp_in_ubleast_f1_f2_r ubclunion_ubcldom ufRanRestrict)

lemma sercomp_in_iter_serial_i_h: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(ubclRestrict (ufRan\<cdot>f1)\<cdot>(iter_ufCompH f1 f2 (Suc (Suc i)) x)) = 
         (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x))"
  proof -
    have ubcldom_l: "ubclDom\<cdot>((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x))) \<uplus>
                  (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)))) =
          (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
      apply (simp add: ubclunion_ubcldom)
      apply (subst ufun_ubclrestrict_ubcldom)
      apply (simp add: ubclunion_ubcldom)
      using sercomp_in_f1_ufdom_subseteq assms(1) assms(2) apply blast
      apply (subst ufun_ubclrestrict_ubcldom, simp_all)
      apply (simp add: ubclunion_ubcldom)
      by (metis (mono_tags, lifting) sercomp_in_f2_ufdom_subseteq assms(1) assms(2) iter_ufCompH_dom le_supI1 sup_assoc)
    have ubcldom_r: "ubclDom\<cdot>(f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> 
                  ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x))) \<uplus>
                  (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x))))))) =
                  ufRan\<cdot>f2"
      apply (subst ufun_ubclrestrict_ubcldom, simp_all)
      apply (simp add: ubclunion_ubcldom)
      by (metis (no_types, lifting) sercomp_in_f2_ufdom_subseteq assms(1) assms(2) le_supI1 sup_assoc ubcldom_l ubclunion_ubcldom)
    show ?thesis   
      using ufcomph_insert sercomp_in_f1_f2_l ubcldom_l ubcldom_r 
      by (smt sercomp_in_f1_ufdom_subseteq assms(1) assms(2) inf.absorb_iff2 inf.right_idem inf_commute inf_sup_aci(2) iterate_Suc ubclunion_restrict3 ubrestrict_dom2 ufran_2_ubcldom2)
  qed

lemma sercomp_in_iter_serial_i: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ufCompH f1 f2 (Suc (Suc (Suc i))) x) = 
         (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"
  by (smt Int_Un_distrib Un_empty_right sercomp_in_f1_f2_l sercomp_in_f1_ubcldom_eq sercomp_in_iter_serial_i_h assms(1) assms(2) 
      distrib_imp1 inf.absorb_iff2 inf.commute iter_ufCompH_dom iterate_Suc sup.absorb_iff2 ubclrestrict_dom_id ubclrestrict_twice 
      ubclunion_ubclrestrict ufcomph_insert)

lemma sercomp_in_iter_max_in_chain: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "max_in_chain (Suc (Suc (Suc 0))) (\<lambda>i. iter_ufCompH f1 f2 i x)"
  proof (rule max_in_chainI)
    fix j
    assume a1: "Suc (Suc (Suc 0)) \<le> j"
    obtain k where o1: "j = Suc (Suc (Suc k))"
      by (metis (no_types) Suc_leD Suc_n_not_le_n a1 not0_implies_Suc)  
    show "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc 0))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x =
       iter_ubfix2 (ufCompH f1 f2) j (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x"
      apply (subst o1)
      by (metis assms(1) assms(2) sercomp_in_iter_serial_i)
  qed

lemma ufcomp_sercomp_in_lub_const1: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = iter_ufCompH f1 f2 (Suc (Suc (Suc 0))) x"  
  using assms(1) assms(2) iter_ufCompH_chain maxinch_is_thelub sercomp_in_iter_max_in_chain by blast

lemma ufcomp_sercomp_in_lub_const2: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"
  by (metis assms(1) assms(2) sercomp_in_iter_serial_i ufcomp_sercomp_in_lub_const1)

lemma ufcomp_sercomp_in_iterconst_eq: 
  assumes "sercomp_in_well f1 f2"
  shows "(\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> (\<Squnion>i. iter_ufCompH f1 f2 i x))
        = (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))))"
  proof -
    have  "\<forall>x. (ubclDom\<cdot>x \<noteq> ufCompI f1 f2)  \<or> 
          (Some ((\<Squnion>i. iter_ufCompH f1 f2 i x))
          = Some ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))))"
        by (metis assms ufcomp_sercomp_in_lub_const2)
    then show ?thesis
      by auto
  qed

lemma ufcomp_sercomp_in_apply: 
  assumes "sercomp_in_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(f1\<otimes>f2) \<rightleftharpoons> x = (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"  
  apply (subst ufcomp_repabs)
  using assms apply blast
  apply (simp add: assms(2))
  apply (simp add: ubFix_def)
  apply (subst ufcomp_sercomp_in_lub_const2)
  using assms(1) apply blast
  using assms(2) apply blast
  by simp



subsection\<open>More Special Comp lemma\<close>

subsubsection\<open>Apply Lemma for ufComp\<close>


lemma ufComp_sercomp_well_apply:
  assumes "sercomp_well f1 f2"
      and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
      and "ubclDom\<cdot>x = ufCompI f1 f2"
    shows "(ufComp f1 f2) \<rightleftharpoons> x = (f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
  by (smt assms(1) assms(2) assms(3) comp_well_def ubclrestrict_dom_id ubclunion_commu ubclunion_restrict_R ubclunion_ubclrestrict_RI ufSerComp_dom ufcomp_I_inter_Oc_empty ufcomp_dom ufcomp_fix ufcomp_fix_f1 ufcomp_ran ufcomp_serial_eq ufhide_dom ufran_2_ubcldom2)


subsubsection\<open>ufHide split\<close>


lemma ufhide_sercomp: 
  assumes "ufDom\<cdot>f2 \<subseteq> ufRan\<cdot>f1"
  and     "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  and     "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  and     "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {}"
(*and     "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {}" *)
shows "(f1 \<otimes> f2) \<h> (ufRan\<cdot>f1) = ((f1 \<h> (ufRan\<cdot>f1-ufDom\<cdot>f2)) \<otimes> f2) \<h> (ufDom\<cdot>f2)" (is "?f = ?g")
proof -
  have f2_no_feedback: "ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {}"
    using assms(1) assms(2) by blast 
  have dom_eq:"ufDom\<cdot>?f = ufDom\<cdot>?g"
    apply(simp add: Diff_triv assms ufCompI_def ufcomp_dom ufhide_dom ufhide_ran)
    apply(subst ufcomp_dom)
    apply(simp add: ufhide_ran)
    apply(simp add: Diff_Int_distrib2 assms(2))
    apply(simp add: ufCompI_def ufhide_dom ufhide_ran)
    by (smt Diff_Diff_Int Diff_Int_distrib2 Diff_Un Diff_idemp Diff_triv Un_Diff Un_Diff_Int assms(3) assms(4) f2_no_feedback inf.idem inf_bot_right)
  have f1_dom: "ufRan\<cdot>(f1 \<h> (ufRan\<cdot>f1 - ufDom\<cdot>f2)) = ufDom\<cdot>f2"
      by (simp add: Diff_Diff_Int Int_absorb1 assms(1) ufhide_ran)
  have g_sercomp_well: "sercomp_well (f1 \<h> (ufRan\<cdot>f1-ufDom\<cdot>f2)) f2"
      apply(simp add: ufhide_dom f1_dom f2_no_feedback)
      using assms(1) assms(4) by blast
  have g_ser: "?g = ((f1 \<h> (ufRan\<cdot>f1-ufDom\<cdot>f2)) \<circ> f2)"
    by (metis (no_types, lifting) assms(3) ufcomp_serial_eq ufhide_dom g_sercomp_well)
  have ran_eq:"ufRan\<cdot>(f1 \<otimes> f2) - ufRan\<cdot>f1 = ufRan\<cdot>f2"
    by (metis Diff_cancel Un_Diff Un_Diff_Int assms(2) inf_commute sup_commute ufCompO_def ufcomp_ran) 
  have out_eq:"\<And> ub. ubclDom\<cdot>ub =(ufDom\<cdot>?f) \<Longrightarrow> ?f \<rightleftharpoons> ub = ?g \<rightleftharpoons> ub"
    apply(simp add: g_ser ufhide_apply ufhide_dom ran_eq)
    apply(subst ufSerComp_apply)
    using g_sercomp_well apply blast
    apply (metis dom_eq g_ser ufhide_dom)
    apply(simp add: ufcomp_fix_f2 comp_well_def assms ufcomp_dom)
    apply(subst ufhide_apply)
    apply (metis (no_types, lifting) assms(2) dom_eq g_ser g_sercomp_well ufSerComp_dom ufcomp_dom ufhide_dom)
    apply(subst ubclunion_restrict_R)
    apply (metis (no_types, lifting) assms(2) dom_eq g_ser g_sercomp_well ufSerComp_dom ufcomp_dom ufhide_dom)
    by (smt Diff_Diff_Int assms(2) comp_well_def dom_eq g_ser g_sercomp_well ubclrestrict_twice 
        ubclunion_commu ubclunion_restrict2 ufSerComp_dom ufcomp_I_inter_Oc_empty ufcomp_dom ufcomp_fix_f1 
        ufcomp_ran ufhide_dom ufhide_ran ufran_2_ubcldom2)
  then show ?thesis
    using dom_eq ufun_eqI by blast
qed

lemma ufhide_parcomp:
  assumes "parcomp_well f1 f2"
  shows "(f1 \<otimes> f2) \<h> cs = ((f1 \<h> cs) \<otimes> (f2 \<h> cs))"
  apply(subst parallelOperatorEq)
  using assms apply blast
  apply(simp add: assms parallelOperatorEq ufhide_parcompwell)
  apply(rule ufun_eqI)
  apply(simp add: assms ufParComp_dom ufhide_dom ufhide_parcompwell)
  apply(simp add: ufhide_dom ufhide_apply)
  apply(subst ufParComp_apply)
  using assms apply blast
  apply(simp add: assms ufParComp_apply ufParComp_dom ufhide_dom ufhide_parcompwell)+
  apply (simp add: ufhide_apply ubrestrict_dom2 ubclunion_ubclrestrict)
  apply(subst ufParComp_ran)
  using assms apply blast
  apply(subst ufParComp_ran)
  using assms apply blast
  by (smt Int_Diff Un_commute Un_upper2 inf_sup_absorb ubclrestrict_dom_id ubclrestrict_twice ufRanRestrict)

subsubsection\<open>Associativity\<close>


lemma ufcomp_asso_sercomp_in: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f3 = {}" and  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f4 = {}" 
  and  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f5 = {}" and "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f3 = {}" and  "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f4 = {}" and  "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f5 = {}"
  and  "ufRan\<cdot>f3 \<inter> ufRan\<cdot>f4 = {}" and  "ufRan\<cdot>f3 \<inter> ufRan\<cdot>f5 = {}"  and  "ufRan\<cdot>f4 \<inter> ufRan\<cdot>f5 = {}" 
shows "ufComp(ufComp(ufComp (ufComp f1 f2)f3)f4)f5 = ufComp(ufComp f1 f2)(ufComp(ufComp f3 f4) f5)"
  proof-
    have f0: "ufRan\<cdot>(ufComp f1 f2) \<inter> ufRan\<cdot>f3 = {}"
      apply (simp add: assms(1) ufcomp_ran)
      unfolding ufCompO_def
      by (simp add: assms inf_sup_distrib2)
    have f1: "ufDom\<cdot>(ufComp (ufComp f1 f2) f3) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (simp add: f0 ufcomp_dom)
      unfolding ufCompI_def
      apply (simp add: ufcomp_ran ufcomp_dom assms(1))
      unfolding ufCompO_def
      apply (subst ufCompI_def)
      by blast
    have f2 :"ufRan\<cdot>(ufComp (ufComp f1 f2) f3) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3"
      by (metis assms(1) f0 ufCompO_def ufcomp_ran)
    have f3: "ufRan\<cdot>(ufComp (ufComp f1 f2) f3) \<inter> ufRan\<cdot>f4 = {}"
      by (simp add: assms(3) assms(6) assms(8) f2 inf_sup_distrib2)
    have f4 :"ufRan\<cdot>(ufComp (ufComp (ufComp f1 f2) f3) f4) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3\<union> ufRan\<cdot>f4"
      by (metis f2 f3 ufCompO_def ufcomp_ran)
    have f5:"ufRan\<cdot>(ufComp (ufComp (ufComp f1 f2) f3) f4) \<inter> ufRan\<cdot>f5 = {}"
      by (simp add: assms(10) assms(4) assms(7) assms(9) f4 inf_sup_distrib2)
    have f6: "ufDom\<cdot>(ufComp (ufComp (ufComp f1 f2) f3) f4) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 \<union> ufDom\<cdot>f4) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3\<union> ufRan\<cdot>f4)"
      apply (simp add: f3 ufcomp_dom)
      unfolding ufCompI_def
      apply(simp add:f1 ufcomp_ran ufcomp_dom assms)
      unfolding ufCompO_def
      apply (simp add:f2)
      by blast
    have f7 :"ufRan\<cdot>(ufComp  (ufComp (ufComp (ufComp f1 f2) f3) f4) f5) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3\<union> ufRan\<cdot>f4\<union> ufRan\<cdot>f5"
      by (metis f4 f5 ufCompO_def ufcomp_ran)
    have f8: "ufDom\<cdot>(ufComp(ufComp (ufComp (ufComp f1 f2) f3) f4) f5) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 \<union> ufDom\<cdot>f4 \<union> ufDom\<cdot>f5) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3\<union> ufRan\<cdot>f4\<union> ufRan\<cdot>f5)"
      apply (simp add: f5 ufcomp_dom)
     unfolding ufCompI_def
     apply(simp add:f4 f6 f7 ufcomp_ran ufcomp_dom assms)
     by blast
    have f9: "ufRan\<cdot>(ufComp f3 f4) \<inter> ufRan\<cdot>f5 = {}"
      apply (simp add: assms ufcomp_ran)
      unfolding ufCompO_def
      by (simp add: assms inf_sup_distrib2)
    have f10: "ufDom\<cdot>(ufComp (ufComp f3 f4) f5) = (ufDom\<cdot>f3 \<union> ufDom\<cdot>f4 \<union> ufDom\<cdot>f5) - (ufRan\<cdot>f3 \<union> ufRan\<cdot>f4 \<union> ufRan\<cdot>f5)"
      apply (simp add: f9 ufcomp_dom)
      unfolding ufCompI_def
      apply (simp add: ufcomp_ran ufcomp_dom assms)
      unfolding ufCompO_def
      apply (subst ufCompI_def)
      by blast
    have f11:"ufRan\<cdot>(ufComp (ufComp f3 f4) f5) = ufRan\<cdot>f3 \<union> ufRan\<cdot>f4 \<union> ufRan\<cdot>f5"
      by (metis assms(8) f9 ufCompO_def ufcomp_ran)
    have f12: "ufRan\<cdot>(ufComp f1 f2) \<inter> ufRan\<cdot>(ufComp (ufComp f3 f4) f5) = {}"
      apply (simp add: assms(1) ufcomp_ran)
      unfolding ufCompO_def
      by (smt assms(1) assms(4) assms(7) assms(8) f0 f11 f3 inf_sup_distrib1 inf_sup_distrib2 sup_bot.right_neutral ufCompO_def ufcomp_ran)
    have f13: "ufDom\<cdot>( ufComp(ufComp f1 f2) (ufComp (ufComp f3 f4) f5)) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 \<union> ufDom\<cdot>f4 \<union> ufDom\<cdot>f5) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3\<union> ufRan\<cdot>f4\<union> ufRan\<cdot>f5)"
      apply (simp add: f12 ufcomp_dom)
      unfolding ufCompI_def
      apply (simp add: ufcomp_ran ufcomp_dom assms f9 f10 f11)
      unfolding ufCompO_def
      apply (subst ufCompI_def)
      by blast
    have f14:"ufDom\<cdot>(ufComp(ufComp (ufComp (ufComp f1 f2) f3) f4) f5) =ufDom\<cdot>( ufComp(ufComp f1 f2) (ufComp (ufComp f3 f4) f5))" 
      by (simp add: f8 f13)
    show ?thesis
      by (smt Un_empty assms(1) f0 f12 f3 f9 inf_sup_distrib1 inf_sup_distrib2 ufCompO_def ufcomp_asso ufcomp_ran)
  qed

lemma ufcomp_asso_sercomp_in_apply: assumes 
  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f3 = {}" and  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f4 = {}" 
  and  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f5 = {}" and "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f3 = {}" and  "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f4 = {}" and  "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f5 = {}"
  and  "ufRan\<cdot>f3 \<inter> ufRan\<cdot>f4 = {}" and  "ufRan\<cdot>f3 \<inter> ufRan\<cdot>f5 = {}"  and  "ufRan\<cdot>f4 \<inter> ufRan\<cdot>f5 = {}" 
shows "ufComp(ufComp(ufComp (ufComp f1 f2) f3) f4) f5  \<rightleftharpoons> ub= ufComp(ufComp f1 f2)(ufComp (ufComp f3 f4) f5) \<rightleftharpoons> ub"
  by (simp add: assms ufcomp_asso_sercomp_in)

subsubsection\<open>property split\<close>


lemma sercomp_prop:
  assumes "\<And>ub. ubclDom\<cdot>ub = ufDom\<cdot>f1 \<Longrightarrow> P ub \<Longrightarrow> Q (f1 \<rightleftharpoons> ub)"
  and     "\<And>ub. ubclDom\<cdot>ub = ufDom\<cdot>f2 \<Longrightarrow> Q ub \<Longrightarrow> R (f2 \<rightleftharpoons> ub)"
  and     "sercomp_well f1 f2"
  and     "ubclDom\<cdot>ub = ufDom\<cdot>f1"
  and     "P ub"
shows     "R ((f1 \<circ> f2) \<rightleftharpoons> ub)"
  apply(subst ufSerComp_apply)
  using assms apply blast
  apply(simp add: assms)
  apply(subst ufSerComp_dom)
  using assms apply blast
  by(simp add: assms ufran_2_ubcldom2)+

lemma parcomp_prop:
  assumes "parcomp_well f1 f2"      
      and "\<And>ub. ubclDom\<cdot>ub = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<Longrightarrow> P ub \<Longrightarrow> P1 (ubclRestrict (ufDom\<cdot>f1)\<cdot>ub) \<and> P2 (ubclRestrict (ufDom\<cdot>f2)\<cdot>ub)"
      and "\<And>ub. ubclDom\<cdot>ub = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<Longrightarrow> Q1 (ubclRestrict (ufRan\<cdot>f1)\<cdot>ub) \<and> Q2 (ubclRestrict (ufRan\<cdot>f2)\<cdot>ub) \<Longrightarrow> R ub"
      and "\<And>ub. ubclDom\<cdot>ub = ufDom\<cdot>f1 \<Longrightarrow> P1 ub \<Longrightarrow> Q1 (f1 \<rightleftharpoons> ub)"
      and "\<And>ub. ubclDom\<cdot>ub = ufDom\<cdot>f2 \<Longrightarrow> P2 ub \<Longrightarrow> Q2 (f2 \<rightleftharpoons> ub)"
      and "ubclDom\<cdot>ub = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
      and "P ub"
    shows "R ((f1 \<parallel> f2) \<rightleftharpoons> ub)"
  apply(subst ufParComp_apply)
  using assms apply blast
  apply(simp add: assms)
  apply(subst ufParComp_dom)
  using assms apply blast
  apply simp
  apply(subst assms(3))
  apply(simp add: ubclunion_dom)
  apply(simp add: ufran_2_ubcldom2 ubclrestrict_dom assms Int_absorb1)
  apply(rule)
  apply(subst ubclunion_restrict_R)
  apply(simp add: ufran_2_ubcldom2 ubclrestrict_dom assms Int_absorb1 Int_commute)
  apply(simp add: assms ubclrestrict_dom_idI ubrestrict_dom2)
  by(metis Un_upper2 assms(2) assms(5) assms(6) assms(7) ubclunion_restrict2 ubrestrict_dom2 ufRanRestrict)+

lemma ufcomp_fix_l: assumes "ubclDom\<cdot>ub = ufCompI f g" and "comp_well f g"
  shows "f \<rightleftharpoons> ((((f\<otimes>g) \<rightleftharpoons> ub) \<uplus> ub)\<bar> ufDom\<cdot>f) = (((f\<otimes>g) \<rightleftharpoons> ub) \<uplus> ub)\<bar> ufRan\<cdot>f"
proof -
have f1: "ubclDom\<cdot>((f \<otimes> g) \<rightleftharpoons> ub) = ufRan\<cdot>(f \<otimes> g)"
by (metis (no_types) assms(1) assms(2) comp_well_def ufcomp_dom ufran_2_ubcldom2)
  have f2: "ufRan\<cdot>(f \<otimes> g) = ufCompO f g"
    using assms(2) comp_well_def ufcomp_ran by blast
  then have "ufRan\<cdot>f \<union> ufRan\<cdot>g = ufRan\<cdot>(f \<otimes> g)"
    by (metis ufCompO_def)
  then show ?thesis
    using f2 f1 by (metis (no_types) assms(1) assms(2) sup_ge1 ubclrestrict_twice ubclrestrict_ubcldom ubclunion_commu ubclunion_restrict2 ubrestrict_dom2 ufcomp_I_inter_Oc_empty ufcomp_fix_f1)
qed

lemma ufcomp_fix_r: assumes "ubclDom\<cdot>ub = ufCompI f g" and "comp_well f g"
  shows "g \<rightleftharpoons> ((((f\<otimes>g) \<rightleftharpoons> ub) \<uplus> ub)\<bar> ufDom\<cdot>g) = (((f\<otimes>g) \<rightleftharpoons> ub) \<uplus> ub)\<bar> ufRan\<cdot>g"
proof -
  have f1: "\<forall>a. ((a::'a)\<bar>ubclDom\<cdot> ub)\<bar>ufRan\<cdot>f \<union> ufRan\<cdot>g = a\<bar>{}"
    by (metis (full_types) assms(1) ubclrestrict_twice ufCompO_def ufcomp_I_inter_Oc_empty)
  have f2: "\<forall>C. ({}::channel set) \<inter> C = {}"
    by blast
  have "ufRan\<cdot>f \<inter> ufRan\<cdot>g = {}"
    by (meson assms(2) comp_well_def)
  then show ?thesis
    using f2 f1 by (metis (no_types) assms(1) comp_well_def ubcldom_ex ubclrestrict_twice ubclunion_restrict2 ubclunion_restrict_R ubclunion_ubclrestrict_union ufcomp_fix_f2)
qed

lemma ufcomp_fix2: 
    assumes "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
    and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(f1 \<otimes> f2) \<rightleftharpoons> x = f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x \<bar> ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x \<bar> ufDom\<cdot>f1)))"
(* Gilt nicht, aber sowas ähnliches könnte interessant sein.... damit es analog zu ser_comp wird
ser_comp wendet 2 Funktionen hintereinander an. Bitte mit GANZ allgemeinen assumptions ! ! !*)
  oops

lemma  
  assumes "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
    and "sercomp_well f1 f2"
    and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "((f1 \<otimes> f2) \<h> ufRan\<cdot>f1) \<rightleftharpoons> x =(f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar> ufDom\<cdot>f1)))"
  oops

end