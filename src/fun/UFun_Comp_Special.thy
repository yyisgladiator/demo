theory UFun_Comp_Special
  imports UFun UFun_Comp
begin

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

subsubsection \<open>ufParcomp_Sercomp\<close>
(* ufcomp ufparcomp_sercomp  *)

lemma parcomp_sercomp_dom_f12: assumes "parcomp_sercomp_well f1 f2"
  shows "ufDom\<cdot>f1 \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) = {}"
  using assms by blast

lemma parcomp_sercomp_dom_f1: assumes "parcomp_sercomp_well f1 f2"
                      and "ubclDom\<cdot>ub = ufCompI f1 f2"
                    shows "ubclDom\<cdot>(f1\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>f1)\<cdot>ub)) = ufRan\<cdot>f1"
  apply (subst ufran_2_ubcldom2)
  apply (simp add: ubclrestrict_ubcldom assms(2) ufCompI_def)
  using assms(1) apply blast
  by simp

lemma parcomp_sercomp_f1_ufdom_subseteq:
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ufDom\<cdot>f1 \<subseteq> ubclDom\<cdot>x"
  apply (simp add: assms(2) ufCompI_def)
  using assms parcomp_sercomp_dom_f12 by blast

lemma parcomp_sercomp_f2_ufdom_subseteq:
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ufDom\<cdot>f2 \<subseteq> ubclDom\<cdot>x \<union> (ufRan\<cdot>f1)"
  apply (simp add: assms(2) ufCompI_def)
  using assms(1) by blast

lemma parcomp_sercomp_f1_ubcldom_eq:
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>(f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) = ufRan\<cdot>f1"
  apply (rule ufun_ubclrestrict_ubcldom)
  using parcomp_sercomp_f1_ufdom_subseteq assms by blast

lemma parcomp_sercomp_f2_ubcldom_eq:
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>(f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1)))) = ufRan\<cdot>f2"
  apply (rule ufun_ubclrestrict_ubcldom)
  apply (simp add: ubclunion_dom ubcldom_least_cs)
  using parcomp_sercomp_f2_ufdom_subseteq assms by blast

lemma parcomp_sercomp_f1_ubcldom_union_eq:
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1))))) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
  apply (simp add: ubclunion_ubcldom)
  using assms parcomp_sercomp_f1_ubcldom_eq parcomp_sercomp_f2_ubcldom_eq
  by (metis (no_types, hide_lams))

lemma parcomp_sercomp_ubleast_f1_f2_l: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) = (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)"
  by (metis parcomp_sercomp_dom_f12 assms(1) inf_commute ubcldom_least_cs ubclunion_restrict_R)

lemma parcomp_sercomp_f1_f2_l: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  and "ubclDom\<cdot>y = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
  shows "(ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> y)) = (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)"
  by (metis parcomp_sercomp_dom_f12 assms(1) assms(3) inf_commute ubclunion_restrict_R)

lemma parcomp_sercomp_ubleast_f1_f2_r: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) = (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ubclLeast (ufRan\<cdot>f1)))"
  by (smt Int_Un_distrib2 assms(1) inf.strict_order_iff inf_commute sup_bot.right_neutral ubclrestrict_ubclleast_inter ubclunion_ubclrestrict)

lemma parcomp_sercomp_f1_f2_r: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  and "ubclDom\<cdot>y = ufRan\<cdot>f2"
  and "ubclDom\<cdot>z = ufRan\<cdot>f1"
  shows "(ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (z \<uplus> y))) = (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> z))"
  by (metis (no_types, hide_lams) assms(1) assms(3) inf_commute ubclunion_restrict_R ubclunion_ubclrestrict)

lemma parcomp_sercomp_iter_serial_zero: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ufCompH f1 f2 (Suc (Suc (Suc 0))) x) = 
         (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"
  apply (simp add: ufcomph_insert)
  using parcomp_sercomp_f1_ubcldom_union_eq parcomp_sercomp_f2_ubcldom_eq parcomp_sercomp_f1_ubcldom_eq parcomp_sercomp_f1_f2_l parcomp_sercomp_f1_f2_r
  by (smt assms(1) assms(2) parcomp_sercomp_f2_ufdom_subseteq parcomp_sercomp_ubleast_f1_f2_l parcomp_sercomp_ubleast_f1_f2_r ubclunion_ubcldom ufRanRestrict)

lemma parcomp_sercomp_iter_serial_i_h: 
  assumes "parcomp_sercomp_well f1 f2"
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
      using parcomp_sercomp_f1_ufdom_subseteq assms(1) assms(2) apply blast
      apply (subst ufun_ubclrestrict_ubcldom, simp_all)
      apply (simp add: ubclunion_ubcldom)
      by (metis (mono_tags, lifting) parcomp_sercomp_f2_ufdom_subseteq assms(1) assms(2) iter_ufCompH_dom le_supI1 sup_assoc)
    have ubcldom_r: "ubclDom\<cdot>(f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> 
                  ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x))) \<uplus>
                  (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x))))))) =
                  ufRan\<cdot>f2"
      apply (subst ufun_ubclrestrict_ubcldom, simp_all)
      apply (simp add: ubclunion_ubcldom)
      by (metis (no_types, lifting) parcomp_sercomp_f2_ufdom_subseteq assms(1) assms(2) le_supI1 sup_assoc ubcldom_l ubclunion_ubcldom)
    show ?thesis   
      using ufcomph_insert parcomp_sercomp_f1_f2_l ubcldom_l ubcldom_r 
      by (smt parcomp_sercomp_f1_ufdom_subseteq assms(1) assms(2) inf.absorb_iff2 inf.right_idem inf_commute inf_sup_aci(2) iterate_Suc ubclunion_restrict3 ubrestrict_dom2 ufran_2_ubcldom2)
  qed

lemma parcomp_sercomp_iter_serial_i: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ufCompH f1 f2 (Suc (Suc (Suc i))) x) = 
         (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"
  by (smt Int_Un_distrib Un_empty_right parcomp_sercomp_f1_f2_l parcomp_sercomp_f1_ubcldom_eq parcomp_sercomp_iter_serial_i_h assms(1) assms(2) 
      distrib_imp1 inf.absorb_iff2 inf.commute iter_ufCompH_dom iterate_Suc sup.absorb_iff2 ubclrestrict_dom_id ubclrestrict_twice 
      ubclunion_ubclrestrict ufcomph_insert)

lemma parcomp_sercomp_iter_max_in_chain: 
  assumes "parcomp_sercomp_well f1 f2"
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
      by (metis assms(1) assms(2) parcomp_sercomp_iter_serial_i)
  qed

lemma ufcomp_parcomp_sercomp_lub_const1: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = iter_ufCompH f1 f2 (Suc (Suc (Suc 0))) x"  
  using assms(1) assms(2) iter_ufCompH_chain maxinch_is_thelub parcomp_sercomp_iter_max_in_chain by blast

lemma ufcomp_parcomp_sercomp_lub_const2: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"
  by (metis assms(1) assms(2) parcomp_sercomp_iter_serial_i ufcomp_parcomp_sercomp_lub_const1)

lemma ufcomp_parcomp_sercomp_iterconst_eq: 
  assumes "parcomp_sercomp_well f1 f2"
  shows "(\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> (\<Squnion>i. iter_ufCompH f1 f2 i x))
        = (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))))"
  proof -
    have  "\<forall>x. (ubclDom\<cdot>x \<noteq> ufCompI f1 f2)  \<or> 
          (Some ((\<Squnion>i. iter_ufCompH f1 f2 i x))
          = Some ((f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))))"
        by (metis assms ufcomp_parcomp_sercomp_lub_const2)
    then show ?thesis
      by auto
  qed

lemma ufcomp_parcomp_sercomp_apply: 
  assumes "parcomp_sercomp_well f1 f2"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(f1\<otimes>f2) \<rightleftharpoons> x = (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>x)))))"  
  apply (subst ufcomp_repabs)
  using assms apply blast
  apply (simp add: assms(2))
  apply (simp add: ubFix_def)
  apply (subst ufcomp_parcomp_sercomp_lub_const2)
  using assms(1) apply blast
  using assms(2) apply blast
  by simp



subsection\<open>More General Comp lemma\<close>

subsubsection\<open>Apply Lemma for ufComp\<close>

lemma ufComp_sercomp_well_apply:
  assumes "sercomp_well f1 f2"
      and "(ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
      and "ubclDom\<cdot>x = ufCompI f1 f2"
    shows "(ufComp f1 f2) \<rightleftharpoons> x = (f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
  by (smt assms(1) assms(2) assms(3) comp_well_def ubclrestrict_dom_id ubclunion_commu ubclunion_restrict_R ubclunion_ubclrestrict_RI ufSerComp_dom ufcomp_I_inter_Oc_empty ufcomp_dom ufcomp_fix ufcomp_fix_f1 ufcomp_ran ufcomp_serial_eq ufhide_dom ufran_2_ubcldom2)



end