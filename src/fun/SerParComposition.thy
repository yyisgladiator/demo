theory SerParComposition
  imports UFun_Comp

begin
  
default_sort ubcl_comp  
(*Maybe for the proof of the associativity of this operator, ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {} is required in serparcomp_well. *)
abbreviation serparcomp_well :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> bool" where
"serparcomp_well f1 f2 \<equiv>  (ufRan\<cdot>f1 \<inter> ufDom\<cdot>f2 \<noteq> {}) 
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                        \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}) 
                        \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"

definition ufSerParComp :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun" (infixl "\<circ>\<parallel>" 50) where
"ufSerParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x =  ufCompI f1 f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>ufDom\<cdot>f1))\<uplus>(f2 \<rightleftharpoons>(x\<uplus> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2 ))))"

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
    by (simp add: if_then_cont)
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

lemma serparcomp_well_ufserparcomp_ufserparcomp: 
  assumes "serparcomp_well f1 f2"
      and "(ufRan\<cdot>f1\<union>ufRan\<cdot>f2) \<inter> ufDom\<cdot>f3 \<noteq>{}"
      and "ufDom\<cdot>(f1  \<circ>\<parallel> f2) \<inter> ufRan\<cdot>(f1  \<circ>\<parallel> f2) = {}" 
      and "ufDom\<cdot>f3 \<inter> ufRan\<cdot>f3 = {}"
      and "ufDom\<cdot>(f1  \<circ>\<parallel> f2) \<inter> ufRan\<cdot>f3 ={}"
      and "ufRan\<cdot>(f1  \<circ>\<parallel> f2) \<inter> ufRan\<cdot>f3 ={}"
    shows "serparcomp_well (ufSerParComp f1 f2) f3"
  by (metis assms ufSerParComp_ran)

lemma serparcomp_well_ufserparcomp_ufserparcomp2: 
  assumes "serparcomp_well f2 f3"
      and "ufRan\<cdot>f1 \<inter> ufDom\<cdot>(ufSerParComp f2 f3) \<noteq>{}"
      and "ufDom\<cdot>(f2 \<circ>\<parallel> f3) \<inter> ufRan\<cdot>(f2 \<circ>\<parallel> f3) = {}" 
      and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {}"
      and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>(f2  \<circ>\<parallel> f3) ={}"
      and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>(f2  \<circ>\<parallel> f3) ={}"
    shows "serparcomp_well f1 (ufSerParComp f2 f3)"
  using assms by blast 

lemma serparcomp_well_asso: 
  assumes "serparcomp_well f1 f2"
      and "serparcomp_well f2 f3"
      and "ufDom\<cdot>(ufSerParComp f2 f3) \<inter> ufRan\<cdot>f1 \<noteq> {}"
      and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>(ufSerParComp f2 f3) ={}"
      and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>(ufSerParComp f2 f3) ={}"
    shows "serparcomp_well f1 (ufSerParComp f2 f3)"
  by (smt Diff_iff assms disjoint_iff_not_equal ufCompI_def ufSerParComp_dom ufSerParComp_ran) 

lemma serparcomp_well_associativity: 
  assumes "serparcomp_well f1 f2"
      and "serparcomp_well f2 f3"
      and "serparcomp_well f1 f3" 
    shows "serparcomp_well f1 (ufSerParComp f2 f3)"
proof-
  have a0:"ufDom\<cdot> (ufSerParComp f2 f3) = ufDom\<cdot>f2 \<union>ufDom\<cdot>f3-(ufRan\<cdot>f2 \<union>ufRan\<cdot>f3) "
    by (simp add: assms(2) ufCompI_def ufSerParComp_dom)
  have a1:"ufRan\<cdot>f1 \<inter> ufDom\<cdot> (ufSerParComp f2 f3) \<noteq>{}"    
    by (simp add: Diff_Int_distrib a0 assms(1) assms(3) inf_sup_distrib1)
  then show ?thesis
    by (smt Diff_disjoint a0 assms(1) assms(2) assms(3) inf_commute inf_sup_distrib1 sup_eq_bot_iff ufSerParComp_ran)
qed

lemma serparcomp_well_associativity2: 
  assumes "serparcomp_well f1 f2"
      and "serparcomp_well f2 f3"
      and "serparcomp_well f1 f3" 
    shows "serparcomp_well (ufSerParComp f1 f2) f3"
proof-
  have a1:" ufRan\<cdot>(ufSerParComp f1 f2)=ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    by (simp add: assms(1) ufSerParComp_ran)
  have a2:" ufRan\<cdot>(ufSerParComp f1 f2) \<inter>ufDom\<cdot>f3 \<noteq>{} "
    by (simp add: Int_Un_distrib2 a1 assms(3))
  have a3:"ufDom\<cdot>(ufSerParComp f1 f2) \<inter>ufRan\<cdot>(ufSerParComp f1 f2) ={}"
    by (metis a1 assms(1) ufCompO_def ufSerParComp_dom ufcomp_I_inter_Oc_empty)
 have a4:"ufDom\<cdot> (ufSerParComp f1 f2) = ufDom\<cdot>f1\<union>ufDom\<cdot>f2-(ufRan\<cdot>f1 \<union>ufRan\<cdot>f2) "
    by (simp add: assms(1) ufCompI_def ufSerParComp_dom)
  have a5:"ufDom\<cdot>(ufSerParComp f1 f2) \<inter> ufRan\<cdot>f3 ={}"
    by (simp add: Diff_Int_distrib2 Int_Un_distrib2 a4 assms(2) assms(3))
  then show?thesis
    by (metis Int_Un_distrib2 a1 a2 a3 assms(2) assms(3) inf.right_idem sup_inf_absorb)
qed

lemma SerParDom_Comp: assumes "serparcomp_well f1 f2" 
      and "serparcomp_well f2 f3" 
      and "serparcomp_well f1 f3"
    shows "ufDom\<cdot>(ufSerParComp f1 (ufSerParComp f2 f3)) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
  apply (subst ufSerParComp_dom)
   apply (meson assms(1) assms(2) assms(3) serparcomp_well_associativity)
  unfolding ufCompI_def
  apply (subst ufSerParComp_dom)
  using assms(2) apply blast
  apply (subst ufSerParComp_ran)
  unfolding ufCompI_def
  using assms(2) apply blast
  by blast

lemma SerParDom_Comp2: assumes "serparcomp_well f1 f2" 
      and "serparcomp_well f2 f3" 
      and "serparcomp_well f1 f3"
    shows "ufDom\<cdot>(ufSerParComp  (ufSerParComp f1 f2) f3) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
apply (subst ufSerParComp_dom)
   apply (meson assms(1) assms(2) assms(3) serparcomp_well_associativity2)
  unfolding ufCompI_def
  apply (subst ufSerParComp_dom)
  using assms(1) apply blast
  unfolding ufCompI_def
  apply (subst ufSerParComp_ran)
  using assms(1) apply blast
  by blast

lemma serparcomp_func_h: assumes "serparcomp_well f1 f2"
                   and "ufCompI f1 f2 \<subseteq> ubclDom\<cdot>ub"
                 shows "((ufSerParComp f1 f2) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(ufSerParComp f1 f2))) = 
(f1 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons>((ub\<bar>ufDom\<cdot>(ufSerParComp f1 f2))\<uplus> (f1 \<rightleftharpoons> (ub\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2)"
proof-
  have a1:" ((ub\<bar>ufDom\<cdot>(ufSerParComp f1 f2))\<bar>ufDom\<cdot>f1) = (ub\<bar>ufDom\<cdot>f1)"
    by (smt Diff_Un Un_Diff Un_Diff_Int assms(1) inf_commute inf_sup_absorb sup_bot.right_neutral ubclrestrict_twice ufCompI_def ufSerParComp_dom)
  have a2:" ((ub\<bar>ufDom\<cdot>(ufSerParComp f1 f2))\<bar>ufDom\<cdot>f2)= (ub\<bar>(ufDom\<cdot>f2-ufRan\<cdot>f1-ufRan\<cdot>f2))"
    by (smt Diff_Int2 Diff_Int_distrib2 Diff_disjoint Int_Un_distrib Int_Un_distrib2 Un_Diff_Int Un_commute assms(1) distrib_imp1 sup_bot.right_neutral ubclrestrict_twice ufCompI_def ufSerParComp_dom)
  have a3:"ufDom\<cdot>(ufSerParComp f1 f2) = ufDom\<cdot>f1 \<union> (ufDom\<cdot>f2-ufRan\<cdot>f1-ufRan\<cdot>f2)"
    by (smt Diff_Int_distrib2 Diff_Un Diff_empty Un_Diff Un_Diff_Int Un_commute assms(1) inf_commute sup_bot.right_neutral ufCompI_def ufSerParComp_dom)
  have a4:"ubclDom\<cdot>(ub\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) =ufCompI f1 f2 "
    by (metis (no_types, lifting) assms(1) assms(2) inf.absorb_iff2 ubclrestrict_ubcldom ufSerParComp_dom)
 have a5: "(Rep_cufun (ufSerParComp f1 f2)) = ((\<lambda>ub. (ubclDom\<cdot>ub = ufCompI f1 f2)\<leadsto>(f1 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons>(ub\<uplus> (f1 \<rightleftharpoons> (ub\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2)))"
   by (simp add: assms(1) ufSerParComp_repAbs)
  have a6:"Rep_cufun (ufSerParComp f1 f2) (ub \<bar> ufDom\<cdot>(ufSerParComp f1 f2)) = 
    Some ((f1 \<rightleftharpoons> (ub \<bar> ufDom\<cdot>(ufSerParComp f1 f2)) \<bar> ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons>(ub \<bar> ufDom\<cdot>(ufSerParComp f1 f2))\<uplus>( (f1 \<rightleftharpoons> ((ub \<bar> ufDom\<cdot>(ufSerParComp f1 f2))\<bar>ufDom\<cdot>f1)))\<bar>ufDom\<cdot>f2)) "
    by (simp add: a4 a5)
   show ?thesis
    by (simp add: a1 a6)
qed       

lemma ufSerParComp_asso: 
  assumes "serparcomp_well f1 f2" 
      and "serparcomp_well f2 f3" 
      and "serparcomp_well f1 f3"
    shows "(ufSerParComp f1 (ufSerParComp f2 f3)) = (ufSerParComp (ufSerParComp f1 f2) f3)"
proof - 
  have h1:" ufDom\<cdot>(ufSerParComp f1 f2) \<subseteq> (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 )"
  proof-
    have a1:" ufDom\<cdot>(ufSerParComp f1 f2) = (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 ) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 )"
      by (simp add: assms(1) ufCompI_def ufSerParComp_dom)
    have a2:" (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ) = (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 )"     
      by (smt Diff_Un Diff_empty Un_Diff Un_Diff_Int assms(2) assms(3) sup_bot.right_neutral)
    then show ?thesis
      by (simp add: Un_Diff a1)
  qed
  have h2:" \<forall> x. (ubclDom\<cdot>x =(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<longrightarrow>((ubclDom\<cdot>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)) = ufRan\<cdot>f1)"
      apply rule
      by (smt Diff_Un Int_Diff Un_Diff_Int assms(1) assms(3) inf_commute inf_left_commute inf_sup_absorb sup_bot.right_neutral ubclrestrict_ubcldom ufran_2_ubcldom2)
   have h3:" (ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ) \<subseteq>((ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<union> ufRan\<cdot>f1"
     by blast
   have h4:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>( ufDom\<cdot>(ufSerParComp f2 f3)\<subseteq>(ubclDom\<cdot>x \<union> ubclDom\<cdot>(f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)) ) "
     by (simp add: h2 h3 assms(2) ufCompI_def ufSerParComp_dom)
   have h5:"((ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<inter>ufDom\<cdot>f2 = ufDom\<cdot>(ufSerParComp f1 f2)\<inter>ufDom\<cdot>f2 "
          by (smt Diff_Un Int_Diff Un_Diff_Int Un_commute assms(1) assms(2) inf_assoc inf_commute inf_sup_absorb sup_bot.right_neutral ufCompI_def ufSerParComp_dom)      
   have c1_1:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((ufSerParComp f1 (ufSerParComp f2 f3)) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp f1 (ufSerParComp f2 f3))= (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> ((ufSerParComp f2 f3) \<rightleftharpoons> x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)))"
     by (smt SerParDom_Comp assms(1) assms(2) assms(3) serparcomp_well_associativity ubclrestrict_dom_id ufSerParComp_apply)
   have c1_2:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>( (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<uplus>((ufSerParComp f2 f3) \<rightleftharpoons> x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)) = (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<uplus>(f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2) \<uplus> (f3 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)) \<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3))"
     by (metis (no_types, lifting) h4 Int_lower1 assms(2) serparcomp_func_h ubclunion_asso ubclunion_ubcldom ufSerParComp_dom)     
   have c2_1:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((ufSerParComp (ufSerParComp f1 f2) f3) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp (ufSerParComp f1 f2) f3) =((ufSerParComp f1 f2) \<rightleftharpoons> x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f3 \<rightleftharpoons> x \<uplus> ((ufSerParComp f1 f2) \<rightleftharpoons> x\<bar>ufDom\<cdot>(ufSerParComp f1 f2))\<bar>ufDom\<cdot>f3))"
     by (smt SerParDom_Comp2 assms(1) assms(2) assms(3) serparcomp_well_associativity2 ubclrestrict_dom_id ufSerParComp_apply) 
   have c2_2:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((((ufSerParComp f1 f2) \<rightleftharpoons> x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f3 \<rightleftharpoons> x \<uplus> ((ufSerParComp f1 f2) \<rightleftharpoons> x\<bar>ufDom\<cdot>(ufSerParComp f1 f2))\<bar>ufDom\<cdot>f3))= ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3))"
     by (metis assms(1) h1 serparcomp_func_h ufSerParComp_dom)
   have b0:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<uplus>(f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2) \<uplus> (f3 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)) \<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3)= ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3))"
   proof-
     have a1:"  \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2) )= ((f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2)) )"
       by (metis (no_types, lifting) h5 ubclrestrict_dom_id ubclrestrict_twice ubclunion_ubclrestrict)
     have a200:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)) \<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3= ((x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3)\<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3)"
       by (simp add: ubclrestrict_twice ubclunion_ubclrestrict)
     have a201:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3)\<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3= ((((x\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3) \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3))\<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3)"
       by (simp add: ubclrestrict_twice ubclunion_ubclrestrict)
     have a210:"  \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(( x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3)= ( (x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3))"
       by (simp add: ubclunion_asso)
     have a211:"  \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(( (x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3)= ( ((x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f3) \<uplus> ((f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3)))" 
       by (simp add: ubclrestrict_twice ubclunion_ubclrestrict)
     have a212:"  \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(( (x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3)= ( ((x\<bar>ufDom\<cdot>f3) \<uplus> (((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f3) \<uplus> ((f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3)))" 
       by (simp add: ubclrestrict_twice ubclunion_ubclrestrict)
     have a220:"  \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((((x\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3) \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3))\<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3= ( ((x\<bar>ufDom\<cdot>f3) \<uplus> (((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f3) \<uplus> ((f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3)))" 
     proof-
       have h11:" ((ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<inter> ((ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<inter> ufDom\<cdot>f3 = ((ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<inter> ufDom\<cdot>f3"
         by blast
       have f1:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((x\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3) = (x\<bar>ufDom\<cdot>f3))"
         by (metis (no_types, lifting) assms(2) h11 ubclrestrict_dom_id ubclrestrict_twice ufCompI_def ufSerParComp_dom)           
       have h22:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>( ufRan\<cdot>f1 \<inter>((ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ) )\<inter>ufDom\<cdot>f3 =ufRan\<cdot>f1 \<inter>ufDom\<cdot>f3)" 
         by (smt Diff_Int_distrib Diff_empty Un_commute assms(1) assms(2) assms(3) inf_commute inf_left_commute inf_sup_absorb serparcomp_well_associativity ufSerParComp_ran)         
       have h230:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3)= (  (((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>(ufDom\<cdot>f3\<inter>ufDom\<cdot>(ufSerParComp f2 f3))) )"
         by (simp add: inf_commute ubclrestrict_twice)
       have h231:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>(ufDom\<cdot>f3\<inter>ufDom\<cdot>(ufSerParComp f2 f3)))))= ((((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>(ufDom\<cdot>f3\<inter>ufDom\<cdot>(ufSerParComp f2 f3)\<inter>ufRan\<cdot>f1)) )"
         by (smt h2 inf_commute ubclrestrict_dom_id ubclrestrict_twice)      
       have h23:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3)= (  (((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>(ufDom\<cdot>f3\<inter>ufRan\<cdot>f1)) )"
         by (smt assms(2) h22 h230 h231 inf_assoc inf_commute ufCompI_def ufSerParComp_dom)    
       have h24:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f3) = (  (((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>(ufDom\<cdot>f3\<inter>ufRan\<cdot>f1)))))"
         by (smt h2 inf_commute ubclrestrict_dom_id ubclrestrict_ubcldom ubclunion_restrict2 ubclunion_ubclrestrict_minus_id)
       have f2:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>(((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))\<bar>ufDom\<cdot>f3)= (  (((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f3) )"
         using h23 h24 by auto
       have f3:"\<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3= (((f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3))"     
         using a1 by auto
       then show ?thesis
         by (smt f1 f2 inf.idem ubclrestrict_twice ubclunion_ubclrestrict)
     qed
     have a2_2:"  \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)) \<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3= ( x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3))"
       using a200 a201 a210 a212 a220 by presburger
        have a2:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((f3 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)) \<uplus> (f2 \<rightleftharpoons> (x \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1))\<bar>ufDom\<cdot>f2)\<bar>ufDom\<cdot>f3)= (f3 \<rightleftharpoons> x \<uplus> ((f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2)) \<uplus> (f1 \<rightleftharpoons> x\<bar>ufDom\<cdot>f1)\<bar>ufDom\<cdot>f2))\<bar>ufDom\<cdot>f3))"
          using a2_2 by auto
        then show?thesis
          using a1 by auto
      qed
   have b1:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or>((ufSerParComp (ufSerParComp f1 f2) f3) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp (ufSerParComp f1 f2) f3) =(ufSerParComp f1 (ufSerParComp f2 f3)) \<rightleftharpoons>x\<bar> ufDom\<cdot>(ufSerParComp f1 (ufSerParComp f2 f3))) "
     using c1_2 c2_2 c1_1 c2_1 b0 
     by presburger
   have b2_1:" \<forall> x. (ubclDom\<cdot>x \<noteq>(ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 ))\<or> ((((ufSerParComp f1 f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(ufSerParComp f1 f2))) \<uplus> (f3\<rightleftharpoons>(x\<uplus> ((ufSerParComp f1 f2) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2))))\<bar>ufDom\<cdot>f3 ))=((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((ufSerParComp f2 f3) \<rightleftharpoons>(x\<uplus> ( f1\<rightleftharpoons>x \<bar> ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3))))) "
     using c1_1 c2_1 b1 by auto
   have b2: "(\<lambda> x. (ubclDom\<cdot>x = ufCompI  (ufSerParComp f1 f2)f3  ) \<leadsto> (((ufSerParComp f1 f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(ufSerParComp f1 f2))) \<uplus> (f3\<rightleftharpoons>(x\<uplus> ((ufSerParComp f1 f2) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2))))\<bar>ufDom\<cdot>f3 )))
          = (\<lambda> x. (ubclDom\<cdot>x =ufCompI f1 (ufSerParComp f2 f3)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((ufSerParComp f2 f3) \<rightleftharpoons>(x\<uplus> ( f1\<rightleftharpoons>x \<bar> ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)))))" 
   proof-
     have a1:" ufCompI  (ufSerParComp f1 f2)f3 = (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 )"
       by (smt SerParDom_Comp2 assms(1) assms(2) assms(3) serparcomp_well_associativity2 ufSerParComp_dom)
     have a2:" ufCompI f1 (ufSerParComp f2 f3) = (ufDom\<cdot>f1\<union>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1\<union>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 )"
       by (smt SerParDom_Comp assms(1) assms(2) assms(3) serparcomp_well_associativity ufSerParComp_dom)
     then show ?thesis
       by (metis (no_types, hide_lams) assms(1) assms(2) b2_1 a1 ufSerParComp_dom)
   qed
   then have b3: "Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufCompI  (ufSerParComp f1 f2)f3  ) \<leadsto> (((ufSerParComp f1 f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(ufSerParComp f1 f2))) \<uplus> (f3\<rightleftharpoons>(x\<uplus> ((ufSerParComp f1 f2) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(ufSerParComp f1 f2))))\<bar>ufDom\<cdot>f3 )))
          = Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 (ufSerParComp f2 f3)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((ufSerParComp f2 f3) \<rightleftharpoons>(x\<uplus> ( f1\<rightleftharpoons>x \<bar> ufDom\<cdot>f1)\<bar>ufDom\<cdot>(ufSerParComp f2 f3)))))"
     by auto
   then show ?thesis    
     by (metis(no_types) ufSerParComp_def)
 qed
end