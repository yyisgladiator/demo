theory SerCompRestricted
  imports   UFun_applyIn SerParComposition
begin 


default_sort ubcl_comp


definition ufSerCompRestricted :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun" (infixl "\<circ>\<^sub>i" 50) where
"ufSerCompRestricted f1 f2 \<equiv> ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot>(ufSerParComp f1 f2)"


section\<open>Used Lemmas\<close>

lemma ufApplyOut_cont: "cont (ufApplyOut)"
  sorry

lemma ufapplyout_apply [simp]:  assumes "ubclDom\<cdot>ub = ufDom\<cdot>f"
  shows "(ufApplyOut k\<cdot>f) \<rightleftharpoons> ub = k\<cdot>(f\<rightleftharpoons>ub)"
  sorry
lemma ufapplyout_dom [simp]:
  shows "ufDom\<cdot>(ufApplyOut k\<cdot>f) = ufDom\<cdot>f"
  sorry

lemma ufapplyout_ran [simp]:
  shows "ufRan\<cdot>(ufApplyOut k\<cdot>f) = ufRan\<cdot>f"
  sorry


section\<open>Lemmas about SerCompRestricted\<close>
lemma ufSerCompRestricted_cont: "cont (\<lambda>x.  (ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot>(ufSerParComp f1 f2)\<rightleftharpoons>x))"
proof -
  have a1:" cont (\<lambda>x. (ufSerParComp f1 f2)\<rightleftharpoons>x)"
    using cont_compose by force
  have a2:" cont (\<lambda>x.  (ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot>(ufSerParComp f1 f2)\<rightleftharpoons>x))"
   using cont_Rep_cfun2 cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed

lemma ufSerCompRestricted_well:
  assumes " serparcomp_well f1 f2"
  shows "ufWell (\<Lambda> x  . (ubclDom\<cdot>x =  ufCompI f1 f2) \<leadsto>(ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot>(ufSerParComp f1 f2)\<rightleftharpoons>x))"
   apply(simp add: ufWell_def)
  apply rule
   apply (rule_tac x="ufCompI f1 f2" in exI)
   apply rule
   apply (simp add: domIff ufSerCompRestricted_cont)
 apply (rule_tac x="ufRan\<cdot>f2" in exI)
  apply rule
  apply (simp add: ufSerCompRestricted_cont)
  by (smt SerCompRestricted.ufapplyout_apply UFun_Comp.ufran_least assms option.distinct(1) option.sel ran2exists ubclrestrict_ubcldom ubclunion_commu ubclunion_restrict3 ubclunion_ubcldom ufSerParComp_dom ufSerParComp_ran ufran_2_ubcldom2)
 

lemma ufSerCompRestricted_repAbs: assumes  "serparcomp_well f1 f2"
  shows "Rep_cufun (ufSerCompRestricted  f1 f2) = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot>(ufSerParComp f1 f2)\<rightleftharpoons>x))"
  apply(subst ufDom_def, simp add: ufSerCompRestricted_def)
  apply (simp add: domIff ufSerCompRestricted_cont)
proof -
have f1: "\<forall>u C. ubclDom\<cdot> (u \<rightleftharpoons> (SOME a. ubclDom\<cdot>(a::'a) = C)::'a) = ufRan\<cdot>u \<or> C \<noteq> ufDom\<cdot>u"
  by (metis ubclDom_h ufran_2_ubcldom2)
  then have f2: "ubclDom\<cdot> (f1 \<rightleftharpoons> (SOME a. ubclDom\<cdot>a = ufDom\<cdot>f1)) \<inter> ufDom\<cdot>f2 \<noteq> {}"
    by (metis assms)
  have f3: "\<forall>C u a. ubclDom\<cdot>(u \<rightleftharpoons> (a::'a)::'a) \<inter> C = ubclDom\<cdot> (ufApplyOut (ubclRestrict C)\<cdot>u \<rightleftharpoons> a) \<or> ubclDom\<cdot>a \<noteq> ufDom\<cdot>u"
    by (metis SerCompRestricted.ufapplyout_apply ubclrestrict_ubcldom)
  have "\<forall>u c. ubclDom\<cdot> (ufApplyOut c\<cdot>u \<rightleftharpoons> (SOME a. ubclDom\<cdot>(a::'a) = ufDom\<cdot>u)::'a) = ubclDom\<cdot> (u \<rightleftharpoons> (SOME a. ubclDom\<cdot>a = ufDom\<cdot>u)::'a)"
using f1 SerCompRestricted.ufapplyout_dom SerCompRestricted.ufapplyout_ran by blast
  then show "Rep_cufun (ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot> (f1 \<circ>\<parallel> f2)) = (\<lambda>x. (ubclDom\<cdot>x = ubclDom\<cdot> (SOME b. \<exists>y. Rep_cufun f1 b = Some y))\<leadsto>ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot> (f1 \<circ>\<parallel> f2) \<rightleftharpoons> x)"
    using f3 f2 ubclDom_h by blast
qed


lemma ufSerCompRestricted_apply: 
  assumes "serparcomp_well f1 f2" and "ubclDom\<cdot>x = ufDom\<cdot>(ufSerCompRestricted f1 f2)"
  shows  "(ufSerCompRestricted f1 f2)\<rightleftharpoons>x = ((ufApplyOut (ubclRestrict (ufRan\<cdot>f2))\<cdot>(ufSerParComp f1 f2)\<rightleftharpoons>x))"
  apply (subst ufSerCompRestricted_repAbs)
  using assms(1) apply blast
  by (smt assms(1) ufSerCompRestricted_def ufSerCompRestricted_repAbs)

lemma ufSerCompRestricted_dom:
assumes "serparcomp_well f1 f2"
 shows "ufDom\<cdot>(ufSerCompRestricted f1 f2) =  ufCompI f1 f2"
   unfolding ufSerCompRestricted_def
  apply (subst  ufapplyout_dom) 
  using assms ufSerParComp_dom by blast

lemma ufSerCompRestricted_ran: assumes "serparcomp_well f1 f2"
  shows "ufRan\<cdot>(ufSerCompRestricted f1 f2) = ufRan\<cdot>f2"
  unfolding ufSerCompRestricted_def
  apply (subst  ufapplyout_ran) 
  using assms ufSerParComp_ran 
  by (metis (no_types, hide_lams) SerCompRestricted.ufapplyout_apply SerCompRestricted.ufapplyout_dom SerCompRestricted.ufapplyout_ran UFun_Comp.ufran_least ubcldom_least_cs ubclunion_ubcldom)
 
end