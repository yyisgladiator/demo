(*  Title:        UFun_Comp
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines Composition of "Processing functions" 
*)

theory UFun_Comp
  imports UFun
begin

  
default_sort ubcl_comp  
  
  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)    

  
(* abbreviations should be defined in the classes or ufun.thy *)
subsection\<open>abbreviations\<close>


abbreviation ubclRestrict_abbr :: " 'm \<Rightarrow> channel set \<Rightarrow> 'm" ("(_\<bar>_)" [66,65] 65)
where "b\<bar>cs \<equiv> ubclRestrict cs\<cdot>b"

  
subsection\<open>definitions\<close>  

  
definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) ufun" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubclDom\<cdot>sb = cin) \<leadsto> ubclLeast cout)"  

definition ufRestrict :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) ufun \<rightarrow> ('in,'out) ufun" where
"ufRestrict In Out \<equiv> (\<Lambda> f. if (ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out) then f else (ufLeast In Out))"

definition ufLift :: "channel set \<Rightarrow> ('a::ubcl_comp \<rightarrow> 'b::ubcl_comp) \<Rightarrow> ('a \<Rrightarrow> 'b)" where
"ufLift cs \<equiv> (\<lambda> f . Abs_ufun (\<Lambda> sb. (ubclDom\<cdot>sb = cs) \<leadsto> (f\<cdot>sb)))"

definition ufHide :: "('in,'out) ufun \<Rightarrow> channel set \<Rightarrow> ('in,'out) ufun" (infixl "\<h>" 100) where
"ufHide f cs \<equiv> Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f ) \<leadsto> ((f\<rightleftharpoons>x) \<bar> (ufRan\<cdot>f - cs)))"


subsection\<open>channel sets\<close>

  
text {* the input channels of the composition of f1 and f2 *}
definition ufCompI :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> channel set" where
"ufCompI f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the internal channels of the composition of f1 and f2 *}
definition ufCompL :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> channel set" where
"ufCompL f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the output channels of the composition of f1 and f2 *}
definition ufCompO :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> channel set" where
"ufCompO f1 f2 \<equiv> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* all channels of the composition of f1 and f2  *}
definition ufCompC :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> channel set" where
"ufCompC f1 f2 \<equiv> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"


subsection \<open>ubFix\<close>
  
  
definition ubFix :: "('m \<rightarrow> 'm) \<Rightarrow> channel set \<Rightarrow> 'm" where 
"ubFix F cs = (\<Squnion>i. iterate i\<cdot>F\<cdot>(ubclLeast cs))"

text {* special case ubFix for cont of the composition *}
definition ubFix2 :: "('m  \<Rightarrow> 'm  \<rightarrow> 'm ) \<Rightarrow> 'm  \<Rightarrow> channel set \<Rightarrow> 'm " where
"ubFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(ubclLeast cs))"

abbreviation iter_ubfix2 :: "('m \<Rightarrow> 'm \<rightarrow> 'm) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm \<Rightarrow> 'm" where
"iter_ubfix2 F i cs \<equiv>  (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(ubclLeast cs))"

text {* ubfun_io_eq f cs is true if f applied to the least ub  with domain cs delivers a 
        ub with the same domain *}
abbreviation ubfun_io_eq :: "('m \<rightarrow> 'm ) \<Rightarrow> channel set \<Rightarrow> bool" where
"ubfun_io_eq f cs \<equiv> ubclDom\<cdot>(f\<cdot>(ubclLeast cs)) = cs"


subsection \<open>composition helpers\<close>

 
definition ufCompH :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> 'm \<Rightarrow> ('m \<rightarrow> 'm)" where
"ufCompH f1 f2 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)))"

abbreviation iter_ufCompH :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> nat \<Rightarrow> 'm  \<Rightarrow> 'm" where
"(iter_ufCompH f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))" 


subsection \<open>composition operators\<close>

definition comp_well :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> bool" where
"comp_well f1 f2 \<equiv> ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
                                       

definition ufComp :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun" (infixl "\<otimes>" 50) where
"ufComp f1 f2 \<equiv>
let I = ufCompI f1 f2;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)
in Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = I) \<leadsto> ubFix (ufCompH f1 f2 x) Oc))" 


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)  


subsection \<open>ufHide\<close>

lemma ufhide_cont: "cont (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f ) \<leadsto> ((f\<rightleftharpoons>x) \<bar> (ufRan\<cdot>f - cs)))"
  by (simp add: cont_compose)

lemma ufhide_well: "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f ) \<leadsto> ((f\<rightleftharpoons>x) \<bar> (ufRan\<cdot>f - cs)))"
  apply(simp add: ufWell_def ufhide_cont)
  apply rule
   apply(rule_tac x="ufDom\<cdot>f" in exI)
   apply (simp add: domIff)
  apply(rule_tac x="ufRan\<cdot>f - cs" in exI)
  by (smt Int_Diff option.distinct(1) option.sel ran2exists ubclrestrict_dom_id ubclrestrict_ubcldom ufran_2_ubcldom2)

lemma ufhide_dom: "ufDom\<cdot>(f \<h> cs) = ufDom\<cdot>f"
  by (smt Abs_cfun_inverse2 domIff rep_abs_cufun2 ubcldom_least_cs ufHide_def ufhide_cont ufhide_well ufun_least_in_dom)

lemma ufhide_ran: "ufRan\<cdot>(f \<h> cs) = ufRan\<cdot>f - cs"
  by (smt Abs_cfun_inverse2 Int_Diff inf.idem option.sel rep_abs_cufun2 ubcldom_least_cs ubclrestrict_ubcldom ufHide_def ufhide_cont ufhide_dom ufhide_well ufran_least)

lemma ufhide_apply: assumes "ubclDom\<cdot>ub = ufDom\<cdot>f" 
  shows "(f \<h> cs) \<rightleftharpoons> ub = ubclRestrict (ufRan\<cdot>f - cs)\<cdot>(f \<rightleftharpoons> ub)"
  by (simp add: assms ufHide_def ufhide_cont ufhide_well)

lemma ufhide_id:
  assumes "ufRan\<cdot>f \<inter> cs = {}" 
  shows   "f \<h> cs = f"
  by (metis Diff_triv assms ubclrestrict_dom_id ufhide_apply ufhide_dom ufran_2_ubcldom2 ufun_eqI)

subsection \<open>ubclLeast\<close>
  
(* ubclLeast is in the same dome as the function f  *)
lemma ufunLeastIDom: "(ubclLeast (ufDom\<cdot>f)) \<in> dom (Rep_cufun f)"
  by (metis rep_ufun_well domD ubcldom_least_cs ufWell_def ufdom_2ufundom)

(* The range of an ufun is equal to the domain of f applied to the least ubundle with domain 
       ufDom f *)
lemma ufran_least: "ufRan\<cdot>f = ubclDom\<cdot>(f\<rightleftharpoons>(ubclLeast (ufDom\<cdot>f)))"
  apply (simp add: ufRan_def)
  by (metis (no_types) domD option.sel ufunLeastIDom ufran_2_ubcldom ufran_insert)

(* ubclLeast of {cs1} ubclRestricted to {cs2} is equal to ubclLeast of the intersection of {cs1} and {cs2} *)
lemma ubclrestrict_ubclleast_inter: "(ubclRestrict (cs2)\<cdot>(ubclLeast cs1))  = ubclLeast (cs1 \<inter> cs2)"
  by (metis (no_types, lifting) below_antisym monofun_cfun_arg sup_inf_absorb ubcldom_least
      ubcldom_least_cs ubclrestrict_dom_id ubclrestrict_twice ubclrestrict_ubcldom ubclunion_restrict2 ubclunion_ubcldom)


subsection \<open>ubclRestrict\<close>

(* ubclDom of ufun applied to ubundle restricted to ufdom of ufun is equal to the range of ufun *)
lemma ufun_ubclrestrict_ubcldom: assumes "ufDom\<cdot>f \<subseteq> ubclDom\<cdot>ub"
  shows "ubclDom\<cdot>(f \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f)\<cdot>ub)) = ufRan\<cdot>f"
  by (simp add: assms subset_antisym ubclrestrict_ubcldom ufran_2_ubcldom2)


subsection\<open>ubFix\<close>
 
(* ub fix iteration is a chain  *)
lemma ub_iterate_chain: "ubclDom\<cdot>(F\<cdot>(ubclLeast cs)) = cs \<Longrightarrow> chain (\<lambda>i. iterate i\<cdot>F\<cdot>(ubclLeast cs))"
  apply (rule chainI, subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by (metis ubcldom_least)

(* ubFix2 is a special case of ubFix *)
lemma ubfix_2_ubfix2: "ubFix (F x) cs = ubFix2 F x cs"
  by (metis (mono_tags, lifting) lub_eq ubFix2_def ubFix_def)  

(* ubFix2 is equal to the iter_ubfix2 abbr  *)
lemma ubfix2iter_eq: "ubFix2 F x cs = (\<Squnion> i. iter_ubfix2 F i cs x)"
  using ubFix2_def by force


subsubsection \<open>iter_ubFix2\<close>
    
(* the iteration over F is continuous in x *)
lemma iter_ubfix2_cont [simp]: assumes "cont F"
  shows "cont (\<lambda> x. iter_ubfix2 F i cs x)"
  by (simp add: assms)

(* helper for monoton proof over x *)
lemma iter_ubfix2_mono_pre: assumes "cont F" and "x \<sqsubseteq> y"
  shows "\<forall> i. (iter_ubfix2 F i cs x) \<sqsubseteq> (iter_ubfix2 F i cs y)"
  by (simp add: assms(1) assms(2) cont2monofunE monofun_cfun_fun)

(* iter_ubfix2 is a chain if the domain are the same  *)
lemma iter_ubfix2_chain: assumes "ubfun_io_eq (F x) cs"
  shows "chain (\<lambda> i. iter_ubfix2 F i cs x)"
  by (simp add: assms ub_iterate_chain)

(* the domain is always the same if io_eq holds *)
lemma iter_ubfix2_dom: assumes "ubfun_io_eq (F x) cs"
  shows "ubclDom\<cdot>(iter_ubfix2 F i cs x) = cs"
proof (induction i)
  case 0
  then show ?case
    by (metis assms iterate_0 ubcldom_fix ubcldom_least)
next
  case (Suc i)
  then show ?case
  proof -
    have "ubclLeast cs \<sqsubseteq> iter_ubfix2 F i cs x"
      by (metis Suc.IH ubcldom_least)
    then have "\<forall>c. ubclDom\<cdot>(c\<cdot>(iter_ubfix2 F i cs x)) = ubclDom\<cdot>(c\<cdot>(ubclLeast cs)::'a)"
      using monofun_cfun_arg ubcldom_fix by blast
    then show ?thesis
      by (simp add: assms)
  qed
qed

  
subsubsection \<open>lub_iter_ubfix2\<close>
  
(* mono *)
(* the lub of x and lub of y has the same relation as x and y  *)
lemma lub_iter_ubfix2_mono_pre [simp]: assumes "x \<sqsubseteq> y" and "cont F" and "ubfun_io_eq (F x) cs"
  shows "(\<Squnion> i. iter_ubfix2 F i cs x) \<sqsubseteq> (\<Squnion> i. iter_ubfix2 F i cs y)"
proof -
  have f1: "\<And> i. (iter_ubfix2 F i cs x) \<sqsubseteq>  (iter_ubfix2 F i cs y)"
    by (simp add: assms(1) assms(2) iter_ubfix2_mono_pre)
  have f2: "ubclDom\<cdot>x = ubclDom\<cdot>y"
    by (simp add: assms(1) ubcldom_fix)
  have f3: "ubfun_io_eq (F y) cs"
    using assms(1) assms(2) assms(3) cont2monofunE monofun_cfun_fun ubcldom_fix by blast
  then show ?thesis
    by (simp add: assms(3) f1 lub_mono ub_iterate_chain)
qed

(* cont *)
(* a chain of the last argument can be build with the lub of the second one  *)
lemma chain_lub_iter_sbfix2: assumes "chain Y" and "cont F" and "ubfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_ubfix2 F ia cs (Y i))"
proof -
  have f1: "\<And> i. (Y i) \<sqsubseteq> (Y (Suc i))"
    by (simp add: assms(1) po_class.chainE)
  have f2: "\<And> ia. ubfun_io_eq (F (Y ia)) cs"
    using assms(1) assms(2) assms(3) cont2monofunE is_ub_thelub monofun_cfun_fun ubcldom_fix by blast
  thus ?thesis
    apply (subst chainI, simp_all)
    by (simp add: assms(2) f1)
qed

(*   *)
lemma chain_lub_lub_iter_ubfix2: assumes "chain Y" and "cont F" 
                                  and "ubfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "(\<Squnion> i ia. iter_ubfix2 F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_ubfix2 F ia cs (Y i))"
proof -
  have f1: "\<And> i. cont (\<lambda> x. iter_ubfix2 F i cs x)"
    by (simp add: assms(2))
  moreover
  have f2: "(\<Squnion>i. iter_ubfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_ubfix2 F ia cs (Y i))"
    by (metis (no_types) assms(1) assms(2) ch2ch_Rep_cfunR ch2ch_cont cont2contlubE 
              contlub_cfun_arg contlub_cfun_fun)
  moreover
  have f3: "\<And> ia. ubfun_io_eq (F (Y ia)) cs"
    using assms(1) assms(2) assms(3) cont2monofunE is_ub_thelub monofun_cfun_fun ubcldom_fix by blast
  ultimately show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_ubfix2_chain)
qed
 
(* dom *)
(* the lub of the second arg has the similar channel set to the result of F x  *)
lemma lub_iter_ubfix2_dom: assumes "ubfun_io_eq (F x) cs"
  shows "ubclDom\<cdot>(\<Squnion>i. iter_ubfix2 F i cs x) =  cs"
proof -
  have "\<And>n. ubfun_io_eq (iterate n\<cdot>(F x)) cs"
    by (simp add: assms iter_ubfix2_dom)
  then show ?thesis
    by (metis (no_types, lifting) assms is_ub_thelub lub_eq ub_iterate_chain ubcldom_fix)
qed
    

subsubsection \<open>if_lub_iter_ubfix2\<close>
  
(* mono *)
(* the processing function has the same relation as its last argument *)
lemma if_lub_iter_ubfix2_mono_pre: assumes "x\<sqsubseteq> y" and "cont F"
                                   and "(P x) \<Longrightarrow> ubfun_io_eq (F x) cs"
                                   and "ubclDom\<cdot>x = ubclDom\<cdot>y \<Longrightarrow> (P x) = (P y)"
  shows "((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x)) x)
         \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x)) y)"
proof (cases "(P x)")
  case True
  hence f1: "ubfun_io_eq (F x) cs"
    by (simp add: assms(3))
  have f2: "ubclDom\<cdot>x = ubclDom\<cdot>y"
    by (simp add: assms(1) ubcldom_fix)
  have f3: "(\<Squnion>i.(iter_ubfix2 F i cs) x) \<sqsubseteq> (\<Squnion>i.(iter_ubfix2 F i cs) y)"
    by (simp add: assms(1) assms(2) f1)
  thus ?thesis
    using assms(4) f2 some_below by auto
next
  case False
  have "ubclDom\<cdot>y = ubclDom\<cdot>x"
    by (metis assms(1) ubcldom_fix)
  then show ?thesis
    using False assms(4) by auto
qed

(* Intro lemma for if ubfix is mono *)  
(* the processing function is mono on the last argument of iter_ubfix2  *)
lemma ubfix_monoI [simp]: assumes "cont F" "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                          and "\<And> x y. ubclDom\<cdot>x = ubclDom\<cdot>y \<Longrightarrow> P x = P y"
                        shows "monofun (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x))"
proof (rule monofunI)
    fix x :: "'a" and y :: "'a"
    assume a1: "x \<sqsubseteq> y"
   show "(P x)\<leadsto>\<Squnion>n. iter_ubfix2 F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_ubfix2 F n cs y"
   proof (cases "P x")
     case True
     have f10: "P y"
       using True a1 assms(3) ubcldom_fix by blast
     have "(\<Squnion>n. iter_ubfix2 F n cs x) \<sqsubseteq> (\<Squnion>n. iter_ubfix2 F n cs y)"
       by (simp add: True a1 assms(1) assms(2))
     then show ?thesis 
       by (simp add: True f10 some_below)
   next
     case False
     then have "P y \<Longrightarrow> False"
       using a1 assms(3) ubcldom_fix by blast
       then show ?thesis 
         using False by auto
   qed
 qed

(* cont *)  
(* two lubs can be merged together if a function F is cont in x for every i *)
lemma cont2lub_lub_eq: assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
  by (simp add: cont cont2lub_lub_eq)

(* lub of iter_ubfix2 is less or eq to the lub of the chain  on case P is true *)
lemma chain_if_lub_iter_ubfix2_case:  assumes "P (\<Squnion>i. Y i)" 
                                      and  "chain Y" and "cont F"
                                      and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                                      and "\<And> x y. ubclDom\<cdot>x = ubclDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_ubfix2 F ia cs) (Y i)))"
proof -
  have f2: "(\<Squnion>i. iter_ubfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_ubfix2 F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f4: "Some (\<Squnion>i ia. iter_ubfix2 F i cs (Y ia)) \<sqsubseteq> Some (\<Squnion>i ia.  iter_ubfix2 F ia cs (Y i))"
    by (simp add: assms(1) assms(2) assms(3) assms(4) chain_lub_lub_iter_ubfix2 some_below)
  have f5: "(\<Squnion>i. (P (Y i)) \<leadsto>   \<Squnion>ia. iter_ubfix2 F ia cs (Y i)) 
                 = (\<Squnion>i. Some(\<Squnion>ia. iter_ubfix2 F ia cs (Y i)))"
    by (meson assms(1) assms(2) assms(5) is_ub_thelub ubcldom_fix)
  have "Some (\<Squnion>n na. iter_ubfix2 F na cs (Y n)) = (\<Squnion>n. Some (\<Squnion>na. iter_ubfix2 F na cs (Y n)))"
    by (simp add: assms(1) assms(2) assms(3) assms(4) chain_lub_iter_sbfix2 some_lub_chain_eq)
  then show ?thesis
      using assms(1) f2 f4 f5 by presburger
  qed

(* lub of iter_ubfix2 is less or eq to the lub of the chain *)
lemma chain_if_lub_iter_ubfix2:  assumes "chain Y" and "cont F"
                                  and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                                  and "\<And> x y. ubclDom\<cdot>x = ubclDom\<cdot>y \<Longrightarrow> P x = P y" 
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_ubfix2 F ia cs) (Y i)))"
proof (cases "P (\<Squnion>i. Y i)")
  case True
  thus ?thesis
    using  chain_if_lub_iter_ubfix2_case assms by blast
next
  case False
  hence f3: "\<And>i. \<not> (P (Y i))"
    using assms(1) assms(4) is_ub_thelub ubcldom_fix by blast
  thus ?thesis
    by (simp add: False)
qed

(* Intro lemma for cont proofs with ubfix *)
lemma ubfix_contI [simp]:   assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                             and "\<And> x y. ubclDom\<cdot>x = ubclDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "cont (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x) )"
    apply (rule contI2)
    using ubfix_monoI assms apply blast
    using chain_if_lub_iter_ubfix2 assms by blast

 
subsubsection \<open>ubFix\<close>    
    
(* ubfix is cont in X *)
lemma ubfix_contI2 [simp]: fixes F :: "'m \<Rightarrow> 'm \<rightarrow> 'm"
                            assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs"
                            and "\<And> x y. ubclDom\<cdot>x = ubclDom\<cdot>y \<Longrightarrow> P x = P y"
                          shows "cont (\<lambda> x. (P x) \<leadsto> ubFix (F x) cs)"
  apply(subst ubfix_2_ubfix2)
  apply (subst ubFix2_def)
  using ubfix_contI assms by blast

(* the domain is always the same if io_eq holds *)
lemma iter_ubfix_dom: assumes "ubfun_io_eq F cs"
  shows "ubclDom\<cdot>(iterate i\<cdot>F\<cdot>(ubclLeast cs)) = cs"
proof (induction i)
      case 0
      then show ?case
        by (metis assms iterate_0 ubcldom_fix ubcldom_least)
    next
      case (Suc i)
      then show ?case
      proof -
        have "\<And>c. (c\<cdot>(ubclLeast cs)::'a) \<sqsubseteq> c\<cdot>(F\<cdot>(ubclLeast cs))"
          by (metis (full_types) assms monofun_cfun_arg ubcldom_least)
        then show ?thesis
          by (metis (no_types) Suc iterate_Suc2 ubcldom_fix)
      qed
qed

lemma ubfix_dom: assumes "ubfun_io_eq (F) cs"
  shows "ubclDom\<cdot>(ubFix F cs) =  cs"
  by (metis (mono_tags, lifting) assms is_ub_thelub iter_ubfix_dom ubFix_def ub_iterate_chain ubcldom_fix)
 
    
subsubsection \<open>fixed point properties\<close>
    
(* ubFix calculates the fixed point *)
lemma ubfix_eq: assumes io_eq: "ubfun_io_eq F cs"
  shows "(ubFix F cs) = F\<cdot>(ubFix F cs)"
  apply (simp add: ubFix_def)
   (* perform an chain index shift by 1 *)
  apply (subst lub_range_shift [of _ 1, symmetric])
   apply (simp add: io_eq ub_iterate_chain)
  apply (subst contlub_cfun_arg)
   apply (simp add: io_eq ub_iterate_chain)
  by simp

(* ubFix calculates the least fix point  *)
lemma ubfix_least_below: assumes "ubfun_io_eq F cs" and "ubclDom\<cdot>x = cs"
  shows "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> (ubFix F cs) \<sqsubseteq> x"
  apply (simp add: ubFix_def)
  apply (rule lub_below)
   apply (simp add: assms ub_iterate_chain)
  apply (induct_tac i)
   apply (simp add: assms(2))
  using assms(2) ubcldom_least apply blast
  apply (simp add: assms(1))
  apply (erule rev_below_trans)
  by (erule monofun_cfun_arg)

(* ubFix calculates the least fixed point *)
lemma ubfix_least: assumes "ubfun_io_eq F cs" and "ubclDom\<cdot>x = cs"
                    and "F\<cdot>x = x"
  shows "(ubFix F cs) \<sqsubseteq> x"
  by (simp add: assms(1) assms(2) assms(3) ubfix_least_below)

 (* Intro rule for ubfix_eq *)
lemma ubfix_eqI: assumes fp: "F\<cdot>x = x" and lst: "\<And>z. ubclDom\<cdot>z = cs \<Longrightarrow> F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
                  and "ubfun_io_eq F cs" and "ubclDom\<cdot>x = cs"
                shows "(ubFix F cs) = x"
  by (metis assms(3) assms(4) below_antisym fp lst ubfix_dom ubfix_eq ubfix_least)  

(* compatibility lemmas to Fix.thy *)
lemma ubfix_least_iff: assumes "ubfun_io_eq F cs"
  shows "((ubFix F cs) = ubclLeast cs) = (F\<cdot>(ubclLeast cs) = ubclLeast cs)"
proof -
  have "F\<cdot>(ubFix F cs) = ubFix F cs"
    by (metis (full_types) assms ubfix_eq)
  then show ?thesis
    by (metis assms ubcldom_least ubfix_eqI)
qed

(* if F returns ubclLeast with ubclLeast as arguments then ubFix will return the ubclLeast  *)
lemma ubfix_strict: assumes "ubfun_io_eq F cs" and "F\<cdot>(ubclLeast cs) = (ubclLeast cs)"
  shows "(ubFix F cs) = ubclLeast cs"
  using assms(1) assms(2) ubfix_least_iff by blast

(* if F is not strict and returns other than ubclLeast when it has ubclLeast as argument then ubFix also returns other than ubclLeast  *)
lemma ubfix_defined: assumes "ubfun_io_eq F cs" and "F\<cdot>(ubclLeast cs) \<noteq> (ubclLeast cs)"
  shows "(ubFix F cs) \<noteq> ubclLeast cs"
  by (metis assms(1) assms(2) ubfix_eq)

(* ubFix calculates the id function  *)
lemma ubfix_id: "(ubFix (\<Lambda> x. x) cs) = (ubclLeast cs)"
  by (simp add: ubcldom_least_cs ubfix_strict)

(* ubfix will return the function if it is a constant  *)
lemma ubfix_const: assumes "ubclDom\<cdot>c = cs"
  shows "(ubFix (\<Lambda> x. c) cs) = c"
  by (metis Abs_cfun_inverse2 assms cont_const ubfix_eq)

(* ubfix induction *)
lemma ubfix_ind: assumes "ubfun_io_eq F cs"
                  and "adm P" and "P (ubclLeast cs)"
                  and "\<And> x. \<lbrakk>(ubclDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F\<cdot>x)"
  shows "P (ubFix F cs)"
proof -
  have f1: "\<And> n. ubclDom\<cdot>(iterate n\<cdot>F\<cdot>(ubclLeast cs)) = cs"
    by (simp add: assms(1) iter_ubfix_dom)
  show ?thesis
    unfolding ubFix_def
    apply (subst admD, simp_all add: assms)
      apply (simp add: assms(1) ub_iterate_chain)
      apply (rule nat_induct, simp add: assms(3))
      by (simp add: assms(4) f1)
qed

(* an adm P will hold on ubFix result if it holds on ubclLeast and for every arguments, if P holds on that argument then 
P hold on the result after the function F is applied  *)
lemma cont_ubfix_ind: assumes "cont F" and "ubfun_io_eq (Abs_cfun F) cs"
                       and "adm P" and "P (ubclLeast cs)"
                       and "\<And> x. \<lbrakk>(ubclDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F x)"
  shows "P (ubFix (Abs_cfun F) cs)"
  apply (rule ubfix_ind, simp_all add: assms)
  using assms(1) assms(2) by auto

(* P holds on ubFix with function f and channel set cs when P is adm, P holds on ubclLeast, result of f applied on ubclLeast
and also on induction step s2  *)
lemma ubfix_ind2:  assumes "ubfun_io_eq F cs"
                    and "adm P" and s0: "P ((ubclLeast cs))" and s1: "P (F\<cdot>(ubclLeast cs))"
                    and s2: "\<And> x. \<lbrakk>(ubclDom\<cdot>x) = cs; P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
  shows "P (ubFix F cs)"
  unfolding ubFix_def
  apply (subst admD, simp_all add: assms)
    apply (simp add: assms(1) ub_iterate_chain)
    apply (rule nat_less_induct)
    apply (case_tac n)
   apply (simp add: s0)
      apply (case_tac nat)
        apply (simp add: s1)
        apply (frule_tac x=nat in spec)
        by (simp add: assms(1) iter_ubfix_dom s2)
  

subsection "General Comp"

  
subsubsection \<open>ufCompHelp\<close>

lemma ufCompHelp_cont [simp]: "cont (\<lambda> last. (b \<uplus> ((Rep_cufun f1)\<rightharpoonup>(last \<bar> ufDom\<cdot>f1))
                                   \<uplus> ((Rep_cufun f2)\<rightharpoonup>(last \<bar> ufDom\<cdot>f2))))"
proof -
  have "cont (\<lambda>s. (Rep_cfun (Rep_ufun f1))\<rightharpoonup>(s\<bar>ufDom\<cdot>f1))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  hence "cont (\<lambda>s. ubclUnion\<cdot> (b \<uplus> Rep_cfun (Rep_ufun f1)\<rightharpoonup>(s\<bar>ufDom\<cdot>f1))) 
                    \<and> cont (\<lambda>s. Rep_ufun f2\<cdot>(s\<bar>ufDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda>s. b \<uplus> (Rep_cfun (Rep_ufun f1)\<rightharpoonup>(s\<bar>ufDom\<cdot>f1)) 
                     \<uplus> (Rep_cfun (Rep_ufun f2))\<rightharpoonup>(s\<bar>ufDom\<cdot>f2))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed

lemma ufCompHelp_monofun2 [simp]: 
  "monofun (\<lambda> b. \<Lambda> last. (b \<uplus> ((Rep_cufun f1)\<rightharpoonup>(last \<bar> ufDom\<cdot>f1))
                                   \<uplus> ((Rep_cufun f2)\<rightharpoonup>(last \<bar> ufDom\<cdot>f2))))"
  apply(rule monofunI)
  apply (simp add: below_cfun_def)
  by (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun)

lemma ufRanRestrict [simp]: assumes "ufDom\<cdot>f2 \<subseteq> ubclDom\<cdot>b"
  shows "ubclDom\<cdot>(Rep_cufun f2\<rightharpoonup>(b\<bar>ufDom\<cdot>f2)) = ufRan\<cdot>f2"
  using assms ubclrestrict_dom ufran_2_ubcldom2 by fastforce
    

subsubsection \<open>ChannelSets\<close>


text{* Input channels are a subset of all channels *}
lemma ufcomp_I_subset_C [simp]: "(ufCompI f1 f2) \<subseteq> (ufCompC f1 f2)"
  using ufCompI_def ufCompC_def by blast

text{* Internal channels are a subset of all channels *}
lemma ufcomp_L_subset_C [simp]: "(ufCompL f1 f2) \<subseteq> (ufCompC f1 f2)"
  using ufCompL_def ufCompC_def by blast

text{* Output channels are a subset of all channels *}
lemma ufcomp_Oc_subset_C [simp]: "(ufCompO f1 f2) \<subseteq> (ufCompC f1 f2)"
  using ufCompO_def ufCompC_def by blast

text{* Internal channels are a subset of output channels *}
lemma ufcomp_L_subset_Oc [simp]: "(ufCompL f1 f2) \<subseteq> (ufCompO f1 f2)"
  using ufCompL_def ufCompO_def by blast

text{* Input channels and Internal channels do not intersect *}
lemma ufcomp_I_inter_L_empty [simp]: "(ufCompI f1 f2) \<inter> (ufCompL f1 f2) = {}"
  using ufCompI_def ufCompL_def by blast

text{* Input channels and Output channels do not intersect *}
lemma ufcomp_I_inter_Oc_empty [simp]: "(ufCompI f1 f2) \<inter> (ufCompO f1 f2) = {}"
  using ufCompI_def ufCompO_def by blast
    
 
subsubsection \<open>commutativness\<close> 
 
text{* Input channels are commutative *}
lemma ufcomp_I_commu: "(ufCompI f1 f2) = (ufCompI f2 f1)"
  using ufCompI_def by blast

text{* Internal channels are commutative *}
lemma ufcomp_L_commu: "(ufCompL f1 f2) = (ufCompL f2 f1)"
  using ufCompL_def by blast

text{* Output channels are commutative *}
lemma ufcomp_Oc_commu: "(ufCompO f1 f2) = (ufCompO f2 f1)"
  using ufCompO_def by blast

text{* All channels are commutative *}
lemma ufcomp_C_commu: "(ufCompC f1 f2) = (ufCompC f2 f1)"
  using ufCompC_def by blast
    
    
subsubsection \<open>ufCompH\<close>

  
paragraph \<open>basic properties\<close>

  
subparagraph \<open>cont\<close>
  
lemma ufCompH_cont[simp]: 
  shows "cont (\<lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2)))"
proof -
  have f1: "cont (\<lambda> z. (f1\<rightleftharpoons>(x \<uplus> z)\<bar>ufDom\<cdot>f1))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  moreover 
  have f2: "cont (\<lambda> z. (f2\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f2)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>z. ubclUnion\<cdot>(f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1))) 
        \<and> cont (\<lambda>z. Rep_ufun f2\<cdot>((x \<uplus> z)\<bar>ufDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1)) 
                          \<uplus> (f2\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed

lemma ufCompH_cont2[simp]: 
  shows "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2)))"
proof -
  have f0: "cont (\<lambda>x. (x \<uplus> z))"
    by simp
  have f1: "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  moreover
  have f2: "cont (\<lambda> x. (f2\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f2)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>x. ubclUnion\<cdot>(f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1))) 
        \<and> cont (\<lambda>x. Rep_ufun f2\<cdot>((x \<uplus> z)\<bar>ufDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed

lemma ufCompH_continX[simp]: "cont (\<lambda> x. ufCompH f1 f2 x)"
proof -
  have "cont (\<lambda> x. \<Lambda> z. ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2))))"
    by (simp add: cont2cont_LAM)
  thus ?thesis
    by (simp add: ufCompH_def)
qed

thm ufComp_def
lemma ubcldom_lub_eq: assumes "chain Y" 
                    and  "(ubclDom\<cdot>(\<Squnion>i. Y i) = ufCompI f1 f2)"
                  shows "\<forall>ia. ubclDom\<cdot>(Y ia) = ufCompI f1 f2"
  using assms(1) assms(2) is_ub_thelub ubcldom_fix by blast

lemma ubcldom_lub_eq2I: assumes "chain Y" 
                    and  "(ubclDom\<cdot>(\<Squnion>i. Y i) = cs)"
                  shows "\<forall>ia. ubclDom\<cdot>(Y ia) = cs"
  using assms(1) assms(2) is_ub_thelub ubcldom_fix by blast

lemma ufcomph_insert: "ufCompH f1 f2 x\<cdot>z = ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2)))"
  by (simp add: ufCompH_def)

    
subparagraph \<open>dom\<close>
 
lemma ufCompH_dom [simp]: assumes "ubclDom\<cdot>x = ufCompI f1 f2"
                            and "ubclDom\<cdot>ub = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
                          shows "ubclDom\<cdot>((ufCompH f1 f2 x)\<cdot>ub) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
proof -
  have f1: "ubclDom\<cdot>(f1 \<rightleftharpoons> ((x \<uplus> ub)  \<bar> ufDom\<cdot>f1)) = ufRan\<cdot>f1"
    by (simp add: Int_absorb1 assms(1) assms(2) sup_commute sup_left_commute ubclrestrict_dom ubclunion_dom ufCompI_def ufran_2_ubcldom2)
  have f2: "ubclDom\<cdot>(f2 \<rightleftharpoons> ((x \<uplus> ub)  \<bar> ufDom\<cdot>f2)) = ufRan\<cdot>f2"
    by (simp add: Int_absorb1 assms(1) assms(2) le_supI1 ubclrestrict_dom ubclunion_dom ufCompI_def ufran_2_ubcldom2)
  show ?thesis
    apply (simp add: ufCompH_def)
    apply (simp add: ubclunion_dom)
    by (simp add: f1 f2)
qed

  
paragraph \<open>commu\<close>  

(*neu*)
lemma ufcomph_commu: assumes  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
                       and "ubclDom\<cdot>ub = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
                       and "ubclDom\<cdot>x = ufCompI f1 f2"
                     shows "(ufCompH f1 f2 x)\<cdot>ub = (ufCompH f2 f1 x)\<cdot>ub"
  apply (simp add: ufCompH_def)
  by (metis (no_types, lifting) Un_Diff_cancel2 assms(1) assms(2) assms(3) le_supI1 sup_ge1 sup_ge2 ubclunion_commu ubclunion_dom ufCompI_def ufRanRestrict)

subsubsection \<open>iterate ufCompH\<close>  

lemma iterate_ufcomph_dom:
  assumes "ubclDom\<cdot>ub = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
  and     "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "ubclDom\<cdot>(iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>ub) =  ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
  by(induction i, simp_all add: assms)

(* lub equalities *)
lemma iter_ufCompH_cont[simp]: "cont (\<lambda>x. iter_ufCompH f1 f2 i x)"
  by simp                                      

lemma iter_ufCompH_mono[simp]: "monofun (\<lambda>x. iter_ufCompH f1 f2 i x)"
  by (simp add: cont2mono)

lemma iter_ufCompH_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_ufCompH f1 f2 i) x) \<sqsubseteq> ((iter_ufCompH f1 f2 i) y)"
  using assms monofun_def by fastforce

lemma iter_ufCompH_chain[simp]: assumes "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "chain (\<lambda> i. iter_ufCompH f1 f2 i x)"
  by (simp add: assms ub_iterate_chain ubcldom_least_cs)

lemma iter_ufCompH_dom[simp]: assumes "ubclDom\<cdot>x = ufCompI f1 f2" 
  shows "ubclDom\<cdot>(iter_ufCompH f1 f2 i x) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
  by (simp add: assms iter_ubfix2_dom ubcldom_least_cs)

(*neu*)
lemma iter_ufcomph_commu: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
                           and "ubclDom\<cdot>tb = ufCompI f1 f2" 
                         shows "(iter_ufCompH f1 f2 i tb) = (iter_ufCompH f2 f1 i tb)"
proof (induction i)
  case 0
  then show ?case 
    by (simp add: Un_commute)
next
  case (Suc i)
  then show ?case 
    by (metis assms(1) assms(2) iter_ufCompH_dom iterate_Suc ufcomph_commu)
qed
    
    
subsubsection \<open>lub iterate ufCompH\<close> 

lemma lub_iter_ufCompH_dom[simp]: assumes "ubclDom\<cdot>x = ufCompI f1 f2" 
  shows "ubclDom\<cdot>(\<Squnion>i. iter_ufCompH f1 f2 i x) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
proof -
  have "ubfun_io_eq (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)"
    by (meson assms ubcldom_least_cs ufCompH_dom)
  then show ?thesis
    by (metis ubFix_def ubfix_dom)
qed

  
subsubsection \<open>General Comp\<close>

(* ufComp is a cont function *)
lemma ufcomp_cont[simp]: 
  shows "cont (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) )"
  apply (rule ubfix_contI2)
proof (simp_all)
  fix x:: "'a"
  assume x_ubclDom: "ubclDom\<cdot>x = ufCompI f1 f2"
  have f4: "ubclDom\<cdot>(x \<uplus> ubclLeast (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)\<bar>UFun.ufDom\<cdot>f1) = ufDom\<cdot>f1"
    apply (simp add: ubclunion_restrict ubclunion_dom ubclrestrict_dom)
    using ubcldom_least_cs ufCompI_def x_ubclDom by fastforce
  have f5: "ubclDom\<cdot>(x \<uplus> ubclLeast (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)\<bar>UFun.ufDom\<cdot>f2) = ufDom\<cdot>f2"
    apply (simp add: ubclunion_restrict ubclunion_dom ubclrestrict_dom)
    using ubcldom_least_cs ufCompI_def x_ubclDom by fastforce
  show " ubfun_io_eq (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)"
    apply (simp add: ufCompH_def)
    by (simp add: f4 f5 ubclunion_dom ufran_2_ubcldom2)
qed

(* helper lemma for  ufWell proof of ufComp *)
lemma ufcomp_well_h: assumes "ubclDom\<cdot>x = ufCompI f1 f2" 
    shows  "ubclDom\<cdot>(ubFix (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)) = ufCompO f1 f2"
  by (simp add: assms ubcldom_least_cs ubfix_dom ufCompO_def)

(* ufcomp produce a ufwell component*)
lemma ufcomp_well[simp]:  
  shows "ufWell (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
  apply (simp add: ufWell_def)
  apply (rule conjI)
   apply (rule_tac x = "ufCompI f1 f2" in exI)
   apply (simp add: domIff)
  apply (rule_tac x = "ufCompO f1 f2" in exI) 
  by (smt option.distinct(1) option.sel ran2exists ufcomp_well_h)

lemma ufcomp_repabs: 
  shows "Rep_cufun (ufComp f1 f2) = (\<lambda>a. (ubclDom\<cdot>a = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 a)(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
  by (simp add: ufComp_def)

lemma ufcomp_insert:
  assumes "ubclDom\<cdot>ub = ufCompI uf1 uf2"
  shows   "(uf1 \<otimes> uf2) \<rightleftharpoons> ub = ubFix (ufCompH uf1 uf2 ub) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)"
  by (simp add: assms ufcomp_repabs)

lemma ufcomp_dom:
  shows "ufDom\<cdot>(ufComp f1 f2) =  ufCompI f1 f2"
  apply (simp add: ufDom_def)
  apply (simp add: ufComp_def)
  apply (simp add: domIff)
  by (meson someI_ex ubcldom_ex)

lemma ubclDom_h: " ubclDom\<cdot>(SOME b::'a. ubclDom\<cdot>b = cs) = cs"
proof -
  obtain x::"'a" where x_def: "ubclDom\<cdot>x = cs" using ubcldom_ex by auto
  show ?thesis
    by (meson x_def someI_ex)
qed

lemma ufcomp_ran:
  shows "ufRan\<cdot>(ufComp f1 f2) = ufCompO f1 f2"
proof -
  obtain x where x_def: "x \<in> (ran (Rep_cufun (ufComp f1 f2)))"
    using ufran_not_empty by blast
  have f2: "ubclDom\<cdot>x = ufCompO f1 f2"
    by (metis (mono_tags, lifting) option.distinct(1) ran2exists ufcomp_well_h ufcomp_repabs ufran_2_ubcldom x_def)
  have f3: "ufRan\<cdot>(ufComp f1 f2) = ubclDom\<cdot>x"
    by (meson ran2exists ufran_2_ubcldom x_def)
  show ?thesis
    by (simp add: f2 f3)
qed


subsubsection\<open>Associativity\<close>

(*
lemma ufcomp_asso: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f3 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f3 = {}" 
  shows "ufComp (ufComp f1 f2) f3 = ufComp f1 (ufComp f2 f3)"
proof - 
  have f1: "(ufCompI (ufComp f1 f2) f3) = (ufCompI f1 (ufComp f2 f3))"
    apply(simp add: ufCompI_def)
    apply(simp add: ufcomp_ran ufcomp_dom assms)
    apply(simp add: ufCompI_def ufCompO_def)
    by auto
  have f2: "\<And>x. ubclDom\<cdot>x = (ufDom\<cdot>(ufComp f1 f2) \<union> ufDom\<cdot>f3 - (ufRan\<cdot>(ufComp f1 f2) \<union> ufRan\<cdot>f3)) \<Longrightarrow>
      ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>(ufComp f1 f2) \<union> ufRan\<cdot>f3) =
      ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3))"
  proof -  
    fix x :: "'a"
    assume f20: "ubclDom\<cdot>x = (ufDom\<cdot>(ufComp f1 f2) \<union> ufDom\<cdot>f3 - (ufRan\<cdot>(ufComp f1 f2) \<union> ufRan\<cdot>f3))"

    show "ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>(ufComp f1 f2) \<union> ufRan\<cdot>f3) =
          ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3))"
      apply(subst ufCompH_def, subst ufComp_def)
      apply(simp)                                                               
      apply(subst rep_abs_cufun)
        apply(simp_all add: assms)
      apply(subst (2) ufCompH_def, subst (4) ufComp_def)
      apply(simp)
      apply(subst rep_abs_cufun)
        apply (simp_all add: assms)


      sorry
  qed
  show ?thesis
    apply(subst (2) ufComp_def)
    apply(simp)
    apply(subst (4) ufComp_def)
    apply(simp add: f1)
    using f2 by (metis (no_types, hide_lams) f1 ufCompI_def)
qed
*)

subsection \<open>ufLeast\<close>
  

(* ufelast if a mono function  *)
lemma ufleast_mono[simp]: "\<And> cin cout. monofun (\<lambda>sb. (ubclDom\<cdot>sb = cin)\<leadsto>ubclLeast cout)"
  by simp

(* ufleast is a cont function *)
lemma ufleast_cont[simp]: "\<And> cin cout. cont (\<lambda>sb. (ubclDom\<cdot>sb = cin)\<leadsto>ubclLeast cout)"
  by simp

(* ufleast produce a ufwell function  *)
lemma ufleast_ufwell[simp]: "\<And> cin cout. ufWell (Abs_cfun (\<lambda>sb. (ubclDom\<cdot>sb = cin)\<leadsto>ubclLeast cout))"
  apply (simp add: ufWell_def, rule)
   apply (rule_tac x="cin" in exI, simp add: domIff)
  by (smt option.distinct(1) option.sel ran2exists ubcldom_least_cs)

(* insert rule of ufleast *)
lemma ufleast_insert:"ufLeast In Out = Abs_ufun (Abs_cfun (\<lambda>sb. (ubclDom\<cdot>sb = In)\<leadsto>ubclLeast Out))"
  by (simp add: ufLeast_def)

(* somwe how ufleast_ufran need this otherwise this cannt be proven with metis  *)
lemma ufleast_rep_abs[simp]: "(Rep_cufun (Abs_cufun (\<lambda>sb. (ubclDom\<cdot>sb = In)\<leadsto>ubclLeast Out))) = (\<lambda>sb. (ubclDom\<cdot>sb = In)\<leadsto>ubclLeast Out)"
  by simp

(* ufdom of ufleast is the first argument  *)
lemma ufleast_ufdom: "ufDom\<cdot>(ufLeast In Out) = In"
  apply (simp add: ufLeast_def  ufdom_insert domIff)
  by (meson someI_ex ubcldom_least_cs)

(* ufran of ufleast is its second argument *)
lemma ufleast_ufRan: "ufRan\<cdot>(ufLeast In Out) = Out"
  by (metis (no_types) option.sel ubcldom_least_cs ufleast_insert ufleast_rep_abs ufleast_ufdom ufran_least)

(* ufleast can produce a function smaller or equal other function  *)
lemma ufleast_min: "(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) \<sqsubseteq> uf"
proof (rule ufun_belowI)
  show "ufDom\<cdot>(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) = UFun.ufDom\<cdot>uf"
    by (simp add: ufleast_ufdom)
next
  show "\<And>x. ubclDom\<cdot>x = ufDom\<cdot>(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) \<Longrightarrow>
         Rep_cufun (ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf))\<rightharpoonup>x \<sqsubseteq> Rep_cufun uf\<rightharpoonup>x"
    by (metis ufleast_rep_abs option.sel ubcldom_least ufLeast_def ufleast_ufdom ufran_2_ubcldom2)
qed

lemma ufleast_apply:assumes "ubclDom\<cdot>sb = In" shows "ufLeast In  Out \<rightleftharpoons> sb = ubclLeast Out"
  by (simp add: assms ufLeast_def)
    

subsection \<open>ufRestrict\<close>


lemma ufLeast_bottom [simp]: assumes "ufDom\<cdot>f = In" and "ufRan\<cdot>f = Out" shows "(ufLeast In Out) \<sqsubseteq> f"
  using assms(1) assms(2) ufleast_min by blast

lemma ufLeast_dom [simp]: "ufDom\<cdot>(ufLeast In Out) = In"
  by (simp add: ufleast_ufdom)

lemma ufLeast_ran [simp]: "ufRan\<cdot>(ufLeast In Out) = Out"
  by (simp add: ufleast_ufRan)

lemma ufRestrict_mono: "monofun (\<lambda> f. if (ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out) then f else (ufLeast In Out))"
  by (simp add: monofun_def ufdom_below_eq ufran_below)

lemma ufRestrict_cont[simp]: "cont (\<lambda> f. if (ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out) then f else (ufLeast In Out))"
  by (smt
      Cont.contI2 lub_eq monofun_def po_eq_conv ufLeast_bottom ufLeast_dom ufLeast_ran ufdom_below_eq
      ufdom_lub_eq ufran_below ufran_lub_eq)

lemma ufRestrict_apply[simp]: assumes "ufDom\<cdot>f = In" and "ufRan\<cdot>f = Out" shows "ufRestrict In Out\<cdot>f = f"
  by (simp add: ufRestrict_def ufRestrict_cont assms)

lemma ufRestrict_dom[simp]: "ufDom\<cdot>(ufRestrict In Out\<cdot>f) = In"
proof (cases "ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out")
  case True
  then show ?thesis
    by (simp add: ufRestrict_apply)
next
  case False
  then show ?thesis
    by (simp add: ufRestrict_def ufleast_ufdom)
qed

lemma ufRestrict_ran[simp]: "ufRan\<cdot>(ufRestrict In Out\<cdot>f) = Out"
proof (cases "ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out")
  case True
  then show ?thesis
    by (simp add: ufRestrict_def ufleast_ufRan)
next
  case False
  then show ?thesis
    by (simp add: ufRestrict_def ufleast_ufRan)
qed




subsection \<open>ufLift\<close>
thm ufLift_def

lemma uflift_ran_h: 
  fixes b::"'m::ubcl_comp"
  shows "ubclDom\<cdot>(f\<cdot>b) = ubclDom\<cdot>(f\<cdot>(ubclLeast (ubclDom\<cdot>b)))"
proof - 
  have "ubclLeast (ubclDom\<cdot>b) \<sqsubseteq> b"
    using ubcldom_least by blast
  hence "f\<cdot>(ubclLeast (ubclDom\<cdot>b)) \<sqsubseteq> f\<cdot>b"
    by (simp add: cont2monofunE)
  thus ?thesis
    using ubcldom_fix by blast
qed

lemma uflift_ran_h_h: 
  fixes b::"'m::ubcl_comp"
  shows  "ubclDom\<cdot>b = ubclDom\<cdot>a  \<Longrightarrow>  ubclDom\<cdot>(f\<cdot>a) =  ubclDom\<cdot>(f\<cdot>b)"
  by (metis uflift_ran_h)

lemma uflift_well[simp]: "ufWell (Abs_cfun (\<lambda> (ub::'m). (ubclDom\<cdot>ub = In) \<leadsto> (f\<cdot>ub)))"
  apply (simp add: ufWell_def domIff2)
  apply rule
  apply blast
  by (smt option.distinct(1) option.sel ran2exists uflift_ran_h_h)

lemma uf_cont_abs: "(\<And>f. ufWell (g\<cdot>f)) \<Longrightarrow> cont (\<lambda>f. Abs_ufun (g\<cdot>f))"
  apply(rule contI2, rule monofunI)
  apply (simp add: below_ufun_def monofun_cfun_arg)
  by (smt below_lub below_ufun_def ch2ch_Rep_cfunR contlub_cfun_arg lub_below_iff po_class.chain_def rep_abs_cufun2)


lemma uflift_cont_h1:  "cont (\<lambda> g. \<Lambda> ub . ((ubclDom\<cdot>ub = In)\<leadsto>(g\<cdot>ub)))"
  oops
(*  apply(rule if_then_cont4)
  by (simp add: ubcldom_fix) *)  (* See OptionCPO for the proof-begin *)

lemma uflift_cont_h[simp]: "cont  (\<lambda> f. Abs_ufun ((\<Lambda> g. (\<Lambda>(ub::'m). (ubclDom\<cdot>ub = In) \<leadsto> g\<cdot>ub))\<cdot>f))"
  oops
(*  apply(rule uf_cont_abs)
  by (simp add: uflift_cont_h1) *)

lemma uflift_cont[simp]: "cont  (\<lambda> f. Abs_ufun (((\<Lambda>(ub::'m). (ubclDom\<cdot>ub = In) \<leadsto> f\<cdot>ub))))"
  oops

lemma uflift_insert: "ufLift In f = Abs_cufun (\<lambda> ub. (ubclDom\<cdot>ub = In) \<leadsto> f\<cdot>ub)"
  by(simp add: ufLift_def)

lemma uflift_dom[simp]: "ufDom\<cdot>(ufLift In f) = In"
  apply (simp add: uflift_insert)
  by (simp add: ufun_ufdom_abs)

lemma uflift_ran[simp]: "ufRan\<cdot>(ufLift In f) = ubclDom\<cdot>(f\<cdot>(ubclLeast In))"
  apply (simp add: uflift_insert ufran_insert)
  by (smt option.distinct(1) option.inject ran2exists ranI tfl_some ubcldom_least ubcldom_least_cs uflift_ran_h)

lemma uflift_apply[simp]: "ubclDom\<cdot>ub = In \<Longrightarrow> (ufLift In f) \<rightleftharpoons> ub = f\<cdot>ub"
  by(simp add: uflift_insert)


subsection\<open>More General Comp lemma\<close>


subsubsection\<open>Fixed point property\<close>


lemma ufcomp_fix_f1: assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<bar> ufRan\<cdot>uf1 = uf1 \<rightleftharpoons> ((sb \<uplus> ((uf1 \<otimes> uf2) \<rightleftharpoons> sb)) \<bar> ufDom\<cdot>uf1)"
proof - 
  have "ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2) = (ufCompH uf1 uf2 sb)\<cdot>(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))"
    apply(subst ubfix_eq)
    apply (simp add: assms(2) ubcldom_least_cs)
    by blast
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) = 
    (uf1 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf1)) \<uplus> 
    (uf2 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf2))"
    by (metis ufcomph_insert)
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) \<bar> ufRan\<cdot>uf1 = (uf1 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))) \<bar> ufDom\<cdot>uf1))"
    using ubclunion_restrict2 ufcomph_insert
    by (smt Un_Diff_cancel assms(1) assms(2) comp_well_def inf_sup_aci(1) subset_Un_eq sup_commute sup_left_commute sup_left_idem ubclunion_restrict3 ubclunion_ubcldom ufCompI_def ufCompO_def ufRanRestrict ufcomp_well_h)
  then show ?thesis
    by (simp add: assms(2) ufcomp_repabs)
qed

lemma ufcomp_fix_f2: assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<bar> ufRan\<cdot>uf2 = uf2 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf2)"
proof - 
  have "ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2) = (ufCompH uf1 uf2 sb)\<cdot>(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))"
    apply(subst ubfix_eq)
    apply (simp add: assms(2) ubcldom_least_cs)
    by blast
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) = 
    (uf1 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf1)) \<uplus> 
    (uf2 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf2))"
    by (metis ufcomph_insert)
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) \<bar> ufRan\<cdot>uf2 = (uf2 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))) \<bar> ufDom\<cdot>uf2))"
    using ubclunion_restrict2 ufcomph_insert
    by (smt Un_Diff_cancel assms(1) assms(2) comp_well_def inf_sup_aci(1) subset_Un_eq sup_commute sup_left_commute sup_left_idem ubclunion_restrict3 ubclunion_ubcldom ufCompI_def ufCompO_def ufRanRestrict ufcomp_well_h)
  then show ?thesis
    by (metis assms(1) assms(2) comp_well_def ubclunion_commu ufcomp_I_inter_Oc_empty ufcomp_insert ufcomp_well_h)

qed

lemma ufcomp_fix: assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "(uf1 \<otimes> uf2) \<rightleftharpoons> sb = (uf1 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf1)) \<uplus> (uf2 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf2))"
  by (metis (no_types, lifting) assms(1) assms(2) comp_well_def ubclunion_commu ubclunion_ubclrestrict_id ufCompO_def ufcomp_I_inter_Oc_empty ufcomp_dom ufcomp_fix_f1 ufcomp_fix_f2 ufcomp_ran ufran_2_ubcldom2) 



(*neu*\<down>*)
lemma ufcomp2_lubiter: "ufComp f1 f2 = 
  Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) 
      \<leadsto> (\<Squnion>i. iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"
  apply (subst ufComp_def, subst ubFix_def)
  by (simp)
    
lemma ufcomp2_iterCompH: "ufComp f1 f2 = 
  Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) 
      \<leadsto> (\<Squnion>i. iter_ufCompH f1 f2 i x))"
  by (simp add: ufcomp2_lubiter)

lemma ufcomp_commu: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufComp f1 f2 = ufComp f2 f1"
proof -
  have f0: "\<And> ub. ubclDom\<cdot>ub = ufCompI f1 f2 \<Longrightarrow> 
                  (\<Squnion> i. iter_ufCompH f1 f2 i ub) = (\<Squnion> i. iter_ufCompH f2 f1 i ub)"
    by (meson assms iter_ufcomph_commu)
  have f1: "ufCompI f1 f2 = ufCompI f2 f1"
    by (simp add: ufcomp_I_commu)
  have f2: "\<forall> ub. (ubclDom\<cdot>ub \<noteq> ufCompI f1 f2) 
            \<or> (Some (\<Squnion> i. iter_ufCompH f1 f2 i ub) = Some (\<Squnion> i. iter_ufCompH f2 f1 i ub)) "
    using f0 by blast
  have f3:"Abs_cufun (\<lambda>t. (ubclDom\<cdot>t = ufCompI f2 f1)
                              \<leadsto>\<Squnion>n. iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) t) 
        = Abs_cufun (\<lambda>t. (ubclDom\<cdot>t = ufCompI f2 f1)
                              \<leadsto>\<Squnion>n. iter_ubfix2 (ufCompH f2 f1) n (ufRan\<cdot>f2 \<union> ufRan\<cdot>f1) t) 
          \<or> (\<forall>t. ubclDom\<cdot>t \<noteq> ufCompI f2 f1 \<or> (ubclDom\<cdot>t \<noteq> ufCompI f2 f1 \<or> 
          Some (\<Squnion>n. iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) t) 
          = Some (\<Squnion>n. iter_ubfix2 (ufCompH f2 f1) n (ufRan\<cdot>f2 \<union> ufRan\<cdot>f1) t)) 
          \<and> (ubclDom\<cdot>t = ufCompI f2 f1 \<or> 
            None = Some (\<Squnion>n. iter_ubfix2 (ufCompH f2 f1) n (ufRan\<cdot>f2 \<union> ufRan\<cdot>f1) t))) 
            \<and> (\<forall>t. ubclDom\<cdot>t = ufCompI f2 f1 \<or> ubclDom\<cdot>t \<noteq> ufCompI f2 f1 
            \<or> Some (\<Squnion>n. iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) t) = None)"
        using f2 ufcomp_I_commu by blast  
    show ?thesis
     apply (subst (1 2) ufcomp2_iterCompH)  
     apply (subst f1)
     using f3 by meson
 qed

definition ufCompI_3arg :: "('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> ('in,'out) ufun \<Rightarrow> channel set" where
"ufCompI_3arg f1 f2 f3 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"


definition ufCompH_3arg :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> 'm \<Rightarrow> ('m \<rightarrow> 'm)" where
"ufCompH_3arg f1 f2 f3 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)) \<uplus>  (f3\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f3)))"

abbreviation iter_ufCompH_3arg :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> nat \<Rightarrow> 'm  \<Rightarrow> 'm" where
"(iter_ufCompH_3arg f1 f2 f3 i) \<equiv> (\<lambda> x. iterate i\<cdot>(ufCompH_3arg f1 f2 f3 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))" 

lemma ufCompH_3arg_cont2: "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)) \<uplus>  (f3\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f3)))"
proof -
  have "cont (\<lambda>a. f3 \<rightleftharpoons> a \<uplus> z\<bar>ufDom\<cdot>f3) \<and> cont (\<lambda>a. ubclUnion\<cdot> ((f1 \<rightleftharpoons> a \<uplus> z\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> a \<uplus> z\<bar>ufDom\<cdot>f2)))"
    using cont_compose by force
  then show ?thesis
    using cont2cont_APP by blast
qed

lemma ufFeedH_cont1: "cont (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"
  using cont_compose by force  

lemma ufCompH_3arg_cont1: "cont (\<lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)) \<uplus>  (f3\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f3)))"
  by (simp add: ufFeedH_cont1)


lemma ufCompH_3arg_continX: "cont (\<lambda> x. ufCompH_3arg f1 f2 f3 x)"
proof -
  have "cont (\<lambda> x. \<Lambda> z. ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2)) \<uplus>  (f3\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f3))))"
    apply (rule cont2cont_LAM)
     apply (simp add: ufCompH_3arg_cont1)
    using ufCompH_3arg_cont2 by blast
  thus ?thesis
    by (simp add: ufCompH_3arg_def)
qed

lemma ufCompH_3arg_io_eq: assumes "ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3"
  shows "ubfun_io_eq (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
proof -
  have f1: "ubclDom\<cdot>(f1 \<rightleftharpoons> x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1) = ufRan\<cdot>f1"
    by (simp add: assms sup.left_commute sup_commute ubcldom_least_cs ubclunion_ubcldom ufCompI_3arg_def)
  have f2: "ubclDom\<cdot>(f2 \<rightleftharpoons> x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2) = ufRan\<cdot>f2"
    by (simp add: assms le_iff_sup sup_commute sup_left_commute ubcldom_least_cs ubclunion_ubcldom ufCompI_3arg_def)
  have f3: "ubclDom\<cdot>(f3 \<rightleftharpoons> x \<uplus> ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3) = ufRan\<cdot>f3"
    by (simp add: assms sup_assoc sup_commute ubcldom_least_cs ubclunion_ubcldom ufCompI_3arg_def)
  show ?thesis
    apply (simp add: ufCompH_3arg_def)
    apply (simp add: ufCompH_3arg_cont1)
    apply (simp add: ubclunion_dom)
    using f1 f2 f3 by blast
qed

lemma iter_comph_3arg_cont: "cont (\<lambda> x. iterate i\<cdot>(ufCompH_3arg f1 f2 f3 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))"
  by (simp add: ufCompH_3arg_continX)

lemma iter_comph_3arg_mono: "monofun (\<lambda> x. iterate i\<cdot>(ufCompH_3arg f1 f2 f3 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))"
  by (simp add: iter_ubfix2_mono_pre monofunI ufCompH_3arg_continX)

    
lemma iter_comph_3arg_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. (iterate i\<cdot>(ufCompH_3arg f1 f2 f3 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))) 
  \<sqsubseteq> (iterate i\<cdot>(ufCompH_3arg f1 f2 f3 y)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))"
  by (simp add: assms iter_ubfix2_mono_pre ufCompH_3arg_continX)


lemma iter_comph_3arg_chain[simp]: assumes "ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3"
  shows "chain (\<lambda> i. iterate i\<cdot>(ufCompH_3arg f1 f2 f3 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))"
  by (simp add: assms ub_iterate_chain ufCompH_3arg_io_eq)

lemma lub_iter_comph_3arg_dom[simp]:assumes "ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3"
  shows "ubclDom\<cdot>(\<Squnion>i. iterate i\<cdot>(ufCompH_3arg f1 f2 f3 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))) 
    = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2  \<union> ufRan\<cdot>f3)"
  by (metis assms lub_iter_ubfix2_dom ufCompH_3arg_io_eq)



subsubsection \<open>ufComp3\<close>

definition ufComp3 :: "('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun \<Rightarrow> ('m,'m) ufun" where
"ufComp3 f1 f2 f3\<equiv>
let I = ufCompI_3arg f1 f2 f3;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)
in Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = I) \<leadsto> ubFix (ufCompH_3arg f1 f2 f3 x) Oc))" 

lemma ufcomp3_cont[simp]: "cont (\<lambda>x::'a. (ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3)\<leadsto>ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))"
  apply (rule ubfix_contI2, simp_all)
   apply (simp add: ufCompH_3arg_continX)
  by (simp add: ufCompH_3arg_io_eq)

lemma ufcomp3_well_h: assumes"ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3"
shows  "ubclDom\<cdot>(ubFix (ufCompH_3arg f1 f2 f3 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2 \<union> UFun.ufRan\<cdot>f3)) 
  = UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2 \<union> UFun.ufRan\<cdot>f3"
  by (simp add: assms ubfix_dom ufCompH_3arg_io_eq)

lemma ufcomp3_well[simp]:
  shows "ufWell (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3) \<leadsto> 
                              ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))"
  apply (rule ufun_wellI)
    apply (simp_all add: ufcomp3_cont)
    apply (simp_all add: domIff2)
  by (simp add: ubfix_dom ufCompH_3arg_io_eq)

(*
lemma Un_Diff0: "A - C \<union> B - C = (A \<union> B) - C"
  by (simp add: Un_Diff)
lemma bla1: "A - B - C = A - (B \<union> C)"
  by (simp add: Diff_eq inf_assoc)
lemma Int_Diff: "(A - B) \<inter> C = (A \<inter> C) - B"
  by auto
*)

lemma ufcomp_asso: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and  "ufRan\<cdot>f2 \<inter> ufRan\<cdot>f3 = {}" 
and  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f3 = {}"
shows "ufComp (ufComp f1 f2) f3 = ufComp f1 (ufComp f2 f3)"
proof -
  have f0: "ufRan\<cdot>(ufComp f1 f2) \<inter> ufRan\<cdot>f3 = {}"
    apply (simp add: assms(1) ufcomp_ran)
    unfolding ufCompO_def
    by (simp add: assms(2) assms(3) inf_sup_distrib2)
  have f1: "ufRan\<cdot>f1 \<inter> ufRan\<cdot>(ufComp f2 f3) = {}"
    apply (simp add: assms(2) ufcomp_ran)
    unfolding ufCompO_def
    by (simp add: assms(1) assms(3) inf_sup_distrib1)
  have f10: " ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<union> (ufDom\<cdot>f3 - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) = 
       (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
    by (simp add: Un_Diff)
  have f11: "ufDom\<cdot>(ufComp (ufComp f1 f2) f3) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
    apply (simp add: f0 ufcomp_dom)
    unfolding ufCompI_def
    apply (simp add: ufcomp_ran ufcomp_dom assms(1))
    unfolding ufCompO_def
    apply (subst ufCompI_def)
    by blast
  have f12: "ufDom\<cdot>(ufComp f1 (ufComp f2 f3)) = (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
    apply (simp add: f1 ufcomp_dom)
    unfolding ufCompI_def
    apply (simp add: ufcomp_ran ufcomp_dom assms(2))
    unfolding ufCompO_def
    apply (subst Un_Diff)
    unfolding ufCompI_def
    by blast
  have f2: "ufDom\<cdot>(ufComp (ufComp f1 f2) f3) = ufDom\<cdot>(ufComp f1 (ufComp f2 f3))"
    by (simp add: f11 f12)
  have f20: "ufDom\<cdot>(ufComp (ufComp f1 f2) f3) = ufCompI_3arg f1 f2 f3"
    by (simp add: f11 ufCompI_3arg_def)
  have f21: "ufDom\<cdot>(ufComp3 f1 f2 f3) = ufCompI_3arg f1 f2 f3"
    apply (simp add: ufComp3_def)
    by (simp add: ufcomp3_cont ufcomp3_well ufun_ufdom_abs)
  have  f100: "ufComp f1 (ufComp f2 f3) = ufComp3 f1 f2 f3"
    apply (rule ufun_eqI)
    using f2 f20 f21 apply blast
  proof -
    fix x::'a
    assume a1: " ubclDom\<cdot>x = ufDom\<cdot>(ufComp f1 (ufComp f2 f3)) "
    have f100: "ubclDom\<cdot>x = ufCompI f1 (ufComp f2 f3)"
      by (simp add: a1 f1 ufcomp_dom)
    have f101: "ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3"
      using a1 f2 f20 by blast
    have f102: "ufComp f2 f3 = (Abs_cufun (\<lambda>x::'a. (ubclDom\<cdot>x = ufCompI f2 f3)\<leadsto>ubFix (ufCompH f2 f3 x) (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)))"
      by (simp add: ufComp_def)

    have f105: "ubclDom\<cdot>(x \<uplus> ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3))\<bar>ufDom\<cdot>(ufComp f2 f3)) = ufCompI f2 f3"
      by (smt Un_Diff_cancel Un_commute a1 assms(2) f1 sup.orderI sup.right_idem sup_assoc 
            ubclunion_ubcldom ubrestrict_dom2 ufCompI_def ufCompO_def ufcomp_dom ufcomp_well_h)
    
    have f150: "ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) = 
    (\<Squnion>i. iterate i\<cdot>(ufCompH f1 (ufComp f2 f3) x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3))))"
      by (simp add: ubFix_def)
    have  f152: "ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) = 
    (\<Squnion>i. iterate (i+1)\<cdot>(ufCompH f1 (ufComp f2 f3) x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3))))"
      apply (simp add: ubFix_def del: iterate_Suc)
      apply (subst lub_range_shift [of _ 1, symmetric])
       apply (simp add: f100)
      by auto
    obtain chain1 where chain1_def: "chain1 = (\<lambda>i. iter_ubfix2 (ufCompH f1 (ufComp f2 f3)) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) x)"
      by simp
    obtain chain2::"nat \<Rightarrow> (nat \<Rightarrow> 'a)"  where chain2_def: "chain2 = (\<lambda> i ia. iter_ubfix2 (ufCompH f2 f3) ia (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) (x \<uplus> chain1 i\<bar>ufCompI f2 f3))"
      by simp
    have chain1_is_chain: "chain chain1"
      apply (simp add: chain1_def)
      by (simp add: f100)
    have chain1_insert: "\<And>i. chain1 i = iter_ubfix2 (ufCompH f1 (ufComp f2 f3)) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) x"
      by (simp add: chain1_def)
    have chain2_insert: "\<And>i ia. chain2 i ia = iter_ubfix2 (ufCompH f2 f3) ia (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) (x \<uplus> chain1 i\<bar>ufCompI f2 f3)"
      by (simp add: chain2_def)
    have f140: "\<And>ia. ubclDom\<cdot>((x \<uplus> (chain1 ia))\<bar>ufCompI f2 f3) = ufCompI f2 f3"
      by (metis assms(2) chain1_def f1 f100 f105 iter_ufCompH_dom ubclrestrict_ubcldom ubclunion_ubcldom ufCompO_def ufcomp_dom ufcomp_well_h)
    have f141: " ubclDom\<cdot>((x \<uplus> Lub chain1)\<bar>ufCompI f2 f3) = ufCompI f2 f3"
      by (metis (no_types, lifting) assms(2) chain1_def f105 f150 image_cong ufcomp_dom)
    have chain2_is_chain: "\<And>i. chain (chain2 i)"
      apply (simp add: chain2_def)
      by (simp add: f140)
    have chain2_is_chain2: "\<And>j. chain (\<lambda>i. chain2 i j)"
      apply (simp add: chain2_def)
      apply (rule chainI)
      by (simp add: chain1_is_chain iter_ufCompH_mono2 monofun_cfun_arg po_class.chainE)
    have chain2_is_chain3: "chain (\<lambda>i. chain2 i i)"
      apply (rule chainI)
      by (metis chain2_is_chain chain2_is_chain2 po_class.chainE rev_below_trans)
    have chain1_chain2_union: "(\<Squnion>i::nat. chain1 i) \<uplus>  (\<Squnion>i::nat. chain2 i i) = (\<Squnion>i::nat. chain1 i \<uplus> chain2 i i)"
      apply (rule ubclunion_lub_sep)
       apply (simp add: chain1_is_chain)
      apply (rule chainI)
      by (metis chain2_is_chain chain2_is_chain2 po_class.chainE rev_below_trans)
    have compf1f2f3_lub_alt: "ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) = (\<Squnion>i. chain1 i \<uplus> chain2 i i)"
      apply (simp add: ubFix_def)
      apply (fold chain1_def)
      apply (subst lub_range_shift [of _ 1, symmetric])
       apply (simp add: chain1_is_chain)
      apply (subst chain1_def)
      apply simp
      apply (subst ufCompH_def)
      apply simp
      apply (fold chain1_insert)
      apply (simp add: assms(2) ufcomp_dom)
      apply (simp add: ufComp_def)
      apply (simp add: assms(2) f140)
      unfolding ubFix_def
      apply (fold chain2_insert) 
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain1_is_chain op_the_chain)
      apply (simp add: ch2ch_lub chain2_is_chain chain2_is_chain2)
      apply (subst diag_lub)
        apply (simp add: chain1_is_chain chain2_is_chain2 op_the_chain)
       apply (simp add: chain2_is_chain)
      apply (rule sym)
      apply (fold chain1_chain2_union)
      apply (subst lub_range_shift [of _ 1, symmetric])
       apply (simp add: chain1_is_chain)
      apply (subst chain1_def)
      apply simp
      apply (subst ufCompH_def)
      apply (simp)
      apply (fold chain1_insert)
      apply (simp add: assms(2) ufcomp_dom)
      apply (simp add: ufComp_def)
      apply (simp add: assms(2) f140)
      unfolding ubFix_def
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain1_is_chain op_the_chain)
       apply (fold chain2_insert)
       apply (rule chainI)
      using ch2ch_lub chain2_is_chain chain2_is_chain2 po_class.chainE apply blast
      apply (subst diag_lub)
        apply (simp add: chain2_is_chain2 chain2_is_chain) +
      by (simp add: ubclunion_id ubclunion_asso)
    have x_chain_id: "x = (\<Squnion>i::nat. x)"
      by simp
    have chain_f1_apply: "chain (\<lambda>n. f1 \<rightleftharpoons> x \<uplus> chain1 n\<bar>ufDom\<cdot>f1)"
      by (simp add: chain1_is_chain op_the_chain)
    have chain_comph_f2f3: "chain (\<lambda>n. ufCompH f2 f3 (x \<uplus> chain1 n\<bar>ufCompI f2 f3))"
      by (metis ch2ch_cont chain1_is_chain cont_Rep_cfun2 ufCompH_continX)
    have f96: "\<And>i. chain (\<lambda>ia::nat. chain2 i (ia + 1))"
      apply (simp only: chain2_def)
      using chain2_def chain2_is_chain by auto
    have chain2_lub_shift: "\<And>i::nat. (\<Squnion>ia::nat. chain2 i (ia + (1::nat))) = Lub (chain2 i)"
      apply (subst po_eq_conv) apply rule defer
       apply (rule lub_mono)
         apply (simp add: chain2_is_chain)
      using f96 apply auto[1]
       apply (simp add: chain2_is_chain chain_mono_less)
      by (metis below_refl chain2_is_chain lub_range_shift2)
    have f299: "\<And>i. ubclDom\<cdot>(x \<uplus> chain1 i \<uplus> chain2 i i\<bar>ufDom\<cdot>f2) = ufDom\<cdot>f2"
      apply (simp add: ubclunion_restrict)
      apply (simp add: ubclunion_ubcldom)
      apply (simp add: ubclrestrict_dom)
      using a1 chain1_def chain2_insert f100 f11 f140 f2 by auto
    have f300: "(ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<inter> ufDom\<cdot>f2  = ufDom\<cdot>f2"
      by (simp add: inf_sup_aci(1))
    have f301: "ufDom\<cdot>f3 \<inter> (ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) = ufDom\<cdot>f3"
      by blast
    have f302: "\<And>i. (x \<uplus> chain1 i\<bar>ufCompI f2 f3) \<uplus> chain2 i i\<bar>ufDom\<cdot>f2  = (x \<uplus> chain1 i) \<uplus> chain2 i i\<bar>ufDom\<cdot>f2"
      apply (subst ufCompI_def)
      apply (subst ubclunion_ubclrestrict_minus)
       apply (simp add: chain2_def f140)
      by (simp add: f300 ubclrestrict_twice ubclunion_ubclrestrict)
    have f303: "\<And>i. (x \<uplus> chain1 i\<bar>ufCompI f2 f3) \<uplus> chain2 i i\<bar>ufDom\<cdot>f3 = (x \<uplus> chain1 i) \<uplus> chain2 i i\<bar>ufDom\<cdot>f3"
      apply (subst ufCompI_def)
      apply (subst ubclunion_ubclrestrict_minus)
       apply (simp add: chain2_def f140)
      by (simp add: f301 inf_commute ubclrestrict_twice ubclunion_ubclrestrict)
    have f304: "f2 \<rightleftharpoons> x \<uplus>  (\<Squnion>i. chain1 i \<uplus> chain2 i i)\<bar>ufDom\<cdot>f2 = (\<Squnion>i::nat. f2 \<rightleftharpoons> x \<uplus> chain1 i \<uplus> chain2 i i\<bar>ufDom\<cdot>f2)"
        apply (subst contlub_cfun_arg)
         apply (simp add: chain1_is_chain chain2_is_chain3)
        apply (subst contlub_cfun_arg)
       apply (simp add: chain1_is_chain chain2_is_chain3)
      apply (subst ufunlub_ufun_fun)
       apply (simp add: chain1_is_chain chain2_is_chain3)
      by (simp add: ubclunion_asso)
    have f305: "f3 \<rightleftharpoons> x \<uplus>  (\<Squnion>i. chain1 i \<uplus> chain2 i i)\<bar>ufDom\<cdot>f3 = (\<Squnion>i::nat. f3 \<rightleftharpoons> x \<uplus> chain1 i \<uplus> chain2 i i\<bar>ufDom\<cdot>f3)"
        apply (subst contlub_cfun_arg)
         apply (simp add: chain1_is_chain chain2_is_chain3)
        apply (subst contlub_cfun_arg)
       apply (simp add: chain1_is_chain chain2_is_chain3)
      apply (subst ufunlub_ufun_fun)
       apply (simp add: chain1_is_chain chain2_is_chain3)
      by (simp add: ubclunion_asso)
    have f306: " ( f1 \<rightleftharpoons> x \<uplus> Lub chain1 \<bar>ufDom\<cdot>f1) =  (\<Squnion>i::nat. f1 \<rightleftharpoons> x \<uplus> chain1 i\<bar>ufDom\<cdot>f1)"
      apply (subst contlub_cfun_arg)
       apply (simp add: chain1_is_chain)
      apply (subst contlub_cfun_arg)
       apply (simp add: chain1_is_chain)
      apply (subst ufunlub_ufun_fun)
       apply (simp add: chain1_is_chain)
      by simp
    have f307: "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<inter> ufDom\<cdot>f2 = ufDom\<cdot>f2"
        by (meson Int_absorb1 Un_upper1 le_supE)
    have f308: "ubclDom\<cdot> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3"
        by (meson f101 ufcomp3_well_h)
    have f207: "(\<Squnion>(i::nat) ia::nat. chain2 i ia) = (\<Squnion>i. chain2 i i)"
      apply (rule diag_lub)
       apply (simp add: chain2_is_chain2)
      by (simp add: chain2_is_chain)
    have  f151: "ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) = (f1 \<rightleftharpoons> x \<uplus> Lub chain1\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x \<uplus> Lub chain1\<bar>ufDom\<cdot>f2) \<uplus> (f3 \<rightleftharpoons> x \<uplus> Lub chain1\<bar>ufDom\<cdot>f3)"
      apply (simp add: ubFix_def)
      apply (subst lub_range_shift [of _ 1, symmetric])
       apply (simp add: f100)
      apply simp
      apply (fold chain1_insert)
      apply (subst ufCompH_def)
      apply simp
      apply (simp add: assms(2) ufcomp_dom)
      apply (simp add: ufComp_def)
      apply (simp add: assms(2) f140)
      apply (simp add: ubFix_def)
      apply (fold chain2_insert)
      apply (fold chain2_lub_shift)
      apply (simp add: chain2_insert)
      apply (fold chain2_insert)
      apply (subst contlub_cfun_arg)
       apply (simp add: chain2_is_chain)
      apply (subst diag_lub)
      apply (simp add: chain2_is_chain2 chain_comph_f2f3 chain_f1_apply)
       apply (simp add: chain2_is_chain)
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain_f1_apply)
       apply (simp add: chain2_is_chain3 chain_comph_f2f3)
      apply (subst ufCompH_def)
      apply simp
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain1_is_chain chain2_is_chain3 op_the_chain) +
      apply (simp add: f302 f303)
      apply (fold f304)
      apply (fold f305)
      apply (fold compf1f2f3_lub_alt)
      apply (simp add: ubFix_def)
      apply (fold chain1_insert)
      apply (fold f306)
      by (simp add: ubclunion_asso)
    have f210: "ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<sqsubseteq> ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3))"
      apply (rule ubfix_least_below)
        apply (simp add: f101 ufCompH_3arg_io_eq)
      apply (metis (mono_tags, lifting) assms(2) f1 f100 sup_assoc ufCompO_def ufcomp_ran ufcomp_well_h)
      apply (simp add: ufCompH_3arg_def ufCompH_3arg_cont1)
      using chain1_def f150 f151 by auto
    have f399: "ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) =
((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))\<bar>ufRan\<cdot>f1)  \<uplus>  
((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (rule sym)
      apply (rule ubclunion_ubclrestrict_id)
       apply (metis (no_types, hide_lams) f101 sup_assoc ufcomp3_well_h)
      by (simp add: assms(1) assms(3) inf_sup_distrib1)
    have f400: "ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) = 
    (f1 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<bar>ufDom\<cdot>f1) \<uplus>
    (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (subst f399)
      apply (subst ubfix_eq)
       apply (simp add: f101 ufCompH_3arg_io_eq)
      apply (subst ufCompH_3arg_def)
      apply (simp add: ufCompH_3arg_cont1)
      apply (subst ubclunion_restrict_R)
       apply (metis Un_Diff_cancel2 a1 assms(3) f101 f12 inf_sup_aci(1) 
          le_supI1 sup_ge2 ubclunion_ubcldom ufRanRestrict ufcomp3_well_h)
      apply (subst ubclunion_restrict_R)
       apply (subst ufran_2_ubcldom2)
        apply (simp add: ubclunion_ubclrestrict)
        apply (simp add: ubclunion_ubcldom)
        apply (simp add: ubclrestrict_dom)
      using a1 f12 f308 apply auto[1]
      apply (simp add: assms(1) inf_sup_aci(1))
      apply (subst ubclrestrict_dom_idI)
       apply (simp add: a1 f12 f308 le_supI1 ubclunion_ubcldom)
      by simp
    have f418: "ubclDom\<cdot>(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f2 f3) = ufCompI f2 f3"
    proof -
      have f1: "ubclDom\<cdot> (x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) = ubclDom\<cdot>(Lub ((\<lambda>n. x)::nat \<Rightarrow> 'a)) \<union> ubclDom\<cdot> ((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f1) \<uplus> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))"
        using f399 ubclunion_ubcldom by auto
      have "(ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f1) \<uplus> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot> f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<sqsubseteq> (\<Squnion>n. iter_ubfix2 (ufCompH f1 (ufComp f2 f3)) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) x)"
        using f150 f210 f399 by presburger
      then have "ubclDom\<cdot> (x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) = ubclDom\<cdot>(Lub ((\<lambda>n. x)::nat \<Rightarrow> 'a)) \<union> ubclDom\<cdot> (\<Squnion>n. iter_ubfix2 (ufCompH f1 (ufComp f2 f3)) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) x)"
        using f1 ubcldom_fix by blast
      then have "ubclDom\<cdot> (x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) = ubclDom\<cdot> (x \<uplus> ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)))"
        using f150 ubclunion_ubcldom by auto
      then show ?thesis
        using f105 ubclrestrict_ubcldom by blast
    qed
    have f417: "(ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<inter> ufDom\<cdot>f2 = ufDom\<cdot>f2  \<inter> (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      by blast
    have int_compi_f2_f3_f2: "(ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) \<inter> ufDom\<cdot>f2 = ((ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<inter> ufDom\<cdot>f2)  - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      by (simp add: Diff_Int2 Diff_Int_distrib2)
    have int_compi_f2_f3_f3: "(ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) \<inter> ufDom\<cdot>f3 = ((ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<inter> ufDom\<cdot>f3)  - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      by (simp add: Diff_Int2 Diff_Int_distrib2)
    have f416: "(((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))\<bar>ufDom\<cdot>f2) \<uplus> ((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2))
 = ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2"
      apply (simp add: ubclrestrict_twice)
      apply (simp add: f417)
      apply (simp add: int_compi_f2_f3_f2)
      apply (simp add: f300)
      by (simp add: ubclunion_ubclrestrict_minus_id)
    have f419: "(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f2 f3) \<uplus> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2
= (x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2)"
      apply (simp add: ufCompI_def)
      apply (simp add: ubclunion_ubclrestrict)
      apply (simp add: ubclunion_asso)
      apply (simp add: f416)
      apply (fold ubclunion_ubclrestrict)
      apply (subst ubclunion_ubclrestrict_minus)
      using f308 apply blast
      by (simp add: f300 ubclrestrict_twice ubclunion_ubclrestrict)
    have f412: "(ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<inter> ufDom\<cdot>f3 = ufDom\<cdot>f3 \<inter> (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      by blast
    have f411: "(ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<inter> ufDom\<cdot>f3 = ufDom\<cdot>f3"
      by blast
    have f413: "(((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2 \<union> ufDom\<cdot>f3 - (ufRan\<cdot>f2 \<union> ufRan\<cdot>f3))\<bar>ufDom\<cdot>f3) \<uplus> ((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3))
= ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3"
      apply (simp add: ubclrestrict_twice)
      apply (simp add: f412)
      apply (simp add: int_compi_f2_f3_f3)
      apply (simp add: f411)
      by (simp add: ubclunion_ubclrestrict_minus_id)
    have f415: "(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f2 f3) \<uplus> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3
= (x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3)"
      apply (simp add: ufCompI_def)
      apply (simp add: ubclunion_ubclrestrict)
      apply (simp add: ubclunion_asso)
      apply (simp add: f413)
      apply (fold ubclunion_ubclrestrict)
      apply (subst ubclunion_ubclrestrict_minus)
      using f308 apply blast
      by (simp add: f301 inf_sup_aci(1) ubclrestrict_twice ubclunion_ubclrestrict)
    have f410: "ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3 = (f2 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2) \<uplus> (f3 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3)"
      apply (subst ubfix_eq)
       apply (simp add: f101 ufCompH_3arg_io_eq)
      apply (subst ufCompH_3arg_def)
      apply (simp add: ufCompH_3arg_cont1)
      apply (subst ubclunion_asso)
      apply (subst ubclunion_ubclrestrict_RI) defer
       apply (rule ubclrestrict_dom_idI)
       apply (simp_all add: ubclunion_dom)
       apply (subst ufran_2_ubcldom2) defer
        apply (subst ufran_2_ubcldom2) defer
      apply blast
       apply (subst ufran_2_ubcldom2) defer
        apply (subst ufran_2_ubcldom2) defer
        apply blast
       apply (simp_all add: ubclunion_ubclrestrict)
       apply (simp_all add: ubclunion_dom)
       apply (simp_all add: ubclrestrict_dom)
      using a1 f12 f308 by auto
    have f420: "(ufComp f2 f3 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>(ufComp f2 f3))
 \<sqsubseteq>  (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (simp add: assms(2) ufcomp_dom)
      apply (simp add: ufComp_def)
      apply (simp add: assms(2) f418)
      apply (rule ubfix_least_below)
        apply (simp add: f418 ubcldom_least_cs)
       apply (metis (mono_tags, lifting) Un_assoc Un_def f308 f399 inf_sup_aci(6) sup.assoc sup.cobounded2 sup_assoc ubrestrict_dom2)
      apply (subst ufCompH_def)
      apply simp
      apply (simp add: f419 f415)
      by (simp add: f410)
    have f450: "(f1 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1) \<uplus> (ufComp f2 f3 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>(ufComp f2 f3)) \<sqsubseteq>
    (f1 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<bar>ufDom\<cdot>f1) \<uplus>
    (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<bar>ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      using f420 monofun_cfun_arg by blast
    have f300: "ubFix (ufCompH f1 (ufComp f2 f3) x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>(ufComp f2 f3)) \<sqsubseteq> 
                    ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (rule ubfix_least_below)
        apply (simp add: f100 ubcldom_least_cs)
       apply (metis (no_types, hide_lams) assms(2) f101 sup_assoc ufCompO_def ufcomp3_well_h ufcomp_ran)
      apply (subst ufCompH_def)
      apply simp
      using f400 f450 by auto
    show "ufComp f1 (ufComp f2 f3) \<rightleftharpoons> x = ufComp3 f1 f2 f3 \<rightleftharpoons> x"
      apply (simp add: ufComp_def)
      apply (fold f102)
      apply (simp add: f100 f1)
      apply (simp add: ufComp3_def f101)
      using f300 f210 po_eq_conv by blast
  qed

  have  f200: "ufComp (ufComp f1 f2) f3 = ufComp3 f1 f2 f3"
    apply (rule ufun_eqI)
    using f20 f21 apply blast
  proof - 
    fix x::'a
    assume a1: "ubclDom\<cdot>x = ufDom\<cdot>(ufComp (ufComp f1 f2) f3)"
    have x_dom1: "ubclDom\<cdot>x = ufCompI (ufComp f1 f2) f3"
      by (simp add: a1 f0 ufcomp_dom)
    have x_dom2: "ubclDom\<cdot>x = ufCompI_3arg f1 f2 f3"
      by (simp add: a1 f20)
    have compf1f2_insert: "ufComp f1 f2 = Abs_cufun (\<lambda>x::'a. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
      by (simp add: ufComp_def)
    have comp3arg_fix_dom: "ubclDom\<cdot>(ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3"
      by (metis assms(1) f0 ufCompO_def ufcomp_ran ufcomp_well_h x_dom1)

    have dom_f1_1: "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> ufDom\<cdot>f1 = ufDom\<cdot>f1"
      by blast
    obtain chain1 where chain1_def: "chain1 = (\<lambda>i.  iter_ubfix2 (ufCompH (ufComp f1 f2) f3) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) x)"
      by simp
    obtain chain2 where chain2_def: "chain2 = (\<lambda>i ia.  iter_ubfix2 (ufCompH f1 f2) ia (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) (x \<uplus> chain1 i\<bar>ufCompI f1 f2))"
      by simp

    have chain1_is_chain_h: "chain (\<lambda>i.  iter_ubfix2 (ufCompH (ufComp f1 f2) f3) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) x)"
      apply (rule chainI)
      by (metis assms(1) cont_pref_eq2I iterate_Suc2 ubcldom_least ubcldom_least_cs ufCompH_dom ufCompO_def ufcomp_ran x_dom1)
    have chain1_is_chain: "chain chain1"
      by (simp add: chain1_is_chain_h chain1_def)
    have chain1_insert: "\<And>i. chain1 i = iter_ubfix2 (ufCompH (ufComp f1 f2) f3) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) x"
      by (simp add: chain1_def)
    have chain1_iter_dom: "\<And>i. ubclDom\<cdot>(iter_ubfix2 (ufCompH (ufComp f1 f2) f3) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) x) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      by (metis assms(1) iter_ufCompH_dom ufCompO_def ufcomp_ran x_dom1)
    have chain1_iter_chain2_dom: "\<And>i. ubclDom\<cdot>(x \<uplus> chain1 i\<bar>ufCompI f1 f2) = ufCompI f1 f2"
      apply (simp add: chain1_insert)
      apply (simp add: ubclunion_ubclrestrict)
      apply (simp add: ubclunion_dom)
      apply (simp add: ubclrestrict_dom)
      apply (simp add: chain1_iter_dom)
      apply (subst x_dom2)
      apply (simp add: ufCompI_3arg_def)
      apply (simp add: ufCompI_def)
      by blast

    have chain2_is_chain: "\<And>i. chain (chain2 i)"
      apply (simp add: chain2_def)
      apply (rule chainI)
      by (metis chain1_iter_chain2_dom iterate_Suc2 monofun_cfun_arg ubcldom_least ubcldom_least_cs ufCompH_dom)
    have chain2_is_chain2: "\<And>j. chain (\<lambda>i. chain2 i j)"
      apply (simp add: chain2_def)
      apply (rule chainI)
      by (meson chain1_is_chain iter_ufCompH_mono2 monofun_Rep_cfun2 monofun_def po_class.chainE)
    have chain2_is_chain3: "chain (\<lambda>i. chain2 i i)"
      apply (simp add: chain2_def)
      apply (rule chainI)
      by (metis chain2_def chain2_is_chain chain2_is_chain2 po_class.chainE rev_below_trans)
    have chain2_insert: "\<And>i ia. chain2 i ia = iter_ubfix2 (ufCompH f1 f2) ia (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) (x \<uplus> chain1 i\<bar>ufCompI f1 f2)"
      by (simp add: chain2_def)

    have chain2_shift_ia: "\<And>i. chain (\<lambda>ia::nat. chain2 i (ia + 1))"
      apply (simp only: chain2_def)
      using chain2_def chain2_is_chain by auto
    have chain2_lub_shift: "\<And>i::nat. (\<Squnion>ia::nat. chain2 i (ia + (1::nat))) = Lub (chain2 i)"
      apply (subst po_eq_conv) apply rule defer
       apply (rule lub_mono)
         apply (simp add: chain2_is_chain)
        apply (simp add: chain2_is_chain po_class.chainE po_class.chainI)
       apply (simp add: chain2_is_chain chain_mono_less)
      by (metis below_refl chain2_is_chain lub_range_shift2)
    have diag_lub1: "\<And>j::nat. chain (\<lambda>i::nat. ufCompH f1 f2 (x \<uplus> chain1 i\<bar>ufCompI f1 f2)\<cdot>(chain2 i j) \<uplus> (f3 \<rightleftharpoons> x \<uplus> chain1 i\<bar>ufDom\<cdot>f3))"
    proof -
      fix j :: nat
      have "chain (\<lambda>n. f3 \<rightleftharpoons> x \<uplus> chain1 n\<bar>ufDom\<cdot>f3) \<and> chain (\<lambda>n. ufCompH f1 f2 (x \<uplus> chain1 n\<bar>ufCompI f1 f2))"
        by (metis (no_types) ch2ch_cont chain1_is_chain cont_Rep_cfun2 op_the_cont ufCompH_continX)
      then have "chain (\<lambda>n. f3 \<rightleftharpoons> x \<uplus> chain1 n\<bar>ufDom\<cdot>f3) \<and> chain (\<lambda>n. ubclUnion\<cdot> (ufCompH f1 f2 (x \<uplus> chain1 n\<bar>ufCompI f1 f2)\<cdot> (chain2 n j)))"
        using ch2ch_Rep_cfun ch2ch_cont chain2_is_chain2 cont_Rep_cfun2 by blast
      then show "chain (\<lambda>n. ufCompH f1 f2 (x \<uplus> chain1 n\<bar>ufCompI f1 f2)\<cdot> (chain2 n j) \<uplus> (f3 \<rightleftharpoons> x \<uplus> chain1 n\<bar>ufDom\<cdot>f3))"
        using ch2ch_Rep_cfun by blast
    qed
    have comph_f1f2_chain2_chain: "chain (\<lambda>i::nat. ufCompH f1 f2 (x \<uplus> chain1 i\<bar>ufCompI f1 f2)\<cdot>(chain2 i i))"
    proof -
      have "chain (\<lambda>n. x \<uplus> chain1 n\<bar>ufCompI f1 f2)"
        by (metis ch2ch_Rep_cfunR chain1_is_chain)
      then show "chain (\<lambda>n. ufCompH f1 f2 (x \<uplus> chain1 n\<bar>ufCompI f1 f2)\<cdot> (chain2 n n))"
        using ch2ch_Rep_cfun ch2ch_cont chain2_is_chain3 ufCompH_continX by blast
    qed
    have chain1_chain2_dom_f1_res: "\<And>i. (x \<uplus> chain1 i\<bar>ufCompI f1 f2) \<uplus> chain2 i i\<bar>ufDom\<cdot>f1 = (x \<uplus> chain1 i) \<uplus> chain2 i i\<bar>ufDom\<cdot>f1"
      apply (simp add: ufCompI_def)
      apply (subst ubclunion_ubclrestrict_minus)
       apply (simp add: chain1_iter_chain2_dom chain2_def)
      apply (simp add: ubclunion_ubclrestrict)
      apply (simp add: ubclrestrict_twice)
      by (simp add: dom_f1_1)
    have chain1_chain2_dom_f2_res: "\<And>i. (x \<uplus> chain1 i\<bar>ufCompI f1 f2) \<uplus> chain2 i i\<bar>ufDom\<cdot>f2 = (x \<uplus> chain1 i) \<uplus> chain2 i i\<bar>ufDom\<cdot>f2"
      apply (simp add: ufCompI_def)
      apply (subst ubclunion_ubclrestrict_minus)
       apply (simp add: chain1_iter_chain2_dom chain2_def)
      apply (simp add: ubclunion_ubclrestrict)
      apply (simp add: ubclrestrict_twice)
      by (simp add: Int_absorb1)


    have chain1_dom_f3: "\<And>i. ubclDom\<cdot>(x \<uplus> chain1 i\<bar>ufDom\<cdot>f3) = ufDom\<cdot>f3"
      apply (simp add: ubclunion_ubclrestrict)
      apply (simp add: ubclunion_dom)
      apply (simp add: ubclrestrict_dom)
      apply (subst chain1_insert)
      using a1 chain1_iter_dom f12 f2 by auto
    have chain1_chain2_commu: "(\<Squnion>i::nat. chain2 i i) \<uplus> (\<Squnion>i::nat. f3 \<rightleftharpoons> x \<uplus> chain1 i\<bar>ufDom\<cdot>f3) = (\<Squnion>i::nat. f3 \<rightleftharpoons> x \<uplus> chain1 i\<bar>ufDom\<cdot>f3) \<uplus> (\<Squnion>i::nat. chain2 i i)"
      apply (subst ubclunion_commu)
      apply (subst contlub_cfun_arg, simp add: chain2_is_chain3)
       apply (subst contlub_cfun_arg, simp add: chain1_is_chain op_the_chain)
       apply (subst chain2_insert)
       apply (subst ufran_2_ubcldom2)
        apply (simp add: chain1_dom_f3)
       apply (subst iter_ubfix_dom)
        apply (simp add: chain1_iter_chain2_dom ubcldom_least_cs)
       apply (metis assms(1) f0 lub_const ufCompO_def ufcomp_ran)
      apply (simp add: ubclunion_asso ubclunion_id)
      done
    have chain1_alt: "(\<Squnion>i::nat. chain1 i) = (\<Squnion>i::nat. chain1 i \<uplus> chain2 i i)"
      apply (subst lub_range_shift [of _ 1, symmetric])
       apply (simp add: chain1_is_chain)
      apply (subst chain1_insert, simp)
      apply (subst ufCompH_def, simp)
      apply (fold chain1_insert)
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain1_is_chain op_the_chain) +
      apply (simp add: assms(1) ufcomp_dom)
      apply (subst ufComp_def, simp)
      apply (simp add: chain1_iter_chain2_dom assms(1))
      apply (subst ubFix_def)
      apply (fold chain2_insert)
      apply (subst diag_lub)
        apply (simp add: chain2_is_chain2 chain2_is_chain) +
      apply (rule sym)
      apply (simp add: chain1_is_chain chain2_is_chain3 ubclunion_lub_sep2)
      apply (subst lub_range_shift [of _ 1, symmetric], simp add: chain1_is_chain)
      apply (subst chain1_insert, simp)
      apply (subst ufCompH_def, simp)
      apply (simp add: assms(1) ufcomp_dom)
      apply (fold chain1_insert)
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain1_is_chain op_the_chain) +
      apply (subst ufComp_def, simp)
      apply (simp add: chain1_iter_chain2_dom assms(1))
      apply (subst ubFix_def)
      apply (fold chain2_insert)
      apply (subst diag_lub)
        apply (simp add: chain2_is_chain2 chain2_is_chain) +
      apply (simp add: chain1_chain2_commu)
      by (simp add: ubclunion_asso ubclunion_id)
    have lub_f1f2f3_alt_f1: "f1 \<rightleftharpoons> x \<uplus> Lub chain1 \<bar>ufDom\<cdot>f1 = (\<Squnion>i::nat. f1 \<rightleftharpoons> x \<uplus> chain1 i \<uplus> chain2 i i\<bar>ufDom\<cdot>f1)"
      apply (subst chain1_alt)
      apply (subst contlub_cfun_arg, simp add: chain1_is_chain chain2_is_chain3)
      apply (subst contlub_cfun_arg, simp add: chain1_is_chain chain2_is_chain3)
      apply (subst ufunlub_ufun_fun, simp add: chain1_is_chain chain2_is_chain3)
      by (simp add: ubclunion_asso)
    have lub_f1f2f3_alt_f2: "f2 \<rightleftharpoons> x \<uplus> Lub chain1 \<bar>ufDom\<cdot>f2 = (\<Squnion>i::nat. f2 \<rightleftharpoons> x \<uplus> chain1 i \<uplus> chain2 i i\<bar>ufDom\<cdot>f2)"
      apply (subst chain1_alt)
      apply (subst contlub_cfun_arg, simp add: chain1_is_chain chain2_is_chain3)
      apply (subst contlub_cfun_arg, simp add: chain1_is_chain chain2_is_chain3)
      apply (subst ufunlub_ufun_fun, simp add: chain1_is_chain chain2_is_chain3)
      by (simp add: ubclunion_asso)
    have lub_f1f2f3_alt_f3: "f3 \<rightleftharpoons> x \<uplus> Lub chain1 \<bar>ufDom\<cdot>f3 = (\<Squnion>i::nat. f3 \<rightleftharpoons> x \<uplus> chain1 i \<uplus> chain2 i i\<bar>ufDom\<cdot>f3)"
      apply (subst chain1_alt)
      apply (subst contlub_cfun_arg, simp add: chain1_is_chain chain2_is_chain3)
      apply (subst contlub_cfun_arg, simp add: chain1_is_chain chain2_is_chain3)
      apply (subst ufunlub_ufun_fun, simp add: chain1_is_chain chain2_is_chain3)
      by (simp add: ubclunion_asso)

    have lub_f1f2f3_alt: "ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) = (f1 \<rightleftharpoons> x \<uplus> ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1)
    \<uplus> (f2 \<rightleftharpoons> x \<uplus> ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2) 
    \<uplus> (f3 \<rightleftharpoons> x \<uplus> ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3)"
      apply (subst ubFix_def)
      apply (subst lub_range_shift [of _ 1, symmetric])
       apply (simp add: chain1_is_chain_h, simp)
      apply (subst ufCompH_def, simp)
      apply (simp add: assms(1) ufcomp_dom)
      apply (fold chain1_insert)
      apply (subst ufComp_def)
      apply (simp add: assms(1) chain1_iter_chain2_dom) 
      apply (subst ubFix_def)
      apply (fold chain2_insert)
      apply (fold chain2_lub_shift)
      apply (simp add: chain2_def)
      apply (fold chain2_insert)
      apply (subst contlub_cfun_arg)
      apply (simp add: chain2_is_chain)
      apply (subst contlub_cfun_fun)
       apply (simp add: chain2_is_chain)
      apply (subst diag_lub)
      apply (simp add: diag_lub1)
      using chain2_is_chain apply auto[1]
      apply (subst ubclunion_lub_sep2)
        apply (simp add: comph_f1f2_chain2_chain)
       apply (simp add: chain1_is_chain op_the_chain)
      apply (subst ufCompH_def, simp)
      apply (subst ubclunion_lub_sep2)
        apply (simp add: chain1_is_chain chain2_is_chain3 op_the_chain)
       apply (simp add: chain1_is_chain chain2_is_chain3 op_the_chain)
      apply (simp add: chain1_chain2_dom_f1_res) 
      apply (simp add: ubFix_def)
      apply (fold chain1_insert)
      apply (fold lub_f1f2f3_alt_f1)
      apply (subst lub_f1f2f3_alt_f2)
      apply (simp add: chain1_chain2_dom_f2_res)
      by (simp add: chain1_is_chain contlub_cfun_arg op_the_lub)
    have R_le_L: "ufComp3 f1 f2 f3 \<rightleftharpoons> x \<sqsubseteq> ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (simp add: x_dom2  ufComp3_def)
      apply (rule ubfix_least_below)
        apply (simp add: ufCompH_3arg_io_eq x_dom2)
       apply (simp add: comp3arg_fix_dom)
      apply (simp add: ufCompH_3arg_def)
      apply (simp add: ufCompH_3arg_cont1)
      using lub_f1f2f3_alt by auto
    have comp3_arg_fix_eq: "ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) = (f1 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2) \<uplus>
    (f3 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3)"
      apply (subst ubfix_eq)
       apply (simp add: ufCompH_3arg_io_eq x_dom2)
      apply (subst ufCompH_3arg_def)
      by (simp add: ufCompH_3arg_cont1)
    have comp3_arg_x_dom_f1: "ubclDom\<cdot>(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1) = ufDom\<cdot>f1"
      by (metis Un_Diff_cancel2 a1 f12 f2 le_supI1 sup_ge1 ubclunion_ubcldom ubrestrict_dom2 ufcomp3_well_h x_dom2)
    have comp3_arg_x_dom_f2: "ubclDom\<cdot>(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2) = ufDom\<cdot>f2"
      apply (simp add: ubclunion_restrict ubclunion_dom ubclrestrict_dom)
      apply (subst ubfix_dom)
       apply (simp add: ufCompH_3arg_io_eq x_dom2)
      apply (simp add: x_dom2 ufCompI_3arg_def)
      by blast
    have comp3_arg_res_f1_f2: "(ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) 
= (f1 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2)"
      apply (subst comp3_arg_fix_eq)
      apply (subst ubclunion_restrict_R)
       apply (subst ufran_2_ubcldom2)
        apply (metis Un_Diff_cancel2 a1 f12 f2 le_supI1 sup_ge2 ubclunion_ubcldom ubrestrict_dom2 ufcomp3_well_h x_dom2)
       apply (simp add: assms(2) assms(3) inf.commute inf_sup_distrib1)
      apply (rule ubclrestrict_dom_idI)
      apply (simp add: ubclunion_dom)
      using comp3_arg_x_dom_f1 comp3_arg_x_dom_f2 ufran_2_ubcldom2 by blast
    have ufcomph_3arg_splt: "ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) = 
(ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f3)"
      using comp3_arg_fix_eq comp3_arg_res_f1_f2 by auto
    have x_fix_comp3_dom_f1_f2: "ubclDom\<cdot>(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f1 f2) = ufCompI f1 f2"
      by (metis (no_types, lifting) Int_Diff Un_def comp3_arg_x_dom_f1 comp3_arg_x_dom_f2 inf_sup_distrib1 ubclrestrict_ubcldom ufCompI_def)

    have int_compi_f1_f2_f1: "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) \<inter> ufDom\<cdot>f1 = ((ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> ufDom\<cdot>f1)  - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
      by (simp add: Diff_Int2 Diff_Int_distrib2)
    have int_compi_f1_f2_f2: "(ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) \<inter> ufDom\<cdot>f2 = ((ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> ufDom\<cdot>f2)  - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
      by (simp add: Diff_Int2 Diff_Int_distrib2)
    have fix_comp3_res_id_f1: "(((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f1 f2)\<bar>ufDom\<cdot>f1) \<uplus> ((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<bar>ufDom\<cdot>f1)) = 
ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1"
      apply (simp add: ubclrestrict_twice)
      apply (simp add: ufCompI_def)
      apply (simp add: int_compi_f1_f2_f1)
      apply (simp add: dom_f1_1)
      apply (simp add: inf_sup_aci(1))
      by (simp add: ubclunion_ubclrestrict_minus_id)
    have fix_comp3_res_id_f2: "(((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f1 f2)\<bar>ufDom\<cdot>f2) \<uplus> ((ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<bar>ufDom\<cdot>f2)) = 
ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2"
      apply (simp add: ubclrestrict_twice)
      apply (simp add: ufCompI_def)
      apply (simp add: int_compi_f1_f2_f2)
      by (metis Int_absorb1 inf_sup_aci(1) sup_ge2 ubclunion_ubclrestrict_minus_id)
    have x_fix_comp3_f1_simp: "(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f1 f2) \<uplus> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<bar>ufDom\<cdot>f1 = 
x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f1"
      apply (simp add: ubclunion_restrict)
      apply (simp add: ubclunion_asso)
      apply (simp add: fix_comp3_res_id_f1)
      apply (fold ubclunion_ubclrestrict)
      apply (subst ufCompI_def)
      apply (subst ubclunion_ubclrestrict_minus)
       apply (simp add: ufcomp3_well_h x_dom2)
      apply (simp add: ubclunion_restrict ubclrestrict_twice)
      by (simp add: dom_f1_1)
    have x_fix_comp3_f2_simp: "(x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufCompI f1 f2) \<uplus> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)\<bar>ufDom\<cdot>f2 = 
x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>f2"
      apply (simp add: ubclunion_restrict)
      apply (simp add: ubclunion_asso)
      apply (simp add: fix_comp3_res_id_f2)
      apply (fold ubclunion_ubclrestrict)
      apply (subst ufCompI_def)
      apply (subst ubclunion_ubclrestrict_minus)
       apply (simp add: ufcomp3_well_h x_dom2)
      apply (simp add: ubclunion_restrict ubclrestrict_twice)
      by (simp add: Int_absorb1)
    have compf1f2_below: "(ufComp f1 f2 \<rightleftharpoons> x \<uplus> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>ufDom\<cdot>(ufComp f1 f2)) \<sqsubseteq> (ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)\<bar>(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
      apply (simp add: assms(1) ufcomp_dom)
      apply (subst ufComp_def)
      apply (simp add: assms(1) x_fix_comp3_dom_f1_f2)
      apply (rule ubfix_least_below)
        apply (simp add: ubcldom_least_cs x_fix_comp3_dom_f1_f2)
       apply (simp add: ubrestrict_dom2 ufcomp3_well_h x_dom2)
      apply (subst ufCompH_def, simp)
      apply (simp add: x_fix_comp3_f1_simp x_fix_comp3_f2_simp)
      by (simp add: comp3_arg_res_f1_f2)
    have "ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<sqsubseteq> ubFix (ufCompH_3arg f1 f2 f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3)"
      apply (rule ubfix_least_below)
        apply (simp add: assms(1) ubcldom_least_cs ufCompO_def ufcomp_ran x_dom1)
      using ufcomp3_well_h x_dom2 apply blast
      apply (subst ufCompH_def, simp)
      by (metis comp3_arg_fix_eq comp3_arg_res_f1_f2 compf1f2_below monofun_cfun_arg monofun_cfun_fun)
    then have L_lq_R: "ubFix (ufCompH (ufComp f1 f2) f3 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2 \<union> ufRan\<cdot>f3) \<sqsubseteq> ufComp3 f1 f2 f3 \<rightleftharpoons> x"
      by (simp add: ufComp3_def x_dom2)
    show "ufComp (ufComp f1 f2) f3 \<rightleftharpoons> x = ufComp3 f1 f2 f3 \<rightleftharpoons> x" (is "?L = ?R")
      apply (simp add: ufComp_def)
      apply (fold compf1f2_insert)
      apply (simp add: x_dom1 f0)
      apply (simp add: ufcomp_ran assms(1))
      apply (simp add: ufCompO_def)
      by (simp add: L_lq_R R_le_L po_eq_conv)
  qed
  show ?thesis
    by (simp add: f100 f200)
qed





instantiation ufun:: (ubcl_comp,ubcl_comp) ufuncl_comp
begin

definition ufunclLeast_ufun_def: "ufunclLeast = ufLeast"

instance 
  apply intro_classes
  apply (simp add: UFun_Comp.ufunclLeast_ufun_def ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: ufclDom_ufun_def ufunclLeast_ufun_def)
  apply (simp add: UFun_Comp.ufunclLeast_ufun_def ufclRan_ufun_def)
  done
end


(*

instantiation ufun:: (ubcl_comp,ubcl_comp) ufuncl_comp
begin

definition ufunclLeast_ufun_def: "ufunclLeast = ufLeast"

definition ufunclComp_ufun_def: "ufunclComp = ufComp"
definition ufunclParComp_ufun_def: "ufunclParComp = ufParComp"
definition ufunclSerComp_ufun_def: "ufunclSerComp = ufSerComp"
definition ufunclFeedbackComp_ufun_def: "ufunclFeedbackComp = ufFeedbackComp"

definition ufunclCompWell_ufun_def: "ufunclCompWell = comp_well"
definition ufunclSerCompWell_ufun_def: "ufunclSerCompWell = sercomp_well"
definition ufunclParCompWell_ufun_def: "ufunclParCompWell = parcomp_well"


lemma ufunclParCompWell_ufun_eq: "ufunclParCompWell f1 f2 = parcomp_well f1 f2"
  by (simp add: ufunclParCompWell_ufun_def)

lemma ufunclSerCompWell_ufun_eq: "ufunclSerCompWell f1 f2 = sercomp_well f1 f2"
  by (simp add: ufunclSerCompWell_ufun_def)

lemma ufun_sercompwell_asso: "\<And>(f1::'a ufun) (f2::'a ufun) f3::'a ufun. ufunclSerCompWell f1 f2 \<Longrightarrow> 
      ufunclSerCompWell f2 f3 \<Longrightarrow> ufclDom\<cdot>f2 \<inter> ufclRan\<cdot>f3 = {} \<Longrightarrow>
      ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f2 = {} \<Longrightarrow> ufunclSerCompWell f1 (f2 \<circ> f3) \<and> ufunclSerCompWell (f1 \<circ> f2) f3"
proof -
  fix f1::"'a ufun" and f2::"'a ufun" and f3::"'a ufun"
  assume a1: "ufunclSerCompWell f1 f2"
  assume a2: "ufunclSerCompWell f2 f3"
  assume a3: "ufclDom\<cdot>f2 \<inter> ufclRan\<cdot>f3 = {}"
  assume a4: "ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f2 = {}"
  have f1: "sercomp_well f1 f2"
    using a1 ufunclSerCompWell_ufun_eq by blast
  have f2: "sercomp_well f2 f3"
    using a2 ufunclSerCompWell_ufun_eq by blast
  show "ufunclSerCompWell f1 (f2 \<circ> f3) \<and> ufunclSerCompWell (f1 \<circ> f2) f3"
    unfolding ufunclSerCompWell_ufun_def ufunclSerComp_ufun_def
    apply rule
    apply (subst ufSerComp_ran)
    using a2 ufunclSerCompWell_ufun_eq apply blast 
    apply (subst ufSerComp_dom)
    using a2 ufunclSerCompWell_ufun_eq apply blast 
    apply (subst ufSerComp_dom)
    using a2 ufunclSerCompWell_ufun_eq apply blast 
     apply (simp add: f1)
     apply rule
    using f1 apply blast
     apply (metis a3 ufclDom_ufun_def ufclRan_ufun_def)
    apply (subst ufSerComp_ran)
    using f1 apply blast
    apply (subst ufSerComp_ran)
    using f1 apply blast
    apply (subst ufSerComp_dom)
    using f1 apply blast
    apply rule
     apply (simp add: f2)
    apply rule
     apply (metis a4 ufclDom_ufun_def ufclRan_ufun_def)
    by (simp add: f2) 
qed

instance 
  apply intro_classes
  apply (simp add: UFun_Comp.ufunclLeast_ufun_def ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: ufclDom_ufun_def ufunclLeast_ufun_def)
  apply (simp add: UFun_Comp.ufunclLeast_ufun_def ufclRan_ufun_def)
  apply (simp add: inf_sup_aci(1) ufcomp_L_commu ufunclParCompWell_ufun_def)
  apply (simp add: comp_well_def inf_sup_aci(1) ufunclCompWell_ufun_def)
  apply (simp add: UFun_Comp.ufunclParComp_ufun_def ufParComp_dom ufclDom_ufun_def ufunclParCompWell_ufun_def)
  apply (simp add: UFun_Comp.ufunclParComp_ufun_def ufParComp_ran ufclRan_ufun_def ufunclParCompWell_ufun_def)
  apply (simp add: UFun_Comp.ufunclCompWell_ufun_def UFun_Comp.ufunclComp_ufun_def comp_well_def ufCompI_def ufcomp_dom)
  using ufSerComp_dom ufunclSerComp_ufun_def apply auto[1]
  apply (simp add: ufunclSerCompWell_ufun_def ufclRan_ufun_def ufunclSerComp_ufun_def)
  apply (simp add: comp_well_def ufCompO_def ufcomp_ran ufunclCompWell_ufun_def ufunclComp_ufun_def)
  apply (simp add: comp_well_def ufCompO_def ufclRan_ufun_def ufcomp_ran ufunclCompWell_ufun_def ufunclComp_ufun_def)
  apply (simp add: comp_well_def ufCompO_def ufclRan_ufun_def ufcomp_ran ufunclCompWell_ufun_def ufunclComp_ufun_def)
  apply (simp add: UFun_Comp.ufunclParCompWell_ufun_eq UFun_Comp.ufunclParComp_ufun_def ufParComp_dom ufclDom_ufun_def)
  apply (simp add: UFun_Comp.ufunclParCompWell_ufun_eq ufParComp_ran ufunclParComp_ufun_def)
  apply (simp add: UFun_Comp.ufunclParCompWell_ufun_def UFun_Comp.ufunclParComp_ufun_def ufParComp_ran ufclRan_ufun_def)
  defer
  defer
  apply (simp add: UFun_Comp.ufunclFeedbackComp_ufun_def ufFeedbackComp_dom ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: ufFeedbackComp_ran ufclRan_ufun_def ufunclFeedbackComp_ufun_def)     
  apply (metis UFun_Comp.ufunclCompWell_ufun_def UFun_Comp.ufunclComp_ufun_def comp_well_def ufcomp_commu)     
  apply (metis UFun_Comp.ufunclParCompWell_ufun_eq UFun_Comp.ufunclParComp_ufun_def ufParComp_commutativity)
  apply (simp add: UFun_Comp.ufunclParComp_ufun_def ufParComp_asso ufunclParCompWell_ufun_def)
  apply (simp add: ufunclSerComp_ufun_def)
  using ufSerComp_asso ufunclSerCompWell_ufun_eq apply blast
     apply (simp add: UFun_Comp.ufunclParCompWell_ufun_eq ufParCompWell_associativity ufunclParComp_ufun_def)
  apply (simp add: ufun_sercompwell_asso)
  proof -
    fix f1 :: "'a ufun" and f2 :: "'a ufun"
    assume a1: "ufunclSerCompWell f1 f2"
    then have "ufRan\<cdot>f1 = ufDom\<cdot>f2"
      by (meson UFun_Comp.ufunclSerCompWell_ufun_eq)
    then show "ufclDom\<cdot>(ufunclSerComp f1 f2) = ufclDom\<cdot>f1"
      using a1 by (simp add: UFun_Comp.ufunclSerCompWell_ufun_eq ufSerComp_dom ufclDom_ufun_def ufunclSerComp_ufun_def)
 next
   fix f1 :: "'a ufun" and f2 :: "'a ufun"
   assume a1: "ufunclSerCompWell f1 f2"
   then have "ufRan\<cdot>f1 = ufDom\<cdot>f2"
     by (meson UFun_Comp.ufunclSerCompWell_ufun_eq)
   then show "ufclRan\<cdot>(ufunclSerComp f1 f2) = ufclRan\<cdot>f2"
     using a1 by (simp add: UFun_Comp.ufunclSerCompWell_ufun_eq UFun_Comp.ufunclSerComp_ufun_def ufSerComp_ran ufclRan_ufun_def)
 qed
     

end
*)




end