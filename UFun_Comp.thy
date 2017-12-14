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


abbreviation ubclUnion_abbr :: " 'm \<Rightarrow> 'm \<Rightarrow> 'm" (infixl "\<uplus>" 100) where 
"b1 \<uplus> b2 \<equiv> ubUnion\<cdot>b1\<cdot>b2"

abbreviation ubclRestrict_abbr :: " 'm \<Rightarrow> channel set \<Rightarrow> 'm" ("(_\<bar>_)" [66,65] 65)
where "b\<bar>cs \<equiv> ubRestrict cs\<cdot>b"

  
subsection\<open>definitions\<close>  

  
definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in \<Rrightarrow> 'out)" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = cin) \<leadsto> ubLeast cout)"  
  
  
subsection\<open>channel sets\<close>

  
text {* the input channels of the composition of f1 and f2 *}
definition ufCompI :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompI f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the internal channels of the composition of f1 and f2 *}
definition ufCompL :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompL f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the output channels of the composition of f1 and f2 *}
definition ufCompO :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompO f1 f2 \<equiv> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* all channels of the composition of f1 and f2  *}
definition ufCompC :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompC f1 f2 \<equiv> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"


subsection \<open>ubFix\<close>
  
  
definition ubFix :: "('m \<rightarrow> 'm) \<Rightarrow> channel set \<Rightarrow> 'm" where 
"ubFix F cs = (\<Squnion>i. iterate i\<cdot>F\<cdot>(ubLeast cs))"

text {* special case ubFix for cont of the composition *}
definition ubFix2 :: "('m  \<Rightarrow> 'm  \<rightarrow> 'm ) \<Rightarrow> 'm  \<Rightarrow> channel set \<Rightarrow> 'm " where
"ubFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(ubLeast cs))"

abbreviation iter_ubfix2 :: "('m \<Rightarrow> 'm \<rightarrow> 'm) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm \<Rightarrow> 'm" where
"iter_ubfix2 F i cs \<equiv>  (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(ubLeast cs))"

text {* ubfun_io_eq f cs is true if f applied to the least ub  with domain cs delivers a 
        ub with the same domain *}
abbreviation ubfun_io_eq :: "('m \<rightarrow> 'm ) \<Rightarrow> channel set \<Rightarrow> bool" where
"ubfun_io_eq f cs \<equiv> ubDom\<cdot>(f\<cdot>(ubLeast cs)) = cs"


subsection \<open>composition helpers\<close>

 
definition ufCompH :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> ('m \<rightarrow> 'm)" where
"ufCompH f1 f2 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)))"

abbreviation iter_ufCompH :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> nat \<Rightarrow> 'm  \<Rightarrow> 'm" where
"(iter_ufCompH f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))" 


subsection \<open>composition operators\<close>


definition ufComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" where
"ufComp f1 f2 \<equiv>
let I = ufCompI f1 f2;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)
in Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = I) \<leadsto> ubFix (ufCompH f1 f2 x) Oc))" 


definition ufParComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" ("_\<parallel>_") where
"ufParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))))"

definition parcomp_well :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> bool" where
"parcomp_well f1 f2 \<equiv> (ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"


abbreviation sercomp_well :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> bool" where
"sercomp_well f1 f2 \<equiv>  (ufRan\<cdot>f1 = ufDom\<cdot>f2) 
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                        \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"

definition ufSerComp :: "('m \<Rrightarrow> 'm) => ('m \<Rrightarrow> 'm) => ('m \<Rrightarrow> 'm)"  ("_\<circ>_") where
"ufSerComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"


definition ufFeedH:: "('m \<Rrightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> 'm  \<rightarrow> 'm" where
"ufFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"

definition ufFeedbackComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" ("\<mu>_" 50) where
"ufFeedbackComp f \<equiv>
let I  = ufDom\<cdot>f - ufRan\<cdot>f;
    C  = ufRan\<cdot>f
in Abs_ufun (Abs_cfun (\<lambda> sb. (ubDom\<cdot>sb = I) \<leadsto>
    (ubFix (ufFeedH f sb) C)))"  

  
(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)  

  
subsection \<open>ubLeast\<close>

  
(* ubLeast is in the same dome as the function f  *)
lemma ufunLeastIDom: "(ubLeast (ufDom\<cdot>f)) \<in> dom (Rep_cufun f)"
  by (metis rep_ufun_well domD ubdom_least_cs ufWell_def ufdom_2ufundom)

(* The range of an ufun is equal to the domain of f applied to the least ubundle with domain 
       ufDom f *)
lemma ufran_least: "ufRan\<cdot>f = ubDom\<cdot>(f\<rightleftharpoons>(ubLeast (ufDom\<cdot>f)))"
  apply (simp add: ufRan_def)
  by (metis (no_types) domD option.sel ufunLeastIDom ufran_2_ubdom ufran_insert)

    
subsection\<open>ubFix\<close>

  
(* ub fix iteration is a chain  *)
lemma ub_iterate_chain: "ubDom\<cdot>(F\<cdot>(ubLeast cs)) = cs \<Longrightarrow> chain (\<lambda>i. iterate i\<cdot>F\<cdot>(ubLeast cs))"
  apply (rule chainI, subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by (metis ubdom_least)

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
  shows "ubDom\<cdot>(iter_ubfix2 F i cs x) = cs"
proof (induction i)
  case 0
  then show ?case
    by (metis assms iterate_0 ubdom_fix ubdom_least)
next
  case (Suc i)
  then show ?case
  proof -
    have "ubLeast cs \<sqsubseteq> iter_ubfix2 F i cs x"
      by (metis Suc.IH ubdom_least)
    then have "\<forall>c. ubDom\<cdot>(c\<cdot>(iter_ubfix2 F i cs x)) = ubDom\<cdot>(c\<cdot>(ubLeast cs)::'a)"
      using monofun_cfun_arg ubdom_fix by blast
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
  have f2: "ubDom\<cdot>x = ubDom\<cdot>y"
    by (simp add: assms(1) ubdom_fix)
  have f3: "ubfun_io_eq (F y) cs"
    using assms(1) assms(2) assms(3) cont2monofunE monofun_cfun_fun ubdom_fix by blast
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
    using assms(1) assms(2) assms(3) cont2monofunE is_ub_thelub monofun_cfun_fun ubdom_fix by blast
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
    using assms(1) assms(2) assms(3) cont2monofunE is_ub_thelub monofun_cfun_fun ubdom_fix by blast
  ultimately show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_ubfix2_chain)
qed
  
(* dom *)
(* the lub of the second arg has the similar channel set to the result of F x  *)
lemma lub_iter_ubfix2_dom: assumes "ubfun_io_eq (F x) cs"
  shows "ubDom\<cdot>(\<Squnion>i. iter_ubfix2 F i cs x) =  cs"
proof -
  have "\<And>n. ubfun_io_eq (iterate n\<cdot>(F x)) cs"
    by (simp add: assms iter_ubfix2_dom)
  then show ?thesis
    by (metis (no_types, lifting) assms is_ub_thelub lub_eq ub_iterate_chain ubdom_fix)
qed
    

subsubsection \<open>if_lub_iter_ubfix2\<close>

  
(* mono *)
(* the processing function has the same relation as its last argument *)
lemma if_lub_iter_ubfix2_mono_pre: assumes "x\<sqsubseteq> y" and "cont F"
                                   and "(P x) \<Longrightarrow> ubfun_io_eq (F x) cs"
                                   and "ubDom\<cdot>x = ubDom\<cdot>y \<Longrightarrow> (P x) = (P y)"
  shows "((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x)) x)
         \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x)) y)"
proof (cases "(P x)")
  case True
  hence f1: "ubfun_io_eq (F x) cs"
    by (simp add: assms(3))
  have f2: "ubDom\<cdot>x = ubDom\<cdot>y"
    by (simp add: assms(1) ubdom_fix)
  have f3: "(\<Squnion>i.(iter_ubfix2 F i cs) x) \<sqsubseteq> (\<Squnion>i.(iter_ubfix2 F i cs) y)"
    by (simp add: assms(1) assms(2) f1)
  thus ?thesis
    using assms(4) f2 some_below by auto
next
  case False
  have "ubDom\<cdot>y = ubDom\<cdot>x"
    by (metis assms(1) ubdom_fix)
  then show ?thesis
    using False assms(4) by auto
qed

(* Intro lemma for if ubfix is mono *)  
(* the processing function is mono on the last argument of iter_ubfix2  *)
lemma ubfix_monoI [simp]: assumes "cont F" "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                          and "\<And> x y. ubDom\<cdot>x = ubDom\<cdot>y \<Longrightarrow> P x = P y"
                        shows "monofun (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x))"
proof (rule monofunI)
    fix x :: "'a" and y :: "'a"
    assume a1: "x \<sqsubseteq> y"
   show "(P x)\<leadsto>\<Squnion>n. iter_ubfix2 F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_ubfix2 F n cs y"
   proof (cases "P x")
     case True
     have f10: "P y"
       using True a1 assms(3) ubdom_fix by blast
     have "(\<Squnion>n. iter_ubfix2 F n cs x) \<sqsubseteq> (\<Squnion>n. iter_ubfix2 F n cs y)"
       by (simp add: True a1 assms(1) assms(2))
     then show ?thesis 
       by (simp add: True f10 some_below)
   next
     case False
     then have "P y \<Longrightarrow> False"
       using a1 assms(3) ubdom_fix by blast
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
                                      and "\<And> x y. ubDom\<cdot>x = ubDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_ubfix2 F ia cs) (Y i)))"
proof -
  have f2: "(\<Squnion>i. iter_ubfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_ubfix2 F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f4: "Some (\<Squnion>i ia. iter_ubfix2 F i cs (Y ia)) \<sqsubseteq> Some (\<Squnion>i ia.  iter_ubfix2 F ia cs (Y i))"
    by (simp add: assms(1) assms(2) assms(3) assms(4) chain_lub_lub_iter_ubfix2 some_below)
  have f5: "(\<Squnion>i. (P (Y i)) \<leadsto>   \<Squnion>ia. iter_ubfix2 F ia cs (Y i)) 
                 = (\<Squnion>i. Some(\<Squnion>ia. iter_ubfix2 F ia cs (Y i)))"
    by (meson assms(1) assms(2) assms(5) is_ub_thelub ubdom_fix)
  have "Some (\<Squnion>n na. iter_ubfix2 F na cs (Y n)) = (\<Squnion>n. Some (\<Squnion>na. iter_ubfix2 F na cs (Y n)))"
    by (simp add: assms(1) assms(2) assms(3) assms(4) chain_lub_iter_sbfix2 some_lub_chain_eq)
  then show ?thesis
      using assms(1) f2 f4 f5 by presburger
  qed

(* lub of iter_ubfix2 is less or eq to the lub of the chain *)
lemma chain_if_lub_iter_ubfix2:  assumes "chain Y" and "cont F"
                                  and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                                  and "\<And> x y. ubDom\<cdot>x = ubDom\<cdot>y \<Longrightarrow> P x = P y" 
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_ubfix2 F ia cs) (Y i)))"
proof (cases "P (\<Squnion>i. Y i)")
  case True
  thus ?thesis
    using  chain_if_lub_iter_ubfix2_case assms by blast
next
  case False
  hence f3: "\<And>i. \<not> (P (Y i))"
    using assms(1) assms(4) is_ub_thelub ubdom_fix by blast
  thus ?thesis
    by (simp add: False)
qed
         
(* Intro lemma for cont proofs with ubfix *)
lemma ubfix_contI [simp]:   assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs" 
                             and "\<And> x y. ubDom\<cdot>x = ubDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "cont (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_ubfix2 F i cs) x) )"
    apply (rule contI2)
    using ubfix_monoI assms apply blast
    using chain_if_lub_iter_ubfix2 assms by blast

 
subsubsection \<open>ubFix\<close>    

    
(* ubfix is cont in X *)
lemma ubfix_contI2 [simp]: fixes F :: "'m \<Rightarrow> 'm \<rightarrow> 'm"
                            assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> ubfun_io_eq (F x) cs"
                            and "\<And> x y. ubDom\<cdot>x = ubDom\<cdot>y \<Longrightarrow> P x = P y"
                          shows "cont (\<lambda> x. (P x) \<leadsto> ubFix (F x) cs)"
  apply(subst ubfix_2_ubfix2)
  apply (subst ubFix2_def)
  using ubfix_contI assms by blast

(* the domain is always the same if io_eq holds *)
lemma iter_ubfix_dom: assumes "ubfun_io_eq F cs"
  shows "ubDom\<cdot>(iterate i\<cdot>F\<cdot>(ubLeast cs)) = cs"
proof (induction i)
      case 0
      then show ?case
        by (metis assms iterate_0 ubdom_fix ubdom_least)
    next
      case (Suc i)
      then show ?case
      proof -
        have "\<And>c. (c\<cdot>(ubLeast cs)::'a) \<sqsubseteq> c\<cdot>(F\<cdot>(ubLeast cs))"
          by (metis (full_types) assms monofun_cfun_arg ubdom_least)
        then show ?thesis
          by (metis (no_types) Suc iterate_Suc2 ubdom_fix)
      qed
qed

lemma ubfix_dom: assumes "ubfun_io_eq (F) cs"
  shows "ubDom\<cdot>(ubFix F cs) =  cs"
  by (metis (mono_tags, lifting) assms is_ub_thelub iter_ubfix_dom ubFix_def ub_iterate_chain ubdom_fix)
 
    
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
lemma ubfix_least_below: assumes "ubfun_io_eq F cs" and "ubDom\<cdot>x = cs"
  shows "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> (ubFix F cs) \<sqsubseteq> x"
  apply (simp add: ubFix_def)
  apply (rule lub_below)
   apply (simp add: assms ub_iterate_chain)
  apply (induct_tac i)
   apply (simp add: assms(2))
  using assms(2) ubdom_least apply blast
  apply (simp add: assms(1))
  apply (erule rev_below_trans)
  by (erule monofun_cfun_arg)

(* ubFix calculates the least fixed point *)
lemma ubfix_least: assumes "ubfun_io_eq F cs" and "ubDom\<cdot>x = cs"
                    and "F\<cdot>x = x"
  shows "(ubFix F cs) \<sqsubseteq> x"
  by (simp add: assms(1) assms(2) assms(3) ubfix_least_below)

 (* Intro rule for ubfix_eq *)
lemma ubfix_eqI: assumes fp: "F\<cdot>x = x" and lst: "\<And>z. ubDom\<cdot>z = cs \<Longrightarrow> F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
                  and "ubfun_io_eq F cs" and "ubDom\<cdot>x = cs"
                shows "(ubFix F cs) = x"
  by (metis assms(3) assms(4) below_antisym fp lst ubfix_dom ubfix_eq ubfix_least)  

(* compatibility lemmas to Fix.thy *)
lemma ubfix_least_iff: assumes "ubfun_io_eq F cs"
  shows "((ubFix F cs) = ubLeast cs) = (F\<cdot>(ubLeast cs) = ubLeast cs)"
proof -
  have "F\<cdot>(ubFix F cs) = ubFix F cs"
    by (metis (full_types) assms ubfix_eq)
  then show ?thesis
    by (metis assms ubdom_least ubfix_eqI)
qed

(* if F returns ubLeast with ubLeast as arguments then ubFix will return the ubLeast  *)
lemma ubfix_strict: assumes "ubfun_io_eq F cs" and "F\<cdot>(ubLeast cs) = (ubLeast cs)"
  shows "(ubFix F cs) = ubLeast cs"
  using assms(1) assms(2) ubfix_least_iff by blast

(* if F is not strict and returns other than ubLeast when it has ubLeast as argument then ubFix also returns other than ubLeast  *)
lemma ubfix_defined: assumes "ubfun_io_eq F cs" and "F\<cdot>(ubLeast cs) \<noteq> (ubLeast cs)"
  shows "(ubFix F cs) \<noteq> ubLeast cs"
  by (metis assms(1) assms(2) ubfix_eq)

(* ubFix calculates the id function  *)
lemma ubfix_id: "(ubFix (\<Lambda> x. x) cs) = (ubLeast cs)"
  by (simp add: ubdom_least_cs ubfix_strict)

(* ubfix will return the function if it is a constant  *)
lemma ubfix_const: assumes "ubDom\<cdot>c = cs"
  shows "(ubFix (\<Lambda> x. c) cs) = c"
  by (metis Abs_cfun_inverse2 assms cont_const ubfix_eq)

(* ubfix induction *)
lemma ubfix_ind: assumes "ubfun_io_eq F cs"
                  and "adm P" and "P (ubLeast cs)"
                  and "\<And> x. \<lbrakk>(ubDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F\<cdot>x)"
  shows "P (ubFix F cs)"
proof -
  have f1: "\<And> n. ubDom\<cdot>(iterate n\<cdot>F\<cdot>(ubLeast cs)) = cs"
    by (simp add: assms(1) iter_ubfix_dom)
  show ?thesis
    unfolding ubFix_def
    apply (subst admD, simp_all add: assms)
      apply (simp add: assms(1) ub_iterate_chain)
      apply (rule nat_induct, simp add: assms(3))
      by (simp add: assms(4) f1)
qed

(* an adm P will hold on ubFix result if it holds on ubLeast and for every arguments, if P holds on that argument then 
P hold on the result after the function F is applied  *)
lemma cont_ubfix_ind: assumes "cont F" and "ubfun_io_eq (Abs_cfun F) cs"
                       and "adm P" and "P (ubLeast cs)"
                       and "\<And> x. \<lbrakk>(ubDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F x)"
  shows "P (ubFix (Abs_cfun F) cs)"
  apply (rule ubfix_ind, simp_all add: assms)
  using assms(1) assms(2) by auto

(* P holds on ubFix with function f and channel set cs when P is adm, P holds on ubLeast, result of f applied on ubLeast
and also on induction step s2  *)
lemma ubfix_ind2:  assumes "ubfun_io_eq F cs"
                    and "adm P" and s0: "P ((ubLeast cs))" and s1: "P (F\<cdot>(ubLeast cs))"
                    and s2: "\<And> x. \<lbrakk>(ubDom\<cdot>x) = cs; P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
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
  hence "cont (\<lambda>s. ubUnion\<cdot> (b \<uplus> Rep_cfun (Rep_ufun f1)\<rightharpoonup>(s\<bar>ufDom\<cdot>f1))) 
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

lemma ufRanRestrict [simp]: assumes "ufDom\<cdot>f2 \<subseteq> ubDom\<cdot>b"
  shows "ubDom\<cdot>(Rep_cufun f2\<rightharpoonup>(b\<bar>ufDom\<cdot>f2)) = ufRan\<cdot>f2"
  using assms ubrestrict_dom ufran_2_ubdom2 by fastforce
    

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
  have "cont (\<lambda>z. ubUnion\<cdot>(f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1))) 
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
  have "cont (\<lambda>x. ubUnion\<cdot>(f1\<rightleftharpoons>((x \<uplus> z)\<bar>ufDom\<cdot>f1))) 
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
lemma ubdom_lub_eq: assumes "chain Y" 
                    and  "(ubDom\<cdot>(\<Squnion>i. Y i) = ufCompI f1 f2)"
                  shows "\<forall>ia. ubDom\<cdot>(Y ia) = ufCompI f1 f2"
  using assms(1) assms(2) is_ub_thelub ubdom_fix by blast

lemma ubdom_lub_eq2I: assumes "chain Y" 
                    and  "(ubDom\<cdot>(\<Squnion>i. Y i) = cs)"
                  shows "\<forall>ia. ubDom\<cdot>(Y ia) = cs"
  using assms(1) assms(2) is_ub_thelub ubdom_fix by blast

    
subparagraph \<open>dom\<close>

  
lemma ufCompH_dom [simp]: assumes "ubDom\<cdot>x = ufCompI f1 f2"
                            and "ubDom\<cdot>ub = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
                          shows "ubDom\<cdot>((ufCompH f1 f2 x)\<cdot>ub) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
proof -
  have f1: "ubDom\<cdot>(f1 \<rightleftharpoons> ((x \<uplus> ub)  \<bar> ufDom\<cdot>f1)) = ufRan\<cdot>f1"
    by (simp add: Int_absorb1 assms(1) assms(2) sup_commute sup_left_commute ubrestrict_dom ubunion_dom ufCompI_def ufran_2_ubdom2)
  have f2: "ubDom\<cdot>(f2 \<rightleftharpoons> ((x \<uplus> ub)  \<bar> ufDom\<cdot>f2)) = ufRan\<cdot>f2"
    by (simp add: Int_absorb1 assms(1) assms(2) le_supI1 ubrestrict_dom ubunion_dom ufCompI_def ufran_2_ubdom2)
  show ?thesis
    apply (simp add: ufCompH_def)
    apply (simp add: ubunion_dom)
    by (simp add: f1 f2)
qed

  
paragraph \<open>commu\<close>  

(*
lemma ufcomph_commu: assumes  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
                       and "ubDom\<cdot>ub = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
                       and "ubDom\<cdot>x = ufCompI f1 f2"
                     shows "(ufCompH f1 f2 x)\<cdot>ub = (ufCompH f2 f1 x)\<cdot>ub"
  apply (simp add: ufCompH_def)
  by (rule ubunion_commutative)
*)
  
  
subsubsection \<open>iterate ufCompH\<close>  

  
(* lub equalities *)
lemma iter_ufCompH_cont[simp]: "cont (\<lambda>x. iter_ufCompH f1 f2 i x)"
  by simp                                      
    
lemma iter_ufCompH_mono[simp]: "monofun (\<lambda>x. iter_ufCompH f1 f2 i x)"
  by (simp add: cont2mono)
    
lemma iter_ufCompH_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_ufCompH f1 f2 i) x) \<sqsubseteq> ((iter_ufCompH f1 f2 i) y)"
  using assms monofun_def by fastforce

lemma iter_ufCompH_chain[simp]: assumes "ubDom\<cdot>x = ufCompI f1 f2"
  shows "chain (\<lambda> i. iter_ufCompH f1 f2 i x)"
  by (simp add: assms ub_iterate_chain ubdom_least_cs)
    
lemma iter_ufCompH_dom[simp]: assumes "ubDom\<cdot>x = ufCompI f1 f2" 
  shows "ubDom\<cdot>(iter_ufCompH f1 f2 i x) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
  by (simp add: assms iter_ubfix2_dom ubdom_least_cs)
(*
lemma iter_ufcomph_commu: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
                           and "ubDom\<cdot>tb = ufCompI f1 f2" 
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
*)
    
    
subsubsection \<open>lub iterate ufCompH\<close> 
  
  
lemma lub_iter_ufCompH_dom[simp]: assumes "ubDom\<cdot>x = ufCompI f1 f2" 
  shows "ubDom\<cdot>(\<Squnion>i. iter_ufCompH f1 f2 i x) = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
proof -
  have "ubfun_io_eq (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)"
    by (meson assms ubdom_least_cs ufCompH_dom)
  then show ?thesis
    by (metis ubFix_def ubfix_dom)
qed

  
subsubsection \<open>General Comp\<close>
  
  
(* ufComp is a cont function *)
lemma ufcomp_cont[simp]: 
  shows "cont (\<lambda> x. (ubDom\<cdot>x = ufCompI f1 f2) \<leadsto> ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) )"
proof (subst ubfix_contI2, simp_all)
  fix x:: "'a"
  assume x_ubDom: "ubDom\<cdot>x = ufCompI f1 f2"
  have f4: "ubDom\<cdot>(x \<uplus> ubLeast (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)\<bar>UFun.ufDom\<cdot>f1) = ufDom\<cdot>f1"
    apply (simp add: ubunion_restrict ubunion_dom ubrestrict_dom)
    using ubdom_least_cs ufCompI_def x_ubDom by fastforce
  have f5: "ubDom\<cdot>(x \<uplus> ubLeast (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)\<bar>UFun.ufDom\<cdot>f2) = ufDom\<cdot>f2"
    apply (simp add: ubunion_restrict ubunion_dom ubrestrict_dom)
    using ubdom_least_cs ufCompI_def x_ubDom by fastforce
  show " ubfun_io_eq (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)"
    apply (simp add: ufCompH_def)
    by (simp add: f4 f5 ubunion_dom ufran_2_ubdom2)
qed

(* helper lemma for  ufWell proof of ufComp *)
lemma ufcomp_well_h: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" 
  and "ubDom\<cdot>x = ufCompI f1 f2" shows  "ubDom\<cdot>(ubFix (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)) = ufCompO f1 f2"
    by (simp add: assms(2) ubdom_least_cs ubfix_dom ufCompO_def)

(* ufcomp produce a ufwell component*)
lemma ufcomp_well[simp]: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" 
  shows "ufWell (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = ufCompI f1 f2) \<leadsto> ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
  apply (simp add: ufWell_def)
  apply (rule conjI)
   apply (rule_tac x = "ufCompI f1 f2" in exI)
   apply (simp add: domIff)
  apply (rule_tac x = "ufCompO f1 f2" in exI) 
  by (smt assms option.distinct(1) option.sel ran2exists ufcomp_well_h)

lemma ufcomp_repabs: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "Rep_cufun (ufComp f1 f2) = (\<lambda>a. (ubDom\<cdot>a = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 a)(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
  apply (simp add: ufComp_def)
  apply (subst rep_abs_cufun)
    apply (simp, simp add: assms)
  by auto

lemma ufcomp_dom: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufDom\<cdot>(ufComp f1 f2) =  ufCompI f1 f2"
  apply (simp add: ufDom_def)
  apply (simp add: ufComp_def)
  apply (subst rep_abs_cufun)
    apply (simp, simp add: assms)
  apply (simp add: domIff)
  by (meson someI_ex ubdom_ex)

lemma ubDom_h: " ubDom\<cdot>(SOME b::'a. ubDom\<cdot>b = cs) = cs"
proof -
  obtain x::"'a" where x_def: "ubDom\<cdot>x = cs" using ubdom_ex by auto
  show ?thesis
    by (meson x_def someI_ex)
qed

lemma ufcomp_ran: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufRan\<cdot>(ufComp f1 f2) = ufCompO f1 f2"
proof -
  obtain x where x_def: "x \<in> (ran (Rep_cufun (ufComp f1 f2)))"
    using ufran_not_empty by blast
  have f2: "ubDom\<cdot>x = ufCompO f1 f2"
    by (metis (mono_tags, lifting) assms option.distinct(1) ran2exists ufcomp_well_h ufcomp_repabs ufran_2_ubdom x_def)
  have f3: "ufRan\<cdot>(ufComp f1 f2) = ubDom\<cdot>x"
    by (meson ran2exists ufran_2_ubdom x_def)
  show ?thesis
    by (simp add: f2 f3)
qed

(* parcomp *)
subsection\<open>Parallel Composition\<close>
  
  
lemma ufparcomp_cont: "cont (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))))"
  sorry

lemma ufparcomp_well: "ufWell (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))))"
  sorry

lemma ufparcomp_repabs: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  shows "Rep_cufun (ufParComp f1 f2) = (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))))"
  apply (simp add: ufParComp_def)
  apply (subst rep_abs_cufun)
    apply (simp add: ufparcomp_cont)
   apply (simp add: ufparcomp_well)
  by auto

lemma ufparcom_dom: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  shows "ufDom\<cdot>(ufParComp f1 f2) = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
  apply (simp add: ufDom_def ufParComp_def)
  apply (subst rep_abs_cufun)
  apply (metis (no_types) ufdom_insert ufparcomp_cont)
   apply (metis (no_types) ufdom_insert ufparcomp_well)
  apply (simp add: domIff)
  by (simp add: ubDom_h)

lemma ufparcomp_well_h2: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubDom\<cdot>x =  ufDom\<cdot>f1 \<union> ufDom\<cdot>f2" shows  "ubDom\<cdot>((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2))) =  ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
  apply (simp add: ubunion_dom)
  by (simp add: assms(2))

lemma ufparcom_ran: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  shows "ufRan\<cdot>(ufParComp f1 f2) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
proof -
  obtain x where x_def: "x \<in> (ran (Rep_cufun (ufParComp f1 f2)))"
    using ufran_not_empty by blast
  have f2: "ufRan\<cdot>(ufParComp f1 f2) = ubDom\<cdot>x"
    by (meson ran2exists ufran_2_ubdom x_def)
  have f3: "ubDom\<cdot>x = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    by (metis (no_types, lifting) assms f2 option.sel ubdom_least_cs ufparcomp_well_h2 ufparcom_dom ufparcomp_repabs ufran_least)
  show ?thesis
    by (simp add: f2 f3)
qed
  

subsection\<open>Serial Composition\<close>
  
  
lemma ufSerComp_cont: "cont (\<lambda> x. (ubDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
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

lemma ufSerComp_well: assumes "ufRan\<cdot>f1 = ufDom\<cdot>f2" shows "ufWell (\<Lambda> x. (ubDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  apply(simp add: ufWell_def)
  apply rule
proof -
  { fix aa :: "channel set \<Rightarrow> 'a"
    { assume "ubDom\<cdot>(aa (UFun.ufDom\<cdot>f1)) = UFun.ufDom\<cdot>f1"
      { assume "\<exists>C. aa C \<in> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)) \<and> ubDom\<cdot>(aa C) = C"
        then have "\<exists>C. cont (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)) \<and> aa C \<in> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)) \<and> ubDom\<cdot>(aa C) = C"
          by (simp add: ufSerComp_cont)
        then have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<and> ubDom\<cdot>(aa C) = C"
          by auto }
      then have "(\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<and> ubDom\<cdot>(aa C) = C) \<or> (\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> ubDom\<cdot>(aa C) \<noteq> UFun.ufDom\<cdot>f1)"
        by fastforce }
    moreover
    { assume "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> ubDom\<cdot>(aa C) \<noteq> UFun.ufDom\<cdot>f1"
      then have "\<exists>C. aa C \<notin> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)) \<and> ubDom\<cdot>(aa C) \<noteq> C"
        by (smt domIff)
      then have "\<exists>C. cont (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)) \<and> aa C \<notin> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)) \<and> ubDom\<cdot>(aa C) \<noteq> C"
        using ufSerComp_cont by auto
      then have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<and> ubDom\<cdot>(aa C) = C"
        by auto }
    ultimately have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a))) \<and> ubDom\<cdot>(aa C) = C"
      by blast }
  then show "\<exists>C. \<forall>a. (a \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> a)))) = (ubDom\<cdot>a = C)"
    by meson
next
  have f1: "\<forall>b::'c. b \<in> ran (\<lambda>x::'a. (ubDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)) \<longrightarrow> ubDom\<cdot>b = ufRan\<cdot>f2"
    by (smt CollectD assms option.distinct(1) option.sel ran_def ufran_2_ubdom2)
  show "\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun (\<Lambda> (x::'a). (ubDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))) \<longrightarrow> (ubDom\<cdot>b = Out)"
    apply(simp add: ufSerComp_cont)
    by (simp add: f1)
qed

lemma ufSerComp_dom: assumes "sercomp_well f1 f2"
  shows "ufDom\<cdot>(ufSerComp f1 f2) = ufDom\<cdot>f1"
  apply(subst ufDom_def, simp add: ufSerComp_def)
  apply(subst rep_abs_cufun, simp add: ufSerComp_cont)
   apply (simp add: assms ufSerComp_well)
  by (smt domIff rep_ufun_well tfl_some ubdom_least_cs ufWell_def ufdom_2ufundom ufunLeastIDom)
  
lemma ufSerComp_ran: assumes "sercomp_well f1 f2"
  shows "ufRan\<cdot>(ufSerComp f1 f2) = ufRan\<cdot>f2"
proof - 
  have f1: "ufRan\<cdot>f1 = ufDom\<cdot>f2"
    using assms by blast
  have f2: "\<And>b. ubDom\<cdot>b=ufDom\<cdot>f1 \<longrightarrow> (the ((\<lambda>x::'a. (ubDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)) b)) \<in> ran (\<lambda>x::'a. (ubDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>(f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
    by (smt option.sel ranI)
  have f3: "\<And>b. ubDom\<cdot>b=ufDom\<cdot>f1 \<longrightarrow> ubDom\<cdot>(the ((\<lambda>x::'a. (ubDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)) b)) = ufRan\<cdot>f2"
    by (simp add: assms ufran_2_ubdom2)
  show ?thesis
    apply(subst ufRan_def, simp add: ufSerComp_def)
    apply(subst rep_abs_cufun, simp add: ufSerComp_cont)
     apply (simp add: assms ufSerComp_well)
     using f2 f3 (* proof found by sledgehammer *)
     oops 
    
lemma ufSerComp_repAbs: assumes "sercomp_well f1 f2"
  shows "Rep_cufun (ufSerComp f1 f2) = (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  apply(simp add: ufSerComp_def, subst rep_abs_cufun)
    apply (simp add: ufSerComp_cont)
   apply (simp add: assms ufSerComp_well)
  by auto 
    
lemma ufSerComp_asso: assumes "sercomp_well f1 f2" and "sercomp_well f2 f3" 
  shows "(ufSerComp f1 (ufSerComp f2 f3)) = (ufSerComp (ufSerComp f1 f2) f3)"
proof - 
  have f1: "UFun.ufDom\<cdot>(Abs_cufun(\<lambda>x::'a. (ubDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))) = UFun.ufDom\<cdot>f1"
    using ufSerComp_def ufSerComp_dom assms(1)
    (* proof found by sledgehammer *)
    sorry
  have f2: "\<And>x. ubDom\<cdot>x = UFun.ufDom\<cdot>f1 \<longrightarrow> ubDom\<cdot>(f1 \<rightleftharpoons> x) = UFun.ufDom\<cdot>f2"
    by (simp add: assms(1) ufran_2_ubdom2)
  show ?thesis
    apply(simp add: ufSerComp_def)
    apply(subst rep_abs_cufun)
    apply(simp add: ufSerComp_cont, simp add: ufSerComp_well assms)
    apply(subst rep_abs_cufun, simp add: ufSerComp_cont, simp add: ufSerComp_well assms)
    apply(subst f1)
    using f2 oops (* proof found by sledgehammer *) 
      

subsection \<open>Feedback\<close>    

  
lemma ufFeedH_cont: "cont (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"
  using cont_compose by force   
   
lemma ufFeedH_cont2: "cont (ufFeedH f)"
proof - 
  have f1: "ufFeedH f = (\<lambda>x. (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f)))))"
    using ufFeedH_def by auto
  have f2: "cont (\<lambda>x. (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f)))))"
    using ufFeedH_cont cont_compose   
    sorry
  show ?thesis
    apply(subst f1)
    by(simp add: f2)
qed

lemma ufFeedH_dom [simp]: assumes "ubDom\<cdot>x = ufDom\<cdot>f - ufRan\<cdot>f" 
                           and "ubDom\<cdot>sb = ufRan\<cdot>f"
shows "ubDom\<cdot>((ufFeedH f x)\<cdot>sb) = (ufRan\<cdot>f)"
  apply(simp add: ufFeedH_def ufFeedH_cont)
  by (simp add: Int_commute assms(1) assms(2) ubrestrict_dom ubunion_dom ufran_2_ubdom2)
    
lemma ufFeedbackComp_cont: "cont (\<lambda> sb. (ubDom\<cdot>sb = (ufDom\<cdot>f - ufRan\<cdot>f)) \<leadsto> (ubFix (ufFeedH f sb) (ufRan\<cdot>f)))"
  apply(rule ubfix_contI2)
   apply (simp add: ufFeedH_cont2)
   apply (simp add: ubdom_least_cs)
    by simp
    
lemma ufFeedbackComp_well: "ufWell (\<Lambda> sb. (ubDom\<cdot>sb = (ufDom\<cdot>f - ufRan\<cdot>f)) \<leadsto> (ubFix (ufFeedH f sb) (ufRan\<cdot>f)))"
  apply(simp add: ufWell_def)
  apply rule
proof -
  { fix aa :: "channel set \<Rightarrow> 'a"
    have "ubDom\<cdot>(aa (UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)) = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f \<or> (\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> ubDom\<cdot>(aa C) \<noteq> UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)"
      by metis
    moreover
    { assume "ubDom\<cdot>(aa (UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)) = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f"
      moreover
      { assume "\<exists>C. aa C \<in> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)) \<and> ubDom\<cdot>(aa C) = C"
        then have "\<exists>C. cont (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)) \<and> aa C \<in> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)) \<and> ubDom\<cdot>(aa C) = C"
          using ufFeedbackComp_cont by blast
        then have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<and> ubDom\<cdot>(aa C) = C"
          by auto }
      moreover
      { assume "\<exists>u. UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f = UFun.ufDom\<cdot>u - UFun.ufRan\<cdot>u \<and> aa (UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f) \<notin> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>u - UFun.ufRan\<cdot> u)\<leadsto>ubFix (ufFeedH u a) (UFun.ufRan\<cdot>u))"
        then have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> ubDom\<cdot>(aa C) \<noteq> UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f"
          by (smt domIff option.distinct(1)) }
      ultimately have "(\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<and> ubDom\<cdot>(aa C) = C) \<or> (\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> ubDom\<cdot>(aa C) \<noteq> UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)"
        by blast }
    moreover
    { assume "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> ubDom\<cdot>(aa C) \<noteq> UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f"
      then have "\<exists>C. aa C \<notin> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)) \<and> ubDom\<cdot>(aa C) \<noteq> C"
        by (smt domIff)
      then have "\<exists>C. cont (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)) \<and> aa C \<notin> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)) \<and> ubDom\<cdot>(aa C) \<noteq> C"
        using ufFeedbackComp_cont by blast
      then have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<and> ubDom\<cdot>(aa C) = C"
        by auto }
    ultimately have "\<exists>C. ubDom\<cdot>(aa C) \<noteq> C \<and> aa C \<notin> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<or> aa C \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) \<and> ubDom\<cdot>(aa C) = C"
      by fastforce }
  then show "\<exists>C. \<forall>a. (a \<in> dom (Rep_cfun (\<Lambda> a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f)))) = (ubDom\<cdot>a = C)"
    by meson
next
  show "\<exists>Out::channel set.
       \<forall>b::'a. b \<in> ran (Rep_cfun (\<Lambda> (sb::'a). (ubDom\<cdot>sb = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f sb) (UFun.ufRan\<cdot>f))) \<longrightarrow> ubDom\<cdot>b = Out"
    apply(simp add: ufFeedbackComp_cont)
    by (smt option.distinct(1) option.sel ran2exists ran_def ubdom_least_cs ubfix_dom ufFeedH_dom)
qed
  
lemma ufFeedbackComp_dom: "ufDom\<cdot>(ufFeedbackComp f) = ufDom\<cdot>f - ufRan\<cdot>f"
  apply(subst ufDom_def , simp add:ufFeedbackComp_def)
  apply(subst rep_abs_cufun, simp add: ufFeedbackComp_cont)
   apply(simp add: ufFeedbackComp_well)
  proof -
    have f1: "\<And>u. UFun.ufDom\<cdot> (Abs_cufun (\<lambda>a. (ubDom\<cdot>(a::'a) = UFun.ufDom\<cdot>u - UFun.ufRan\<cdot> u)\<leadsto>ubFix (ufFeedH u a) (UFun.ufRan\<cdot>u))) = UFun.ufDom\<cdot>u - UFun.ufRan\<cdot>u"
      by (simp add: ufFeedbackComp_cont ufFeedbackComp_well ufun_ufdom_abs)
    have "\<And>f. \<not> cont f \<or> \<not> ufWell (Abs_cfun f) \<or> ubDom\<cdot>(SOME a. a \<in> dom f) = UFun.ufDom\<cdot>(Abs_cufun f::'a \<Rrightarrow> 'a)"
      by (simp add: rep_abs_cufun ufdom_insert)
    then show "ubDom\<cdot> (SOME a. a \<in> dom (\<lambda>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot> f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f))) = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f"
      using f1 ufFeedbackComp_cont ufFeedbackComp_well by blast
  qed
    
lemma ufFeedbackComp_ran: "ufRan\<cdot>(ufFeedbackComp f) = ufRan\<cdot>f"
proof - 
  have f2: "\<And>b. ubDom\<cdot>b=ufDom\<cdot>f - ufRan\<cdot>f \<longrightarrow> (the ((\<lambda>sb::'a. (ubDom\<cdot>sb = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f sb) (UFun.ufRan\<cdot>f)) b)) \<in> ran (\<lambda>sb::'a. (ubDom\<cdot>sb = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f sb) (UFun.ufRan\<cdot>f))"
  proof -
    fix b :: 'a
    have "\<exists>a. (ubDom\<cdot>a = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f a) (UFun.ufRan\<cdot>f) = (ubDom\<cdot>b = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f b) (UFun.ufRan\<cdot>f)"
      by blast
    then show "(ubDom\<cdot>b = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f) \<longrightarrow> (the ((\<lambda>sb::'a. (ubDom\<cdot>sb = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f sb) (UFun.ufRan\<cdot>f)) b)) \<in> ran (\<lambda>sb::'a. (ubDom\<cdot>sb = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f sb) (UFun.ufRan\<cdot>f))"
      using ranI by force
  qed
  then have f3: "\<And>b. ubDom\<cdot>b=ufDom\<cdot>f - ufRan\<cdot>f \<longrightarrow> ubDom\<cdot>(the ((\<lambda>sb::'a. (ubDom\<cdot>sb = UFun.ufDom\<cdot>f - UFun.ufRan\<cdot>f)\<leadsto>ubFix (ufFeedH f sb) (UFun.ufRan\<cdot>f)) b)) = ufRan\<cdot>f"
     by (smt option.distinct(1) option.sel ran2exists ubdom_least_cs ubfix_dom ufFeedH_dom)
  show ?thesis
    apply(subst ufRan_def, simp add: ufFeedbackComp_def)
    apply(subst rep_abs_cufun, simp add:ufFeedbackComp_cont, simp add: ufFeedbackComp_well)
    using f2 f3 ubDom_h ran_def (* proof found *)
    sorry
qed
  

subsection \<open>Equality\<close>

(* ufcomp ufsercomp  *)

lemma ufcomph_insert: "ufCompH f1 f2 x\<cdot>z = ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2)))"
  by (simp add: ufCompH_def)

lemma sercomp_dom_f1: assumes "sercomp_well f1 f2"
                      and "ubDom\<cdot>tb = ufCompI f1 f2"
                    shows "ubDom\<cdot>(f1\<rightleftharpoons>(tb\<bar>(ufDom\<cdot>f1))) = ufRan\<cdot>f1"
proof -
  have "ufDom\<cdot>f1 = ufCompI f1 f2"
    using assms(1) ufCompI_def by fastforce
  then show ?thesis
    by (simp add: assms(2) ubrestrict_dom ufran_2_ubdom2)
qed

lemma sercomp_dom_f12: assumes "sercomp_well f1 f2"
  shows "ufDom\<cdot>f1 \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) = {}"
  using assms by blast

lemma ubunion_restrict3 [simp]: assumes "(ubDom\<cdot>y)\<inter>(ubDom\<cdot>x) = {}" 
  shows "(x\<uplus>y) \<bar> ubDom\<cdot>x = x"
  by (simp add: assms ubrestrict_dom_id ubunion_restrict_R)

lemma sercomp_iter_serial_res_f1: assumes "sercomp_well f1 f2"
                                  and "ubDom\<cdot>x = ufCompI f1 f2"
                                shows "(iter_ufCompH f1 f2 (Suc (Suc i)) x) \<bar> (ufRan\<cdot>f1) = (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1))"
  by (smt assms(1) assms(2) inf_sup_absorb inf_sup_aci(1) iter_ufCompH_dom iterate_Suc 
          sercomp_dom_f1 sercomp_dom_f12 ubrestrict_twice ubunion_restrict_R ubunion_restrict2 
          ubunion_restrict3 ufran_2_ubdom2 ufcomph_insert ubrestrict_dom)

lemma sercomp_iter_serial: assumes "sercomp_well f1 f2"
                              and "ubDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ufCompH f1 f2 (Suc (Suc (Suc i))) x) = 
    (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))"
proof -
  have "ubDom\<cdot>(f1 \<rightleftharpoons> ubLeast (UFun.ufDom\<cdot>f1)) \<inter> UFun.ufDom\<cdot>f1 = UFun.ufDom\<cdot>f1 \<inter> UFun.ufRan\<cdot>f1"
    by (simp add: inf_commute ufran_least)
then have f1: "ubDom\<cdot>(f1 \<rightleftharpoons> ubLeast (UFun.ufDom\<cdot>f1)) \<inter> UFun.ufDom\<cdot>f1 = {}"
by (metis assms(1))
  have f2: "ubDom\<cdot>(f2 \<rightleftharpoons> ubLeast (UFun.ufDom\<cdot>f2)) \<inter> UFun.ufDom\<cdot>f2 = UFun.ufDom\<cdot>f2 \<inter> UFun.ufRan\<cdot>f2"
    by (simp add: inf_commute ufran_least)
  have "iter_ubfix2 (ufCompH f1 f2) (Suc (Suc (Suc i))) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x\<bar>UFun.ufRan\<cdot>f1 = f1 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f1"
    using assms(1) assms(2) sercomp_iter_serial_res_f1 by blast
  then show ?thesis
    by (smt assms(1) assms(2) inf_sup_aci(1) iter_ufCompH_dom iterate_Suc sercomp_dom_f1 sercomp_dom_f12 sercomp_iter_serial_res_f1 ubrestrict_twice
          ubrestrict_dom ubunion_restrict2 ubunion_restrict_R ufcomph_insert)
qed
 
lemma sercomp_iter_max_in_chain: assumes "sercomp_well f1 f2"
                                 and "ubDom\<cdot>x = ufCompI f1 f2"
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
    by (metis assms(1) assms(2) sercomp_iter_serial)
  qed

lemma ufcomp_sercomp_lub_const1: assumes "sercomp_well f1 f2"
                                   and "ubDom\<cdot>x = ufCompI f1 f2"
                                 shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = iter_ufCompH f1 f2 (Suc (Suc (Suc 0))) x"  
  using assms(1) assms(2) iter_ufCompH_chain maxinch_is_thelub sercomp_iter_max_in_chain by blast

lemma ufcomp_sercomp_lub_const2: assumes "sercomp_well f1 f2"
                                   and "ubDom\<cdot>x = ufCompI f1 f2"
                                 shows "(\<Squnion>i. iter_ufCompH f1 f2 i x) = (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))"
  by (metis assms(1) assms(2) sercomp_iter_serial ufcomp_sercomp_lub_const1)

lemma ufcomp_serial_iterconst_eq: assumes "sercomp_well f1 f2"
  shows "(\<lambda> x. (ubDom\<cdot>x = ufCompI f1 f2) \<leadsto> (\<Squnion>i. iter_ufCompH f1 f2 i x) )
        = (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))))"
proof -
  have f1: " ufCompI f1 f2 = ufDom\<cdot>f1"
    using assms ufCompI_def by blast
  have  "\<forall>x. (ubDom\<cdot>x \<noteq> ufCompI f1 f2)  \<or> 
        (Some ((\<Squnion>i. iter_ufCompH f1 f2 i x))
        = Some ((f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f1)))))"
      by (metis assms ufcomp_sercomp_lub_const2)
    then show ?thesis
      using f1 by auto
qed

  
(* ufcomp ufparcomp  *)
(*  *)
lemma parcomp_dom_ran_empty: assumes "ufCompL f1 f2 = {}"
  shows "(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) \<inter> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) = {}"
  by (metis assms inf_commute ufCompL_def)

(*  *)
lemma ufComp_parallel :assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ubfix2 (ufCompH f1 f2) (Suc (Suc i)) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x)
                  =(f1\<rightleftharpoons>(x \<bar>ufDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>ufDom\<cdot>f2))" (is "?L = ?R")
  by (smt assms(1) assms(2) bot_eq_sup_iff inf_sup_aci(1) inf_sup_distrib2 iter_ufCompH_dom iterate_Suc ubunion_restrict_R ufCompL_def ufcomph_insert)

(* the third iteration returns the fixpoint  *)
lemma ufComp_parallel_max: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubDom\<cdot>x = ufCompI f1 f2"
shows "max_in_chain (Suc (Suc 0)) (\<lambda>i. iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
  by (metis (no_types, lifting) Suc_le_D Suc_le_lessD assms(1) assms(2) le_simps(2) max_in_chainI ufComp_parallel)

(* the lub of ubFix is the parcomp *)
lemma ufComp_parallel_itconst1: assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubDom\<cdot>x = ufCompI f1 f2"
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
    using assms f1 ufcomp_dom ufparcom_dom by blast
  have "\<And> ub. ubDom\<cdot>ub \<noteq> UFun.ufDom\<cdot>f1 \<union> UFun.ufDom\<cdot>f2 \<or> ubFix (ufCompH f1 f2 ub) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) =
    (f1 \<rightleftharpoons> ub\<bar>UFun.ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> ub\<bar>UFun.ufDom\<cdot>f2)"
    by (simp add: assms f1 ubFix_def ufComp_parallel_itconst1)
  then have "(\<lambda>x::'a. (ubDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)) =
    (\<lambda>x::'a. (ubDom\<cdot>x = UFun.ufDom\<cdot>f1 \<union> UFun.ufDom\<cdot>f2)\<leadsto>(f1 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> x\<bar>UFun.ufDom\<cdot>f2))"
    using f1 by auto
  then show ?thesis
    by (simp add: ufComp_def ufParComp_def)
qed


subsection \<open>ufLeast\<close>
  

(* ufelast if a mono function  *)
lemma ufleast_mono[simp]: "\<And> cin cout. monofun (\<lambda>sb. (ubDom\<cdot>sb = cin)\<leadsto>ubLeast cout)"
  by simp

(* ufleast is a cont function *)
lemma ufleast_cont[simp]: "\<And> cin cout. cont (\<lambda>sb. (ubDom\<cdot>sb = cin)\<leadsto>ubLeast cout)"
  by simp

(* ufleast produce a ufwell function  *)
lemma ufleast_ufwell[simp]: "\<And> cin cout. ufWell (Abs_cfun (\<lambda>sb. (ubDom\<cdot>sb = cin)\<leadsto>ubLeast cout))"
  apply (simp add: ufWell_def, rule)
   apply (rule_tac x="cin" in exI, simp add: domIff)
  by (smt option.distinct(1) option.sel ran2exists ubdom_least_cs)

(* insert rule of ufleast *)
lemma ufleast_insert:"ufLeast In Out = Abs_ufun (Abs_cfun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>ubLeast Out))"
  by (simp add: ufLeast_def)

(* somwe how ufleast_ufran need this otherwise this cannt be proven with metis  *)
lemma ufleast_rep_abs[simp]: "(Rep_cufun (Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>ubLeast Out))) = (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>ubLeast Out)"
  by simp

(* ufdom of ufleast is the first argument  *)
lemma ufleast_ufdom: "ufDom\<cdot>(ufLeast In Out) = In"
  apply (simp add: ufLeast_def  ufdom_insert domIff)
  by (meson someI_ex ubdom_least_cs)

(* ufran of ufleast is its second argument *)
lemma ufleast_ufRan: "ufRan\<cdot>(ufLeast In Out) = Out"
  by (metis (no_types) option.sel ubdom_least_cs ufleast_insert ufleast_rep_abs ufleast_ufdom ufran_least)

(* ufleast can produce a function smaller or equal other function  *)
lemma ufleast_min: "(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) \<sqsubseteq> uf"
proof (rule ufun_belowI)
  show "ufDom\<cdot>(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) = UFun.ufDom\<cdot>uf"
    by (simp add: ufleast_ufdom)
next
  show "\<And>x. ubDom\<cdot>x = ufDom\<cdot>(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) \<Longrightarrow>
         Rep_cufun (ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf))\<rightharpoonup>x \<sqsubseteq> Rep_cufun uf\<rightharpoonup>x"
    by (metis ufleast_rep_abs option.sel ubdom_least ufLeast_def ufleast_ufdom ufran_2_ubdom2)
qed

  
end