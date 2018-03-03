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
"b1 \<uplus> b2 \<equiv> ubclUnion\<cdot>b1\<cdot>b2"

abbreviation ubclRestrict_abbr :: " 'm \<Rightarrow> channel set \<Rightarrow> 'm" ("(_\<bar>_)" [66,65] 65)
where "b\<bar>cs \<equiv> ubclRestrict cs\<cdot>b"

  
subsection\<open>definitions\<close>  

  
definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'in ufun" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubclDom\<cdot>sb = cin) \<leadsto> ubclLeast cout)"  

definition ufRestrict :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm ufun \<rightarrow> 'm ufun" where
  "ufRestrict In Out \<equiv> (\<Lambda> f. if (ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out) then f else (ufLeast In Out))"

  
subsection\<open>channel sets\<close>

  
text {* the input channels of the composition of f1 and f2 *}
definition ufCompI :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> channel set" where
"ufCompI f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the internal channels of the composition of f1 and f2 *}
definition ufCompL :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> channel set" where
"ufCompL f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the output channels of the composition of f1 and f2 *}
definition ufCompO :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> channel set" where
"ufCompO f1 f2 \<equiv> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* all channels of the composition of f1 and f2  *}
definition ufCompC :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> channel set" where
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

 
definition ufCompH :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> 'm \<Rightarrow> ('m \<rightarrow> 'm)" where
"ufCompH f1 f2 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)))"

abbreviation iter_ufCompH :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> nat \<Rightarrow> 'm  \<Rightarrow> 'm" where
"(iter_ufCompH f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))" 


subsection \<open>composition operators\<close>

definition comp_well :: "('a ufun) \<Rightarrow> ('a ufun) \<Rightarrow> bool" where
"comp_well f1 f2 \<equiv> ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"


definition ufComp :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> 'm ufun" where
"ufComp f1 f2 \<equiv>
let I = ufCompI f1 f2;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)
in Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = I) \<leadsto> ubFix (ufCompH f1 f2 x) Oc))" 


(* parcomp *)
abbreviation parcomp_well :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> bool" where
"parcomp_well f1 f2 \<equiv> (ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"


definition ufParComp :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> 'm ufun" ("_\<parallel>_") where
"ufParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))))"


abbreviation sercomp_well :: "'m ufun \<Rightarrow> 'm ufun \<Rightarrow> bool" where
"sercomp_well f1 f2 \<equiv>  (ufRan\<cdot>f1 = ufDom\<cdot>f2) 
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                        \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})"

definition ufSerComp :: "'m ufun => 'm ufun => 'm ufun"  (infixl " \<circ> " 60) where
"ufSerComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"


definition ufFeedH:: "'m ufun \<Rightarrow> 'm \<Rightarrow> 'm  \<rightarrow> 'm" where
"ufFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"

definition ufFeedbackComp :: "'m ufun \<Rightarrow> 'm ufun" ("\<mu>_" 50) where
"ufFeedbackComp f \<equiv>
let I  = ufDom\<cdot>f - ufRan\<cdot>f;
    C  = ufRan\<cdot>f
in Abs_ufun (Abs_cfun (\<lambda> sb. (ubclDom\<cdot>sb = I) \<leadsto>
    (ubFix (ufFeedH f sb) C)))"  

  
(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)  

  
subsection \<open>ubclLeast\<close>

  
(* ubclLeast is in the same dome as the function f  *)
lemma ufunLeastIDom: "(ubclLeast (ufDom\<cdot>f)) \<in> dom (Rep_cufun f)"
  by (metis rep_ufun_well domD ubcldom_least_cs ufWell_def ufdom_2ufundom)

(* The range of an ufun is equal to the domain of f applied to the least ubundle with domain 
       ufDom f *)
lemma ufran_least: "ufRan\<cdot>f = ubclDom\<cdot>(f\<rightleftharpoons>(ubclLeast (ufDom\<cdot>f)))"
  apply (simp add: ufRan_def)
  by (metis (no_types) domD option.sel ufunLeastIDom ufran_2_ubcldom ufran_insert)

    
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
proof (subst ubfix_contI2, simp_all)
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
lemma ufcomp_well_h: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" 
  and "ubclDom\<cdot>x = ufCompI f1 f2" shows  "ubclDom\<cdot>(ubFix (ufCompH f1 f2 x) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2)) = ufCompO f1 f2"
    by (simp add: assms(2) ubcldom_least_cs ubfix_dom ufCompO_def)

(* ufcomp produce a ufwell component*)
lemma ufcomp_well[simp]: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" 
  shows "ufWell (Abs_cfun (\<lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2) \<leadsto> ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
  apply (simp add: ufWell_def)
  apply (rule conjI)
   apply (rule_tac x = "ufCompI f1 f2" in exI)
   apply (simp add: domIff)
  apply (rule_tac x = "ufCompO f1 f2" in exI) 
  by (smt assms option.distinct(1) option.sel ran2exists ufcomp_well_h)

lemma ufcomp_repabs: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "Rep_cufun (ufComp f1 f2) = (\<lambda>a. (ubclDom\<cdot>a = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 a)(ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
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
  by (meson someI_ex ubcldom_ex)

lemma ubclDom_h: " ubclDom\<cdot>(SOME b::'a. ubclDom\<cdot>b = cs) = cs"
proof -
  obtain x::"'a" where x_def: "ubclDom\<cdot>x = cs" using ubcldom_ex by auto
  show ?thesis
    by (meson x_def someI_ex)
qed

lemma ufcomp_ran: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufRan\<cdot>(ufComp f1 f2) = ufCompO f1 f2"
proof -
  obtain x where x_def: "x \<in> (ran (Rep_cufun (ufComp f1 f2)))"
    using ufran_not_empty by blast
  have f2: "ubclDom\<cdot>x = ufCompO f1 f2"
    by (metis (mono_tags, lifting) assms option.distinct(1) ran2exists ufcomp_well_h ufcomp_repabs ufran_2_ubcldom x_def)
  have f3: "ufRan\<cdot>(ufComp f1 f2) = ubclDom\<cdot>x"
    by (meson ran2exists ufran_2_ubcldom x_def)
  show ?thesis
    by (simp add: f2 f3)
qed

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
               shows "((f1 \<parallel> f2) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(f1 \<parallel> f2))) = (f1 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f2)"
proof -
  have f3: "((ub\<bar>ufDom\<cdot>(f1 \<parallel> f2))\<bar>ufDom\<cdot>f1) = (ub\<bar>ufDom\<cdot>f1)"
    by (metis assms(1) inf.absorb_iff2 sup_ge1 ubclunion_test ufParComp_dom)

  have f4: "(ub\<bar>ufDom\<cdot>(f1 \<parallel> f2))\<bar>ufDom\<cdot>f2 = (ub\<bar>ufDom\<cdot>f2)"
    by (metis assms(1) inf.absorb_iff2 sup.cobounded2 ubclunion_test ufParComp_dom)

  have f1: "ufDom\<cdot>(f1 \<parallel> f2) = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
    by (simp add: assms(1) ufParComp_dom)
  have f2: "ubclDom\<cdot>(ub\<bar>ufDom\<cdot>(f1 \<parallel> f2)) = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
    by (metis Int_absorb1 assms(2) f1 ubclrestrict_ubcldom)

  have f5: "(Rep_cufun (f1 \<parallel> f2)) = ((\<lambda>t. (ubclDom\<cdot>t = ufDom\<cdot>f1 \<union> ufDom\<cdot> f2)\<leadsto>((f1 \<rightleftharpoons> t \<bar> ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> t \<bar> ufDom\<cdot>f2))))"
    by (simp add: assms(1) ufParComp_repAbs)

  then have "Rep_cufun (f1 \<parallel> f2) (ub \<bar> ufDom\<cdot>(f1 \<parallel> f2)) = 
    Some ((f1 \<rightleftharpoons> (ub \<bar> ufDom\<cdot>(f1 \<parallel> f2)) \<bar> ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (ub \<bar> ufDom\<cdot>(f1 \<parallel> f2)) \<bar> ufDom\<cdot>f2))"
    by (simp add: f2)

  then show ?thesis
    by (metis f3 f4 option.sel)
qed

lemma parcomp_func_h2: assumes "parcomp_well f1 f2"
                   and "ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 = ubclDom\<cdot>ub"
               shows "((f1 \<parallel> f2) \<rightleftharpoons> ub) = (f1 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> ub\<bar>ufDom\<cdot>f2)"
  by (metis assms(1) assms(2) inf_idem inf_le2 parcomp_func_h ubclrestrict_dom_id ufParComp_dom)  

lemma ubresrict_dom2: assumes "cs \<subseteq> ubclDom\<cdot>ub"
  shows "ubclDom\<cdot>(ub \<bar> cs) = cs"
  by (simp add: Int_absorb1 assms ubclrestrict_ubcldom)

lemma ufParCompWell_associativity: assumes "parcomp_well f1 f2"
                                   and "parcomp_well f2 f3"
                                   and "parcomp_well f1 f3"                                  
                                 shows "parcomp_well f1 (f2 \<parallel> f3)"
   apply (simp add: ufCompL_def)
   apply (simp_all add: ufParComp_dom ufParComp_ran assms)
  apply (simp_all add: Int_Un_distrib2 Int_Un_distrib)
  by (meson assms(1) assms(2) assms(3) parcomp_well_h1(1) parcomp_well_h1(2) parcomp_well_h2(1) parcomp_well_h2(2))

lemma ufParComp_asso: assumes "parcomp_well f1 f2"
                                   and "parcomp_well f2 f3"
                                   and "parcomp_well f1 f3"                                  
                                 shows "((ufParComp f1 f2) \<parallel> f3) = (f1 \<parallel> ( f2 \<parallel> f3))"
proof-
  have f1: "\<forall>ub. (ubclDom\<cdot>ub \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<or>
            (((f1 \<parallel> f2) \<rightleftharpoons> (ub \<bar>ufDom\<cdot>(f1 \<parallel> f2))) \<uplus> (f3 \<rightleftharpoons> (ub\<bar>ufDom\<cdot>f3)))
          = ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f3)))"
    by (simp add: assms(1) parcomp_func_h)

  have f2: "\<forall>ub. (ubclDom\<cdot>ub \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<or>
            ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> ((f2 \<parallel> f3) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(f2 \<parallel> f3))))
          = ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f2)) \<uplus> (f3 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f3)))"
    using ubclunion_asso
    by (smt assms(1) assms(2) assms(3) le_sup_iff parcomp_func_h sup_ge1 sup_ge2 ubresrict_dom2 ufran_2_ubcldom2)

  have f3: "\<forall>ub. (ubclDom\<cdot>ub \<noteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufDom\<cdot>f3) \<or>
            (((f1 \<parallel> f2) \<rightleftharpoons> (ub \<bar>ufDom\<cdot>(f1 \<parallel> f2))) \<uplus> (f3 \<rightleftharpoons> (ub\<bar>ufDom\<cdot>f3))) 
          = ((f1 \<rightleftharpoons> (ub \<bar>ufDom\<cdot>f1)) \<uplus> ((f2 \<parallel> f3) \<rightleftharpoons> (ub\<bar>ufDom\<cdot>(f2 \<parallel> f3))))"
    using f1 f2 by auto

  have f4: "(\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(f1 \<parallel> f2) \<union> ufDom\<cdot>f3) \<leadsto> (((f1 \<parallel> f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(f1 \<parallel> f2))) \<uplus> (f3 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f3))))
          = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>(f2 \<parallel> f3)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((f2 \<parallel> f3) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(f2 \<parallel> f3)))))"
    by (metis (no_types, hide_lams) Un_assoc assms(1) assms(2) f3 ufParComp_dom)

  then have f5:"Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(f1 \<parallel> f2) \<union> ufDom\<cdot>f3) \<leadsto> (((f1 \<parallel> f2) \<rightleftharpoons> (x \<bar>ufDom\<cdot>(f1 \<parallel> f2))) \<uplus> (f3 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f3))))
              = Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>(f2 \<parallel> f3)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> ((f2 \<parallel> f3) \<rightleftharpoons> (x\<bar>ufDom\<cdot>(f2 \<parallel> f3)))))"
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
  have f1: "\<forall>b::'a. b \<in> ran (\<lambda>x::'a. (ubclDom\<cdot>x = UFun.ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)) \<longrightarrow> ubclDom\<cdot>b = ufRan\<cdot>f2"
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

lemma ufSerComp_apply: assumes "sercomp_well f1 f2" and "ubclDom\<cdot>x = ufDom\<cdot>(f1\<circ>f2)"
  shows "(f1\<circ>f2)\<rightleftharpoons>x = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
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
  have f25: "\<forall> sb. (ubclDom\<cdot>sb \<noteq> ufDom\<cdot>f1) \<or> (f3 \<rightleftharpoons> ((f1 \<circ> f2) \<rightleftharpoons> sb)) = ((f2 \<circ> f3) \<rightleftharpoons> (f1 \<rightleftharpoons> sb))"
  proof -
    have f1: "ufDom\<cdot>(f1 \<circ> f2) = ufDom\<cdot>f1"
      by (metis (no_types) assms(1) ufSerComp_dom)
    have f2: "\<forall>a u. ubclDom\<cdot>(a::'a) \<noteq> ufDom\<cdot>u \<or> ubclDom\<cdot>(u \<rightleftharpoons> a) = ufRan\<cdot>u"
      by (meson ufran_2_ubcldom2)
    have "ufDom\<cdot>(f2 \<circ> f3) = ufRan\<cdot>f1"
      by (metis (full_types) assms(1) assms(2) ufSerComp_dom)
    then show ?thesis
      using f2 f1 by (metis (no_types) assms(1) assms(2) ufSerComp_apply)
  qed
  then have f29: "(\<lambda>x. (ubclDom\<cdot>x =  ufDom\<cdot>(f1 \<circ> f2))\<leadsto>f3 \<rightleftharpoons> ((f1 \<circ> f2) \<rightleftharpoons> x))
              =  (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f2 \<circ> f3) \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    by (metis (no_types, hide_lams) assms(1) assms(2) ufSerComp_dom)
  then have f30: "Abs_cufun (\<lambda>x. (ubclDom\<cdot>x =  ufDom\<cdot>(f1 \<circ> f2))\<leadsto>f3 \<rightleftharpoons> ((f1 \<circ> f2) \<rightleftharpoons> x))
              =  Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>(f2 \<circ> f3) \<rightleftharpoons> (f1 \<rightleftharpoons> x))"
    by simp
  then show ?thesis
      by (metis (no_types) f30 ufSerComp_def)
  qed
(*
proof -
  have f1: "sercomp_well f1 (ufSerComp f2 f3)" and f2: "sercomp_well (ufSerComp f1 f2) f3"
    by (metis assms(1) assms(2) assms(3) ufSerComp_dom ufSerComp_ran) +
  have f3: "ufDom\<cdot>(f1\<circ>(f2\<circ>f3)) = ufDom\<cdot>((f1\<circ>f2)\<circ>f3)"
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


subsection \<open>Feedback\<close>    

  
lemma ufFeedH_cont1: "cont (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"
  using cont_compose by force   

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

(* ufcomp ufsercomp  *)

lemma ufcomph_insert: "ufCompH f1 f2 x\<cdot>z = ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> ufDom\<cdot>f2)))"
  by (simp add: ufCompH_def)

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

lemma ubclunion_restrict3 [simp]: assumes "(ubclDom\<cdot>y)\<inter>(ubclDom\<cdot>x) = {}" 
  shows "(x\<uplus>y) \<bar> ubclDom\<cdot>x = x"
  by (simp add: assms ubclrestrict_dom_id ubclunion_restrict_R)

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

  
(* ufcomp ufparcomp  *)

(*  *)
lemma ufComp_parallel :assumes "(ufCompL f1 f2 = {}) \<and> (ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"
  and "ubclDom\<cdot>x = ufCompI f1 f2"
  shows "(iter_ubfix2 (ufCompH f1 f2) (Suc (Suc i)) (UFun.ufRan\<cdot>f1 \<union> UFun.ufRan\<cdot>f2) x)
                  =(f1\<rightleftharpoons>(x \<bar>ufDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>ufDom\<cdot>f2))" (is "?L = ?R")
  by (smt assms(1) assms(2) bot_eq_sup_iff inf_sup_aci(1) inf_sup_distrib2 iter_ufCompH_dom iterate_Suc ubclunion_restrict_R ufCompL_def ufcomph_insert)

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

instantiation ufun:: (ubcl_comp) ufuncl_comp
begin

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


instance 
  apply intro_classes
             apply (simp add: inf_sup_aci(1) ufcomp_L_commu ufunclParCompWell_ufun_def)
            apply (simp add: comp_well_def inf_sup_aci(1) ufunclCompWell_ufun_def)
           apply (simp add: UFun_Comp.ufunclParComp_ufun_def ufParComp_dom ufclDom_ufun_def ufunclParCompWell_ufun_def)
          apply (simp add: UFun_Comp.ufunclParComp_ufun_def ufParComp_ran ufclRan_ufun_def ufunclParCompWell_ufun_def)
         apply (simp add: ufunclSerCompWell_ufun_def ufclDom_ufun_def)
         using ufSerComp_dom ufunclSerComp_ufun_def apply auto[1]
               apply (simp add: ufunclSerCompWell_ufun_def ufclRan_ufun_def ufunclSerComp_ufun_def)
         using ufSerComp_ran apply auto[1]
                apply (simp add: ufFeedbackComp_dom ufclDom_ufun_def ufclRan_ufun_def ufunclFeedbackComp_ufun_def)
               apply (simp add: UFun_Comp.ufunclFeedbackComp_ufun_def ufFeedbackComp_ran ufclRan_ufun_def)
              apply (simp add: UFun_Comp.ufunclCompWell_ufun_def UFun_Comp.ufunclComp_ufun_def comp_well_def inf_sup_aci(1) ufcomp_commu)
            apply (metis ufParComp_commutativity ufunclParCompWell_ufun_def ufunclParComp_ufun_def)
           apply (simp add: UFun_Comp.ufunclParComp_ufun_def ufParComp_asso ufunclParCompWell_ufun_def)
          apply (simp add: ufunclSerComp_ufun_def)
          apply (rule ufSerComp_asso)
           apply (meson ufunclSerCompWell_ufun_def) +
         by (simp add: UFun_Comp.ufunclParComp_ufun_def ufParCompWell_associativity ufunclParCompWell_ufun_def)
end

end