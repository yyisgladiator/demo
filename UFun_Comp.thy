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

  
(* ufLeast *)
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


subsection \<open>composition operators\<close>

(* general *) 
definition ufComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" where
"ufComp f1 f2 \<equiv>
let I = ufCompI f1 f2;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)
in Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = I) \<leadsto> ubFix (ufCompH f1 f2 x) Oc))" 

(* parcomp *)
definition ufParComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" ("_\<parallel>_") where
"ufParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))))"

(* sercomp *)
abbreviation sercomp_well :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> bool" where
"sercomp_well f1 f2 \<equiv>  (ufRan\<cdot>f1 = ufDom\<cdot>f2) 
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f1 = {})
                        \<and> (ufDom\<cdot>f2 \<inter> ufRan\<cdot>f2 = {})
                        \<and> (ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {})"

definition ufSerComp :: "('m \<Rrightarrow> 'm) => ('m \<Rrightarrow> 'm) => ('m \<Rrightarrow> 'm)"  ("_\<circ>_") where
"ufSerComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"

(* feedback *)
definition ufFeedH:: "('m \<Rrightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> 'm  \<rightarrow> 'm" where
"ufFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"

definition ufFeedbackComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" ("\<mu>_" 50) where
"ufFeedbackComp f \<equiv>
let I  = ufDom\<cdot>f - ufRan\<cdot>f;
    I1 = ufDom\<cdot>f;
    C  = ufRan\<cdot>f
in Abs_ufun (Abs_cfun (\<lambda> sb. (ubDom\<cdot>sb = I) \<leadsto>
    (ubFix (ufFeedH f sb) C)))"  

  
(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)  

subsection\<open>ubFix\<close>
thm ubFix_def

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

(* Intro lemma for if sbfix is mono *)  
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

  

  thm ubFix_def
 
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

(* TODO: here the ubleast dom assump is needed otherwise you can not prove it 
  assumes ubleast_dom: "\<And> cs. ubDom\<cdot>(ubLeast cs) = cs"
lemma ubfix_id: "(ubFix (\<Lambda> x. x) cs) = (ubLeast cs)"
  by (simp add: ubfix_strict ubleast_dom)
*)

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

  
(* general *)  
  
(* parcomp *)

(* sercomp *)
subsection\<open>Serial Composition\<close>

lemma if_then_mono:  assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In) \<leadsto> g b)"
proof(rule monofunI)
  fix x y :: "'a"
  assume "x\<sqsubseteq>y"
  hence "ubDom\<cdot>x = ubDom\<cdot>y" using ubdom_fix by blast 
  thus "(ubDom\<cdot>x = In)\<leadsto>g x \<sqsubseteq> (ubDom\<cdot>y = In)\<leadsto>g y" 
    by (smt \<open>(x::'a) \<sqsubseteq> (y::'a)\<close> assms monofun_def po_eq_conv some_below)
qed  
  
lemma if_then_cont:  assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In) \<leadsto> g b)"
proof(rule contI2)
  show "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)" using assms cont2mono if_then_mono by blast 
  thus " \<forall>Y. chain Y \<longrightarrow> (ubDom\<cdot>(\<Squnion>i. Y i) = In)\<leadsto>g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
    by (smt Abs_cfun_inverse2 assms below_refl if_then_lub is_ub_thelub lub_eq po_class.chainI ubdom_fix)
qed
  
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

(* This should be proven with the ufDom/Ran lemmas *)
lemma ufRan_dom: assumes "ubDom\<cdot>b = ufDom\<cdot>f" shows "ubDom\<cdot>(f\<rightleftharpoons>b) = ufRan\<cdot>f" 
  sorry  
  
lemma ufSerComp_well: assumes "ufRan\<cdot>f1 = ufDom\<cdot>f2" shows "ufWell (\<Lambda> x. (ubDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  apply(simp add: ufWell_def)
  apply rule
  (* Generated by sledgehammer *)
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
    by (smt CollectD assms option.distinct(1) option.sel ran_def ufRan_dom)
  show "\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun (\<Lambda> (x::'a). (ubDom\<cdot>x = ufDom\<cdot>f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))) \<longrightarrow> (ubDom\<cdot>b = Out)"
    apply(simp add: ufSerComp_cont)
    by (simp add: f1)
qed
  

(* feedback *)  
  
  
end