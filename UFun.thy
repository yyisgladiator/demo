(*  Title:        UFun
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Processing functions" 
*)

theory UFun
  imports UnivClasses
begin

  
default_sort ubcl 
  
  
(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
  
definition ufWell:: "('in \<rightarrow> 'out option) \<Rightarrow> bool" where
"ufWell f \<equiv> (\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))"

lemma ufWell_exists: "\<exists>x::('in \<rightarrow> 'out option). ufWell x"
proof - 
  obtain inf_ub:: "'out"  where inf_ub_ublen: "ubLen inf_ub = \<infinity>"
    using ublen_inf_ex by auto
  obtain ufun1:: "'in \<Rightarrow> 'out option" where ufun1_def: "ufun1 = (\<lambda> f. if ubDom\<cdot>f = {} then  Some inf_ub else None)"
    by simp
  have f1: "cont ufun1"
    apply(rule contI2)
     apply (simp add: monofun_def ubdom_fix ufun1_def)
    apply auto
  proof -
    fix Y :: "nat \<Rightarrow> 'in"
    assume "chain Y"
    then have "\<And>n. ubDom\<cdot>(Y n) = ubDom\<cdot>(Lub Y)"
      using is_ub_thelub ubdom_fix by blast
    then show "ufun1 (\<Squnion>n. Y n) \<sqsubseteq> (\<Squnion>n. ufun1 (Y n))"
      using ufun1_def by auto
  qed
  have f2: "(Rep_cfun (Abs_cfun ufun1)) = ufun1"
    using f1 by auto
  have f3: "ufWell (Abs_cfun ufun1)"
    apply (simp only: ufWell_def f2, rule)
    apply (metis domIff option.distinct(1) ufun1_def)
    apply (rule_tac x = "ubDom\<cdot>inf_ub" in exI)
    apply rule
  proof -
    fix b :: 'out
    have "(b \<in> ran ufun1 \<longrightarrow> ubDom\<cdot>b = ubDom\<cdot>inf_ub) = (b \<notin> ran ufun1 \<or> ubDom\<cdot>b = ubDom\<cdot>inf_ub)"
      by meson
    then show "b \<in> ran ufun1 \<longrightarrow> ubDom\<cdot>b = ubDom\<cdot>inf_ub"
      by (simp add: ran_def ufun1_def)
  qed
  thus ?thesis
    by auto
qed
    
lemma ufWell_adm: "adm (\<lambda>f. ((\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))))" (is "adm( ?P )")
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'b option"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  hence f1: "\<And>i. Rep_cfun (Y i) \<sqsubseteq> Rep_cfun (\<Squnion>i. Y i)" by (meson below_cfun_def is_ub_thelub)
  hence f2: "\<And>i. dom (Rep_cfun (Y i)) =  dom (Rep_cfun (\<Squnion>i. Y i))" by (simp add: part_dom_eq)
  have f0: "\<forall>i.(\<exists>Out::channel set. \<forall>b::'b. b \<in> ran (Rep_cfun (Y i)) \<longrightarrow> ubDom\<cdot>b = Out)"
    using as2 by simp 
  hence f01: "\<forall>i.(\<exists>Out::channel set. \<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Y i)\<cdot>b)) = Out)"
    by (metis (mono_tags, lifting) domD f2 mem_Collect_eq option.sel ran_def) 
  hence f4: "\<forall>i. \<forall>j\<ge>i. (\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> (the ((Y i)\<cdot>b)) \<sqsubseteq> (the ((Y j)\<cdot>b)))"
    by (metis f2 chY domIff monofun_cfun_fun option.collapse po_class.chain_mono some_below2)
  hence f4: "\<forall>i. \<forall>j\<ge>i. (\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Y i)\<cdot>b)) = ubDom\<cdot>(the ((Y j)\<cdot>b)))"
    by (simp add: ubdom_fix)
  then obtain Out where f6: "\<forall>i::nat. (\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Y i)\<cdot>b)) = Out)"
    by (metis f01 le_cases)
  hence f7: "(\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((\<Squnion>i. Y i)\<cdot>b)) = Out)"
    by (metis cfun_below_iff chY domIff f2 is_ub_thelub option.collapse some_below2 ubdom_fix)
  have f8: "\<forall>b. b \<in> ran (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>b = Out"
  proof (rule, rule)
    fix b :: 'b
    assume "b \<in> ran (Rep_cfun (\<Squnion>i. Y i))"
    then have "\<exists>a. Lub Y\<cdot>a = Some b"
      by (simp add: ran_def)
    then show "ubDom\<cdot>b = Out"
      by (metis (no_types) domI f7 option.sel)
  qed
  hence f10: "\<exists>Out::channel set. \<forall>b::'b. b \<in> ran (Rep_cfun (\<Squnion>i::nat. Y i)) \<longrightarrow> ubDom\<cdot>b = Out"
    by simp
  show "?P (\<Squnion>i. Y i)"
    apply rule
    apply (metis as2 below_cfun_def chY is_ub_thelub part_dom_eq)
    using f10 by blast
qed

lemma ufWell_adm2: "adm (\<lambda>f. ufWell f)"
  apply(simp add: ufWell_def)
  using ufWell_adm by blast
  
(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) ufun ("(_ \<Rrightarrow>/ _)" [20, 20] 20) = "{f :: 'in \<rightarrow> 'out option . ufWell f}"
  apply (simp add: ufWell_exists)
  using ufWell_adm2 by auto

    
(* Shorter version to get to normal functions from ('in,'out) ufun's *)
abbreviation Rep_cufun:: "('in, 'out) ufun \<Rightarrow> ('in \<Rightarrow> 'out option)" where
"Rep_cufun F \<equiv>  Rep_cfun (Rep_ufun F) "

(* Shorter version to get from normal functions to ('in,'out)  ufun's *)
  (* of course the argument should be "ufun_well" and "cont" *)
abbreviation Abs_cufun:: "('in \<Rightarrow> 'out option) \<Rightarrow> ('in, 'out) ufun " where
"Abs_cufun F \<equiv> Abs_ufun (Abs_cfun F)"
  

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  
  
definition ufDom :: "('in \<Rrightarrow> 'out) \<rightarrow> channel set" where
"ufDom \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_ufun f)))" 

definition ufRan :: "('in,'out) ufun \<rightarrow> channel set" where
"ufRan \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_ufun f)))" 

definition ufunType :: "('in,'out) ufun \<rightarrow> (channel set \<times> channel set)" where
"ufunType \<equiv> \<Lambda> f . (ufDom\<cdot>f, ufRan\<cdot>f)"

definition ufunIO :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) ufun set" where
"ufunIO In Out = {f. ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out}"

abbreviation theRep_abbrv :: "('in,'out) ufun \<Rightarrow> 'in \<Rightarrow> 'out " (infix "\<rightleftharpoons>" 62) where
"(f \<rightleftharpoons> s) \<equiv> (Rep_cufun f)\<rightharpoonup>s"


(****************************************************)
section\<open>Subtype\<close>
(****************************************************) 

  
(* return true iff tickcount holds *)
definition ufIsWeak :: "('in,'out) ufun \<Rightarrow> bool" where
"ufIsWeak f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> ubLen b \<le> ubLen (the ((Rep_ufun f)\<cdot>b))))"

definition ufIsStrong :: "('in,'out) ufun \<Rightarrow> bool" where
"ufIsStrong f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> lnsuc\<cdot>(ubLen b) \<le> ubLen (the ((Rep_ufun f)\<cdot>b))))"

(* ufIsWeak is adm (helper) *)
lemma ufIsWeak_adm: "adm (\<lambda> f. (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> ubLen b \<le> ubLen (the ((Rep_ufun f)\<cdot>b)))))" (is "adm( ?P )")
proof (rule admI)
  fix Y :: "nat \<Rightarrow> (('a,'b) ufun)"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  show "?P (\<Squnion>i. Y i)"
  proof (auto)
    fix b:: "'a"
    fix y:: "'b"
    fix i2:: "nat"
    assume as3: "Rep_cufun (\<Squnion>i. Y i) b = Some y"
    obtain c where c_def: "Rep_cufun (Y i2) b = Some c"
      by (metis as3 below_cfun_def below_ufun_def chY domD domI is_ub_thelub part_dom_eq)
    show "ubLen b \<le> ubLen y"
      by (metis (no_types, lifting) ublen_mono as2 as3 below_ufun_def c_def cfun_below_iff chY domI is_ub_thelub 
          lnle_def monofun_def option.sel some_below2 trans_lnle)
  qed
qed

(* ufIsWeak is adm *)
lemma ufIsWeak_adm2: "adm (\<lambda>f. ufIsWeak f)"
  by  (simp add: ufIsWeak_def ufIsWeak_adm)

(* there is a ufun which has ufIsStrong property *)
lemma ufistrongk_exist: "\<exists>x::('in,'out) ufun. ufIsStrong x"
proof -
   obtain inf_ub:: "'out"  where inf_ub_ublen: "ubLen inf_ub = \<infinity>"
      using ublen_inf_ex by auto
    obtain ufun1:: "'in \<Rightarrow> 'out option" where ufun1_def: "ufun1 = (\<lambda> f. if ubDom\<cdot>f = {} then  Some inf_ub else None)"
      by simp
    have f1: "cont ufun1"
      apply(rule contI2)
       apply (simp add: ufun1_def monofunI ubdom_fix)
      apply auto
    proof -
      fix Y :: "nat \<Rightarrow> 'in"
      assume "chain Y"
      then have "\<And>n. ubDom\<cdot>(Y n) = ubDom\<cdot>(Lub Y)"
        by (meson is_ub_thelub ubdom_fix)
      then show "ufun1 (\<Squnion>n. Y n) \<sqsubseteq> (\<Squnion>n. ufun1 (Y n))"
        by (simp add: ufun1_def)
    qed
    have f2: "(Rep_cfun (Abs_cfun ufun1)) = ufun1"
      using f1 by auto
    have f3: "ufWell (Abs_cfun ufun1)"
      apply (simp only: ufWell_def f2, rule)
       apply (metis domIff option.distinct(1) ufun1_def)
      apply (rule_tac x = "ubDom\<cdot>inf_ub" in exI)
      apply (rule, rule)
    proof -
      fix b :: 'out
      assume "b \<in> ran ufun1"
      then have "\<exists>i. ufun1 i = Some b"
        by (simp add: ran_def)
      then show "ubDom\<cdot>b = ubDom\<cdot>inf_ub"
        by (metis option.inject option.simps(3) ufun1_def)
    qed
    have f31: "Rep_cufun (Abs_cufun ufun1) = ufun1"
      by (simp add: Abs_ufun_inverse f2 f3)
    have f4: "ufIsStrong (Abs_ufun (Abs_cfun ufun1))"
    proof (simp add: ufIsStrong_def, auto, simp add: f31)
      fix b:: "'in"
      fix y:: "'out"
      assume assm41: "ufun1 b = Some y"
      have f41: "ufun1 b =  Some inf_ub"
        by (metis assm41 option.distinct(1) ufun1_def)
      then show "lnsuc\<cdot>(ubLen b) \<le> ubLen y"
        by (simp add: assm41 inf_ub_ublen)
      qed
    then show "\<exists>x::('in,'out) ufun. ufIsStrong x"
      by (rule_tac x = "(Abs_ufun (Abs_cfun ufun1))" in exI)
  qed

(* if ufun has the ufisstrong property then it also has the ufisweak property  *)
lemma ufisstrong_2_ufisweak: "\<And> f. ufIsStrong f \<Longrightarrow> ufIsWeak f"
  by (meson less_lnsuc trans_lnle ufIsStrong_def ufIsWeak_def)

    
(* new type, ufun which has the ufISWeak property  *)
cpodef ('in,'out)  USPFw = "{f ::  ('in,'out) ufun. ufIsWeak f}"
  using ufisstrong_2_ufisweak ufistrongk_exist apply auto[1]
  using ufIsWeak_adm2 by auto

(* ufIsStrong is adm  *)
lemma ufIsStrong_adm2: "adm (\<lambda>f. ufIsStrong (Rep_USPFw f))" (is "adm( ?P )")
proof  (rule admI)
  fix Y :: "nat \<Rightarrow> (('a,'b) USPFw)"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  show "?P (\<Squnion>i. Y i)"
  proof (simp add: ufIsStrong_def, auto)
    fix b:: "'a"
    fix y:: "'b"
    fix i2:: "nat"
    assume as3: "Rep_cufun (Rep_USPFw (Lub Y)) b = Some y"
    obtain c where c_def: "Rep_cufun (Rep_USPFw (Y i2)) b = Some c"
      by (metis as3 below_USPFw_def below_option_def below_ufun_def cfun_below_iff chY is_ub_thelub not_None_eq)
    have f1: "lnsuc\<cdot>(ubLen b) \<le> ubLen c"
      using as2 c_def ufIsStrong_def by fastforce
    have f3: "c \<sqsubseteq> y"
      by (metis as3 below_USPFw_def below_ufun_def c_def chY is_ub_thelub monofun_cfun_fun some_below2)
    have f4: "ubLen c \<le> ubLen y"
      using ublen_mono f3 lnle_def monofun_def by blast
    show "lnsuc\<cdot>(ubLen b) \<le> ubLen y"
      using f1 f4 by auto
  qed
qed

(* ufun, which has the ufIsStrong property  *)
cpodef ('in,'out) USPFs = "{f :: ('in,'out) USPFw. ufIsStrong (Rep_USPFw f)}"
   apply (metis Rep_USPFw_cases mem_Collect_eq ufisstrong_2_ufisweak ufistrongk_exist)
  using ufIsStrong_adm2 by auto


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   


subsection \<open>Rep_ufun / Abs_ufun\<close>

  
(* if we have a ufun chain, then we still have a chain after applying rep on each element in the chain  *)
lemma rep_ufun_chain [simp]: assumes "chain Y" shows "chain (\<lambda>i. Rep_ufun (Y i))"
  by (meson assms below_ufun_def po_class.chain_def)

(* rep_ufun is a mono func *)
lemma rep_ufun_mono [simp]: "monofun Rep_ufun"
  by (meson below_ufun_def monofunI)

(* rep_ufun is a continuous function *)
lemma rep_ufun_cont [simp]: "cont Rep_ufun"
  using cont_Rep_ufun cont_id by blast

(* rep_ufun produces a ufwell function  *)
lemma rep_ufun_well [simp]:  "ufWell (Rep_ufun s)"
  using Rep_ufun by blast

(* Rep_cufun is continuous  *)
lemma rep_cufun_cont [simp]: "cont Rep_cufun"
  by simp

(* Rep_cufun produces a ufwell function  *)
lemma rep_cufun_well [simp]: "ufWell (Abs_cfun (Rep_cufun x))"
  by (simp add: Cfun.cfun.Rep_cfun_inverse)

(* applying rep and abs after eachother proces the origin function  *)
lemma rep_abs_cufun [simp]: assumes "cont f" and "ufWell (Abs_cfun f)" 
  shows "Rep_cufun (Abs_cufun f) = f"
  by (simp add: Abs_ufun_inverse assms(1) assms(2))

(* like rep_abs_cufun but with less assm *)
lemma rep_abs_cufun2 [simp]: "ufWell f \<Longrightarrow> Rep_ufun (Abs_ufun f) = f"
  by (simp add: Abs_ufun_inverse)

  (* lemmata for reverse substitution *)
lemma abs_cufun_rev: "Abs_ufun (Abs_cfun F) = Abs_cufun F"
  by simp
    
lemma rep_cufun_rev: "Rep_cfun (Rep_ufun F) = Rep_cufun F"
  by simp


subsection \<open>ufun_definition\<close>

  
text{*  introduction rules for mono proofs *}
lemma ufun_monoI2 [simp]: assumes "\<And> x y. ubDom\<cdot>x = In \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (g x) \<sqsubseteq> (g y)"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
  by (simp add: assms monofunI some_below ubdom_fix)
 
text{* introduction rules for cont proofs *}
lemma ufun_contI [simp]: assumes "\<And> x y. ubDom\<cdot>x = In \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (g x) \<sqsubseteq> (g y)"
                  and "\<And> Y. chain Y \<Longrightarrow> (ubDom\<cdot>(\<Squnion>i. Y i) = In) \<Longrightarrow> g (\<Squnion>i. Y i)\<sqsubseteq> (\<Squnion>i. (g (Y i)))"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule contI2)
   apply (simp only: assms(1) ufun_monoI2)
  apply rule +
proof -
  fix Y::"nat \<Rightarrow> 'a"
  assume chain_Y: "chain Y"
  have f1: "\<And> i. ubDom\<cdot>(\<Squnion>i::nat. Y i) = ubDom\<cdot>(Y i)"
    using chain_Y is_ub_thelub ubdom_fix by blast
  show "(ubDom\<cdot>(\<Squnion>i::nat. Y i) = In)\<leadsto>g (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
  proof (cases "ubDom\<cdot>(\<Squnion>i::nat. Y i) = In")
    case True
    have f10: "g (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. g (Y i))"
      by (simp add: True assms(2) chain_Y)
    have f11: "(ubDom\<cdot>(\<Squnion>i::nat. Y i) = In)\<leadsto>g (\<Squnion>i::nat. Y i) = Some (g (\<Squnion>i::nat. Y i))"
      by (simp add: True)
    have f12: "(\<Squnion>i::nat. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i)) = (\<Squnion>i::nat. Some (g (Y i)))"
      using True f1 by auto
    show ?thesis 
      apply (subst f11)
      apply (subst f12)
      by (metis True assms(1) chain_Y f1 f10 po_class.chain_def some_below some_lub_chain_eq3)
  next
    case False
    then show ?thesis 
      using f1 by auto
  qed
qed


text{* Alternative Intro rule for ufun is mono with stronger assumptions than 
         @{thm (prem 1) ufun_monoI2} *}
lemma ufun_monoI3 [simp]: assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule ufun_monoI2)
    using assms monofunE by blast
  
text{* Alternative Intro rule for ufun is cont with stronger assumptions than 
         @{thm (prem 1) ufun_contI} *}
lemma ufun_contI2 [simp]: assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
proof(rule contI2)
  show "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    by (simp add: assms cont2mono)
  show " \<forall>Y. chain Y \<longrightarrow> (ubDom\<cdot>(\<Squnion>i. Y i) = In)\<leadsto>g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
  proof  (rule ,rule)
    fix Y::"nat \<Rightarrow> 'a"
    assume chain_Y: "chain Y"
    have f1: "\<And> i. ubDom\<cdot>(\<Squnion>i::nat. Y i) = ubDom\<cdot>(Y i)"
      using chain_Y is_ub_thelub ubdom_fix by blast
    show "(ubDom\<cdot>(\<Squnion>i::nat. Y i) = In)\<leadsto>g (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
    proof (cases "(ubDom\<cdot>(\<Squnion>i::nat. Y i) = In)")
      case True
      then show ?thesis 
        using assms chain_Y f1 if_then_lub2 by auto
    next
      case False
      then show ?thesis 
        using f1 by auto
    qed
  qed
qed

text{* Intro rule for ufun well *}
lemma ufun_wellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (ubDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> ubDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (ubDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  shows "ufWell f"
  apply (simp add: ufWell_def, rule)
   apply (meson assms(1) assms(3))
  apply (rule_tac x="Out" in exI)
  apply (simp add: ran_def)
  using assms(2) by force


(* only 'm ubs with the same domain are in an (in, out) ufun *)
lemma ufun_ufundom2dom: assumes "ubDom\<cdot>x = ubDom\<cdot>y" 
  shows "x\<in>dom (Rep_cufun f) \<longleftrightarrow>y\<in>dom (Rep_cufun f)"
  by (metis rep_ufun_well assms ufWell_def)

(* only 'm ubs with the same domain are in an (in, out) ufun *)
lemma ufun_dom2ufundom: assumes "x\<in>dom (Rep_cufun f)" and "y\<in>dom (Rep_cufun f)" 
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  by (metis rep_ufun_well assms(1) assms(2) ufWell_def)

(* helper function for "ufun_ran2ufundom" *)
lemma ran2exists[simp]: assumes "x\<in>(ran f)"
  shows "\<exists> xb. ((f xb) = (Some x))"
  using assms by (simp add: ran_def)

(* only 'm ubs with the same domain are in an 'm ufun *)
lemma ufun_ran2ufundom: assumes "x\<in>ran (Rep_cufun f)" and "y\<in>ran (Rep_cufun f)" 
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  using rep_ufun_well assms(1) assms(2) ufWell_def by blast

(* if 2 (in, out) ufun's are in a below-relation their Input-Channels are equal *)
lemma ufun_below_ufundom: assumes "a\<sqsubseteq>b" and "x \<in> dom (Rep_cufun b)" and "y \<in> dom (Rep_cufun a)"
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  by (metis assms(1) assms(2) assms(3) below_cfun_def below_ufun_def part_dom_eq ufun_dom2ufundom)

(* if 2 (in, out) ufun's are in a below-relation their Output-Channels are equal *)
lemma ufun_below_ran: assumes "a\<sqsubseteq>b" and "x \<in> ran (Rep_cufun b)" and "y \<in> ran (Rep_cufun a)"
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  proof -
    obtain sx where sx_def: "((Rep_cufun b) sx) =  (Some x)" 
      using assms ran2exists by fastforce
    obtain sy where sy_def: "((Rep_cufun a) sy) =  (Some y)" 
      using assms ran2exists by fastforce

    have "dom (Rep_cufun a) = dom (Rep_cufun b) " 
      by (meson assms(1) below_cfun_def below_ufun_def part_dom_eq)
    thus ?thesis
      by (metis (no_types, lifting) rep_ufun_well assms(1) assms(3) below_ufun_def cfun_below_iff domD domI ranI some_below2 sx_def ubdom_fix ufWell_def)
qed

(*   *)
lemma ufun_rel_eq: assumes "(a \<sqsubseteq> b)"
  shows "((Rep_cufun f) a) \<sqsubseteq> ((Rep_cufun f) b)"
  by (simp add: assms monofun_cfun_arg)

(*   *)
lemma ufun_arg_eqI: assumes "(a = b)"
  shows "(Rep_cufun f) a = (Rep_cufun f) b"
  by (simp add: assms)

(* empty function is not ufWell  *)
lemma map_not_ufun [simp]: "\<not>(ufWell (Abs_cfun empty))"
  apply (simp add: ufWell_def)
  using ubdom_ex by auto

(* there is at least one element in a ufun dom *)
lemma ufdom_not_empty [simp]: 
  shows "\<exists>x. x\<in>dom (Rep_cufun F)"
  by (metis domIff ex_in_conv map_not_ufun part_eq rep_cufun_well)

(* there is at least one element in a ufun ran *)
lemma ufran_not_empty [simp]: 
  shows "\<exists>x. x\<in> (ran (Rep_cufun F))"
  by (meson domIff not_None_eq ranI ufdom_not_empty)

lemma if_then_mono:  assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In) \<leadsto> g b)"
proof(rule monofunI)
  fix x y :: "'a"
  assume "x\<sqsubseteq>y"
  hence "ubDom\<cdot>x = ubDom\<cdot>y" using ubdom_fix by blast 
  thus "(ubDom\<cdot>x = In)\<leadsto>g x \<sqsubseteq> (ubDom\<cdot>y = In)\<leadsto>g y" 
    apply auto
    using \<open>(x::'a) \<sqsubseteq> (y::'a)\<close> assms monofun_def some_below by blast
qed  
  
lemma if_then_cont:  assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In) \<leadsto> g b)"
  apply (rule ufun_contI2)
  by (simp add: assms)
  
  subsection \<open>ufDom\<close>


(* mono proof of ufDom  *)
lemma ufdom_mono[simp]: "monofun (\<lambda>f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun f)))"
proof(rule monofunI)
  fix x y:: "('in, 'out) ufun"
  assume "x \<sqsubseteq> y"
  thus "ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun x)) \<sqsubseteq> ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun y))"
    by (simp add: below_cfun_def below_ufun_def part_dom_eq)
qed

(* used to show that ufunDom is continuous *)
lemma ufdom_contlub [simp]: assumes "chain Y" 
  shows "ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun (\<Squnion>i. Y i))) 
         \<sqsubseteq> (\<Squnion>i. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun (Y i))))"
proof -
  have "\<And>f n. \<not> chain f \<or> dom (Rep_cufun (f n::'a \<Rrightarrow> 'b)) = dom (Rep_cufun (Lub f))"
    by (meson below_cfun_def below_ufun_def is_ub_thelub part_dom_eq)
  then show ?thesis
    using assms by force
qed

(* ufunDom is continuous *)
lemma ufdom_cont [simp]:"cont (\<lambda>f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun f)))"
  by(simp add: contI2)

(* Insertion rule for ufunDom *)
lemma ufdom_insert: "ufDom\<cdot>f = ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun f))"
  by (simp add: ufDom_def)

(* if two ufuns are in a below relation their ufunDom is equal *)
lemma ufdom_below_eq: assumes "x \<sqsubseteq> y"
  shows "ufDom\<cdot>x = ufDom\<cdot>y"
  by (metis (no_types) assms below_cfun_def below_ufun_def part_dom_eq ufdom_insert)

(* The lub of a chain of ufuns has the same domain as each chain element *)
lemma ufdom_lub_eq: assumes "chain Y"
  shows "ufDom\<cdot>(\<Squnion>i. Y i) = ufDom\<cdot>(Y i)"
  using assms is_ub_thelub ufdom_below_eq by blast

(* if function S applies on a return none null then a has the same dome as the funtion S  *)    
lemma ufdom_2ufundom [simp]: assumes "(Rep_cufun S) a = Some b"
  shows "ufDom\<cdot>S = ubDom\<cdot>a"
  by (metis assms domI someI_ex ufun_dom2ufundom ufdom_insert)

(*neu*)
(* tspf_least_in_dom *)
lemma ufun_least_in_dom: "(ubLeast (ufDom\<cdot>f)) \<in> dom (Rep_cufun f)"
  by (metis domD rep_ufun_well ubdom_least_cs ufWell_def ufdom_2ufundom)

(* if the function has the same dom then they also have the same dom after rep is applied  *)
lemma ufdom_2_dom_ctufun: assumes "ufDom\<cdot>f = ufDom\<cdot>g"
  shows "dom (Rep_cufun f) = dom (Rep_cufun g)"  
  (* proof found by sledgehammer *)
  apply auto
  apply (metis assms domIff not_None_eq ufdom_2ufundom ufdom_not_empty ufun_ufundom2dom)
  by (metis assms domIff not_None_eq ufdom_2ufundom ufdom_not_empty ufun_ufundom2dom)

(* induction rule to proof that f is leq g  *)
lemma ufun_belowI: assumes "ufDom\<cdot>f = ufDom\<cdot>g"
          and "\<And>x. (ubDom\<cdot>x = ufDom\<cdot>f \<Longrightarrow> (Rep_cufun f)\<rightharpoonup>x \<sqsubseteq> (Rep_cufun g)\<rightharpoonup>x)"
        shows "f \<sqsubseteq> g"
proof -
  have "dom (Rep_cufun f) = dom (Rep_cufun g)"
    using assms(1) ufdom_2_dom_ctufun by blast
  thus ?thesis
    by (metis (full_types) assms(2) below_cfun_def below_ufun_def domI part_below ran2exists 
        ufran_not_empty ufun_dom2ufundom ufdom_2ufundom)
qed

(* the dom of a function is the if-argument  *)
lemma ufun_ufdom_abs: assumes "cont (\<lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))" 
                     and "ufWell (\<Lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))"
  shows "ufDom\<cdot>(Abs_cufun (\<lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
  apply(simp add: assms ufDom_def)
  apply (simp add: domIff)
  by (meson someI_ex ubdom_ex)

lemma ufun_eqI: assumes "ufDom\<cdot>f = ufDom\<cdot>g"
          and "\<And>x. (ubDom\<cdot>x = ufDom\<cdot>f \<Longrightarrow> (Rep_cufun f)\<rightharpoonup>x = (Rep_cufun g)\<rightharpoonup>x)"
        shows "f = g"
proof -
  have "dom (Rep_cufun f) = dom (Rep_cufun g)"
    using assms(1) ufdom_2_dom_ctufun by blast
  thus ?thesis
    by (metis Cfun.cfun.Rep_cfun_inject Rep_ufun_inject assms(2) domD part_eq ufdom_2ufundom)
qed

  
subsection \<open>ufRan\<close>


(* ufRan_def is monotone *)
lemma ufran_mono [simp]: "monofun (\<lambda> F. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun F)))"
proof (rule monofunI)
  fix x y :: "('in, 'out) ufun"
  assume "x \<sqsubseteq> y"
  thus "ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun x)) \<sqsubseteq> ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun y))"
    by (metis (no_types, lifting) po_eq_conv someI ufun_below_ran ufran_not_empty)
qed

(* helper function for cont proof of ufran  *)
lemma ufran_contlub [simp]: assumes "chain Y"
  shows "ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun (\<Squnion>i. Y i))) 
          \<sqsubseteq> (\<Squnion>i. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun (Y i))))"
  by (metis (no_types, lifting) assms below_refl is_ub_thelub po_class.chain_def 
             someI_ex ufun_below_ran ufran_not_empty)

(* ufRan_def is continuous *)
lemma ufran_cont [simp]: "cont (\<lambda> F. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun F)))"
  by (rule contI2, simp_all)

(* Insertion rule for ufran *)
lemma ufran_insert: "ufRan\<cdot>f = ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun f))"
  by (simp add: ufRan_def)
    
(* If two ufuns are in a below relation their output channels are equal *)
lemma ufran_below: assumes "x \<sqsubseteq> y"
  shows "ufRan\<cdot>x = ufRan\<cdot>y"
  apply (simp add: ufRan_def)
  by (metis (no_types, lifting) assms someI_ex ufran_not_empty ufun_below_ran)

(* the lub of an ufun chain has the same output channels as all the ufuns in the chain *)
lemma ufran_lub_eq: assumes "chain Y"
  shows "ufRan\<cdot>(\<Squnion>i. Y i) = ufRan\<cdot>(Y i)"
  using assms is_ub_thelub ufran_below by blast

(*   *)
lemma ufran_2_ubdom [simp]: assumes "(Rep_cufun F) a = Some b"
  shows "ufRan\<cdot>F = ubDom\<cdot>b"
    by (metis (no_types, lifting) Abs_cfun_inverse2 assms ranI someI_ex ufRan_def 
            ufun_ran2ufundom ufran_cont)

(*neu*)
(*tspfran_least*)
lemma ufran_least: "ufRan\<cdot>f = ubDom\<cdot>(f\<rightleftharpoons> (ubLeast (ufDom\<cdot>f)))"
  apply (simp add: ufRan_def)
  by (metis domIff option.collapse ufran_2_ubdom ufran_insert ufun_least_in_dom)

(*   *)
lemma ufran_2_ubdom2: assumes "ubDom\<cdot>tb = ufDom\<cdot>f"
  shows "ubDom\<cdot>((Rep_cufun f)\<rightharpoonup>tb) = ufRan\<cdot>f"
  by (metis assms domIff option.exhaust_sel rep_ufun_well ufWell_def ufdom_2ufundom ufdom_not_empty ufran_2_ubdom)



subsection \<open>ufunType\<close>


(* cont proof because ufdom and ufran are cont *)
lemma ufuntype_cont: "cont (\<lambda>f. (ufDom\<cdot>f, ufRan\<cdot>f))"
  by simp

(* insert rule for ufuntype *)
lemma ufuntype_insert: "ufunType\<cdot>f = (ufDom\<cdot>f, ufRan\<cdot>f)"
  by (simp add: ufunType_def)
  


(****************************************************)
section\<open>Instantiation\<close>
(****************************************************) 


instantiation ufun :: (ubcl, ubcl) ufuncl
begin

definition ufDom_ufun_def: "UnivClasses.ufDom \<equiv> ufDom"

definition ufRan_ufun_def: "UnivClasses.ufRan \<equiv> ufRan"

instance
  apply intro_classes
  apply (simp add: ufDom_ufun_def ufdom_below_eq)
  by (simp add: ufRan_ufun_def ufran_below)
end

end