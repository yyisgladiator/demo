(*  Title:        SPF
    Author:       Sebastian Stüber
    Authro:       Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Defines "Stream Processing Functions"
*)

theory SPF
imports SB

begin
  
  default_sort message 

(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)

(* an 'm SPF has a fixed input-channel-set and output-set.  *)
(* it is also an continuous function *)
definition spf_well:: "('m SB \<rightarrow> 'm SB option) \<Rightarrow> bool" where
"spf_well f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> sbDom\<cdot>b = In) \<and> 
    (b \<in> dom (Rep_cfun f) \<longrightarrow> sbDom\<cdot>(the (f\<cdot>b)) = Out)"

(* Show that a function exists which is spf_well *)
    (* Show that this function ist continuous. *)
  lemma spf_least_cont[simp]: "cont [sbLeast {} \<mapsto> sbLeast {}]"
  proof (rule contI)
  fix Y:: "nat \<Rightarrow> 'm SB"
  assume chY: "chain Y"
  thus "range (\<lambda>i. [sbLeast {} \<mapsto> sbLeast {}] (Y i)) <<| [sbLeast {} \<mapsto> sbLeast {}] (\<Squnion>i. Y i) "
  proof (cases "sbLeast {} \<in> range (Y)")
   case True
   thus ?thesis
     by (simp add: below_option_def chY is_lub_maximal lub_eqI po_class.chainE rangeI 
                   stbundle_allempty ub_rangeI)
  next
  case False
  hence "\<forall>i. (sbDom\<cdot>(Y i) \<noteq> {})" by (metis empty_iff rangeI sbleast_sbdom sb_eq)
  hence "(\<Squnion>i. Y i) \<noteq> sbLeast {}" using chY by (auto simp add: sbChain_dom_eq2)
  thus ?thesis
    by (metis (mono_tags, lifting) False below_option_def fun_upd_apply is_lub_maximal 
              rangeI ub_rangeI)
      qed
  qed 
  
    (* Show that an wellformed function exists.  Used in cpo_def proof. *)
  lemma spf_well_exists[simp]: "spf_well (Abs_cfun [sbLeast {} \<mapsto> sbLeast {}])"
  apply(simp add: spf_well_def)
  by (metis empty_iff sbleast_sbdom sb_eq)
  

(* Show that spw_wellformed is admissible *)
    (* Split the spf_well definition into 2 parts *)
  lemma spf_well_def2: "spf_well f = ((\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f)) = (sbDom\<cdot>b = In)) 
  \<and> (\<exists>Out. \<forall>b. b \<in> dom (Rep_cfun f) \<longrightarrow> sbDom\<cdot>(the (f\<cdot>b)) = Out))"
  by (meson spf_well_def)

  
    (* Proof admissibility on the first part of spf_well *)
  lemma spf_well_adm1[simp]: "adm (\<lambda>f. \<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f)) = (sbDom\<cdot>b = In))"
  by (smt adm_upward below_cfun_def part_dom_eq)
  
    (* Proof admissibility on the second part of spf_well *)
lemma spf_well_adm2[simp]: "adm (\<lambda>f. \<exists>Out. \<forall>b. b \<in> dom (Rep_cfun f) 
                                        \<longrightarrow> sbDom\<cdot>(the (f\<cdot>b)) = Out)" (is "adm( ?P )")   
  proof (rule admI)
  fix i :: nat
  fix Y
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  hence "Rep_cfun (Y i) \<sqsubseteq> Rep_cfun (\<Squnion>i. Y i)" by (meson below_cfun_def is_ub_thelub)
  hence "dom (Rep_cfun (Y i)) =  dom (Rep_cfun (\<Squnion>i. Y i))" by (simp add: part_dom_eq)
  thus "?P (\<Squnion>i. Y i)"
    proof -
      { fix aa :: "channel set \<Rightarrow> 'a"
        obtain CC :: "nat \<Rightarrow> channel set" where
          "\<forall>n a. a \<notin> dom (Rep_cfun (Y n)) \<or> sbDom\<cdot>Rep_cfun (Y n)\<rightharpoonup>a = CC n"
          using as2 by moura
        moreover
        { assume "sbDom\<cdot>Rep_cfun (Y i)\<rightharpoonup>aa (CC i) = CC i"
          moreover
          { assume "Y i\<cdot>(aa (CC i)) \<noteq> Lub Y\<cdot>(aa (CC i))"
            hence "\<exists>C. Rep_cfun (Y i)\<rightharpoonup>aa C \<sqsubseteq> Rep_cfun (Lub Y)\<rightharpoonup>aa (CC i)"
              by (meson below_option_def chY is_ub_thelub monofun_cfun_fun)
            hence "(\<exists>C. sbDom\<cdot>Rep_cfun (Y i)\<rightharpoonup>aa C \<noteq> CC i) 
                            \<or> (\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) 
                            \<or> sbDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C)"
              by (metis (no_types) sbdom_eq) }
          ultimately have "(\<exists>C. sbDom\<cdot>Rep_cfun (Y i)\<rightharpoonup>aa C \<noteq> CC i) 
                                 \<or> (\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) 
                                 \<or> sbDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C)"
            by fastforce }
        ultimately have "\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> sbDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C"
          by (metis \<open>dom (Rep_cfun (Y i)) = dom (Rep_cfun (\<Squnion>i. Y i))\<close>) }
      thus ?thesis
        by metis
    qed 
  qed
  
    (* unite the two admissible proofs. Used in cpo_def proof. *)
  lemma spf_well_adm[simp]: "adm (\<lambda>f. spf_well f)"
  by(simp add: spf_well_def2)
  

  (* Define the type 'm SPF (Stream Processing Functions) as cpo *)
  cpodef 'm SPF = "{f :: 'm SB \<rightarrow> 'm SB option . spf_well f}"
   using spf_well_exists apply blast
  using spf_well_adm by auto


setup_lifting type_definition_SPF




(* ----------------------------------------------------------------------- *)
  section \<open>Definitions on 'm SPF's\<close>
(* ----------------------------------------------------------------------- *)


subsection \<open>rep/abs\<close>

(* Shorter version to get to normal functions from 'm SPF's *)
abbreviation Rep_CSPF:: "'m SPF \<Rightarrow> ('m SB \<rightharpoonup> 'm SB)" where
"Rep_CSPF F \<equiv>  Rep_cfun (Rep_SPF F) "

(* Shorter version to get from normal functions to 'm SPF's *)
  (* of course the argument should be "spf_well" and "cont" *)
abbreviation Abs_CSPF:: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> 'm SPF" where
"Abs_CSPF F \<equiv> Abs_SPF (Abs_cfun F)"

subsection \<open>domain/range\<close>

  (* get input channel set for given 'm SPF *)
definition spfDom :: "'m SPF \<rightarrow> channel set" where
"spfDom \<equiv> \<Lambda> f. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF f))" 

  (* get output channel set for given 'm SPF *)
definition spfRan :: "'m SPF \<rightarrow> channel set" where
"spfRan \<equiv> \<Lambda> f.  sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF f))"


text {* spftype" returns the type of the stream processing function.*}
definition spfType :: "'m SPF \<rightarrow> (channel set \<times> channel set)" where
"spfType \<equiv> \<Lambda> f . (spfDom\<cdot>f, spfRan\<cdot>f)"

  (* All 'm SPF's with "In" as Input and "Out" as Output set *)
definition spfIO :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm SPF set" where
"spfIO In Out = {f. spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out}"



subsection \<open>apply\<close>

(* harpoon and Rep operation all in one for simpler SPF on SB applications *)
    (* bounds weaker than tsbres *)
abbreviation theRep_abbrv :: "'a SPF \<Rightarrow> 'a SB \<Rightarrow> 'a SB " (infix "\<rightleftharpoons>" 62) where
"(f \<rightleftharpoons> s) \<equiv> (Rep_CSPF f)\<rightharpoonup>s"


subsection \<open>fix\<close>

  (* fixed point operator for bundle to bundle functions *)
definition sbFix :: "('m SB \<rightarrow> 'm SB) \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix F cs \<equiv>  (\<Squnion>i. iterate i\<cdot>F\<cdot>(cs^\<bottom>))"

text {* special case sbFix for cont of the composition *}
definition sbFix2 :: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> 'm SB  \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation iter_sbfix2:: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_sbfix2 F i cs \<equiv> (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation sbfun_io_eq :: "('m SB \<rightarrow> 'm SB)  \<Rightarrow> channel set \<Rightarrow> bool" where
"sbfun_io_eq f cs \<equiv> sbDom\<cdot>(f\<cdot>(cs^\<bottom>)) = cs"


subsection \<open>composition\<close>

subsubsection \<open>channel sets\<close>
  
text {* the input channels of the composition of f1 and f2 *}
definition spfCompI :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompI f1 f2 \<equiv> (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

text {* the internal channels of the composition of f1 and f2 *}
definition spfCompL :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompL f1 f2 \<equiv> (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<inter> (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

text {* the output channels of the composition of f1 and f2 *}
definition spfCompOc :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompOc f1 f2 \<equiv> (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

text {* all channels of the composition of f1 and f2  *}
definition spfCompC :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompC f1 f2 \<equiv> spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"


subsubsection \<open>composition helpers\<close>
  (* basically the composition helpers are parallel composition operators that take an 
    additional feedback and input bundle x *)
  
definition spfCompH :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompH f1 f2 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"

abbreviation iter_spfCompH :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfCompH f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompH f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>))" 

(* old composition helper *)
definition spfCompH2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompH2 f1 f2 x \<equiv> (\<Lambda> z. x \<uplus> (f1\<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"

abbreviation iter_spfcompH2 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfcompH2 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompH2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))"  


subsubsection \<open>composition operators\<close>

text {* The general composition operator for SPFs *}
definition spfComp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" (infixl "\<otimes>" 40) where
"spfComp f1 f2 \<equiv>
let I = spfCompI f1 f2;
    Oc = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> sbFix (spfCompH f1 f2 x) Oc)"


(* alternative versions, only for evaluation of the spfComp *)
  (* do not use those in production *)
definition spfCompOld :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF"  where
"spfCompOld f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    O1 = spfRan\<cdot>f1; 
    O2 = spfRan\<cdot>f2; 
    I  = spfCompI f1 f2;
    Oc = spfCompOc f1 f2;
    C  = spfCompC f1 f2   
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. x \<uplus> (f1\<rightleftharpoons>(z \<bar> I1)) \<uplus> (f2\<rightleftharpoons>(z \<bar> I2)))\<cdot>(sbLeast C)) \<bar> Oc)"


(* equal to spfComp \<Rightarrow> sbFix_def *)
definition spfCompOld2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" where
"spfCompOld2 f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    I  = spfCompI f1 f2; 
    C  = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> I1)) \<uplus> (f2\<rightleftharpoons>((x \<uplus> z) \<bar> I2)))\<cdot>(C^\<bottom>)))"


subsection \<open>spfLift\<close>
  (* example for SPF instantiations can also be found in SPF_Templates *)

text {* "spflift" takes a "simple stream processing function" and two channel 
         names where the streams flow, and lifts it to a stream bundle processing function.*}
definition spfLift :: "('m stream \<rightarrow> 'm stream) => channel => channel => 'm SPF" where
"spfLift f ch1 ch2  \<equiv> Abs_CSPF (\<lambda>b. ( (b\<in>{c1}^\<Omega>) \<leadsto> ([ch2 \<mapsto> f\<cdot>(b . ch1)]\<Omega>)))" 

(* takes a fully defined 'm SPF-function and changes it to an 
    'm SPF with given In & Out channels *)
definition spfSbLift:: "('m SB \<rightarrow> 'm SB) \<Rightarrow> channel set \<Rightarrow> channel set \<Rightarrow> 'm SPF" where
"spfSbLift f In Out \<equiv> Abs_CSPF (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto> (\<up>f\<cdot>b) \<bar> Out)"


subsection \<open>hide\<close>

definition hide :: "'m SPF \<Rightarrow>  channel set \<Rightarrow> 'm SPF" ("_\<h>_") where
"hide f cs \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"

subsection \<open>spfLeast\<close>
  
definition spfLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm SPF" where
"spfLeast In Out \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = In) \<leadsto> (sbLeast Out))" 

subsection \<open>spfRestrict\<close>
  
definition spfRestrict :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfRestrict In Out \<equiv> (\<Lambda> f. if (spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out) then f else (spfLeast In Out))"

(* ----------------------------------------------------------------------- *)
  section \<open>Lemmas on 'm SPF's\<close>
(* ----------------------------------------------------------------------- *)


  subsection \<open>Rep_CSPF / Abs_CSPF\<close>

lemma rep_spf_chain [simp]: assumes "chain Y" shows "chain (\<lambda>i. Rep_SPF (Y i))"
  by (meson assms below_SPF_def po_class.chain_def)

lemma rep_spf_mono [simp]: shows "monofun Rep_SPF"
  by (meson below_SPF_def monofunI)

(* The newly defined Rep_SPF is a continuous function *)
lemma rep_spf_cont [simp]: "cont Rep_SPF"
  using cont_Rep_SPF cont_id by blast

lemma rep_spf_well [simp]:  "spf_well (Rep_SPF s)"
  using Rep_SPF by blast

lemma rep_cspf_cont [simp]: "cont Rep_CSPF"
  by simp

lemma rep_cspf_well [simp]: "spf_well (Abs_cfun (Rep_CSPF x))"
  by (metis Rep_SPF eta_cfun mem_Collect_eq)

lemma rep_cspf_cont2 [simp]: "cont (Rep_CSPF x)"
  by simp

lemma rep_abs_cspf [simp]: assumes "cont f" and "spf_well (Abs_cfun f)" 
  shows "Rep_CSPF (Abs_CSPF f) = f"
  by (simp add: Abs_SPF_inverse  assms(1) assms(2))

lemma [simp]: "spf_well f \<Longrightarrow> Rep_SPF (Abs_SPF f) = f"
by (simp add: Abs_SPF_inverse)

  (* lemmata for reverse substitution *)
lemma abs_cspf_rev: "Abs_SPF (Abs_cfun F) = Abs_CSPF F"
  by simp
    
lemma rep_cspf_rev: "Rep_cfun (Rep_SPF F) = Rep_CSPF F"
  by simp



subsection \<open>SPF_definition\<close>
  
text{*  introduction rules for mono proofs *}
lemma spf_monoI2 [simp]: assumes "\<And> x y. sbDom\<cdot>x = In \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (g x) \<sqsubseteq> (g y)"
  shows "monofun (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)"
  by (smt assms below_option_def monofun_def sbdom_eq some_below)
 
text{* introduction rules for cont proofs *}
lemma spf_contI [simp]: assumes "\<And> x y. sbDom\<cdot>x = In \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (g x) \<sqsubseteq> (g y)"
                  and "\<And> Y. chain Y \<Longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = In) \<Longrightarrow> g (\<Squnion>i. Y i)\<sqsubseteq> (\<Squnion>i. (g (Y i)))"
  shows "cont (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule contI2)
   apply (simp only: assms(1) spf_monoI2)
  by (smt assms(1) assms(2) below_option_def is_ub_thelub l1 lub_eq op_the_lub 
          option.sel option.simps(3) po_class.chain_def sbdom_insert)

text{* Alternative Intro rule for SPF is mono with stronger assumptions than 
         @{thm (prem 1) spf_monoI2} *}
lemma spf_monoI3 [simp]: assumes "monofun g"
  shows "monofun (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule spf_monoI2)
    using assms monofunE by blast
  
text{* Alternative Intro rule for SPF is cont with stronger assumptions than 
         @{thm (prem 1) spf_contI} *}
lemma spf_contI2 [simp]: assumes "cont g"
  shows "cont (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)"
  using assms if_then_cont by blast
    
text{* Intro rule for spf well *}
lemma spf_wellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (sbDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> sbDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (sbDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  shows "spf_well f"
  by (meson assms spf_well_def)
    
    
text{* Show that Map.empty is not an 'm SPF *}
lemma map_not_spf [simp]: "\<not>(spf_well (Abs_cfun empty))"
  apply (simp add: spf_well_def)
  using sbleast_sbdom by blast

(* the "dom" of an 'm SPF is never empty *) 
(* Used in "Some" proofs, for example in "spfDom" *)
lemma spf_dom_not_empty [simp]: 
  shows "\<exists>x. x\<in>dom (Rep_CSPF F)"
  by (metis domIff ex_in_conv map_not_spf part_eq rep_cspf_well)

(* the "rand" of an 'm SPF is never empty *) 
(* Used in "Some" proofs, for example in "spfRan" *)
lemma spf_ran_not_empty [simp]: 
  shows "\<exists>x. x\<in> (ran (Rep_CSPF F))"
  by (meson domIff not_None_eq ranI spf_dom_not_empty)

(* only 'm SBs with the same domain are in an 'm SPF *)
lemma spf_sbdom2dom: assumes "sbDom\<cdot>x = sbDom\<cdot>y" 
  shows "x\<in>dom (Rep_CSPF f) \<longleftrightarrow>y\<in>dom (Rep_CSPF f)"
  by (metis (no_types)  assms rep_spf_well spf_well_def2)

(* only 'm SBs with the same domain are in an 'm SPF *)
lemma spf_dom2sbdom: assumes "x\<in>dom (Rep_CSPF f)" and "y\<in>dom (Rep_CSPF f)" 
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  by (metis  assms rep_spf_well spf_well_def)

(* helper function for "spf_ran2sbdom". Somehow it doesn't work without *)
lemma ran2exists[simp]: assumes "x\<in>(ran f)"
  shows "\<exists> xb. ((f xb) = (Some x))"
  using assms by (simp add: ran_def)

(* only 'm SBs with the same domain are in an 'm SPF *)
lemma spf_ran2sbdom: assumes "x\<in>ran (Rep_CSPF f)" and "y\<in>ran (Rep_CSPF f)" 
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  proof -
  obtain sx where sx_def: "((Rep_CSPF f) sx) =  (Some x)" using assms ran2exists by fastforce
  obtain sy where sy_def: "((Rep_CSPF f) sy) =  (Some y)" using assms ran2exists by fastforce
  thus ?thesis
  by (metis Cfun.cfun.Rep_cfun_inverse  sx_def domI option.sel rep_cspf_well spf_well_def2)
qed



(* if 2 'm SPF's are in a below-relation their Input-Channels are equal *)
lemma spf_below_sbdom: assumes "a\<sqsubseteq>b" and "x \<in> dom (Rep_CSPF b)" and "y \<in> dom (Rep_CSPF a)"
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  by (metis assms(1) assms(2) assms(3) below_SPF_def below_cfun_def part_dom_eq spf_dom2sbdom)

(* if 2 'm SPF's are in a below-relation their Output-Channels are equal *)
lemma spf_below_ran: assumes "a\<sqsubseteq>b" and "x \<in> ran (Rep_CSPF b)" and "y \<in> ran (Rep_CSPF a)"
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  proof -
    obtain sx where sx_def: "((Rep_CSPF b) sx) =  (Some x)" 
      using assms ran2exists by fastforce
    obtain sy where sy_def: "((Rep_CSPF a) sy) =  (Some y)" 
      using assms ran2exists by fastforce

    have "dom (Rep_CSPF a) = dom (Rep_CSPF b) " 
      by (metis  assms(1) below_SPF_def below_cfun_def part_dom_eq)
    thus ?thesis
      by (metis (no_types, lifting)  assms(1) assms(3) below_SPF_def below_cfun_def domD 
              domI fun_below_iff ranI sbdom_eq some_below2 spf_ran2sbdom sx_def)
qed

lemma spf_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (f \<rightleftharpoons> b)"
  by (metis  assms cont2mono monofun_cfun_arg monofun_def op_the_cont)
    
lemma spf_arg_eqI: assumes "(a = b)"
  shows "f\<rightleftharpoons>a = f\<rightleftharpoons>b"
  by (simp add: assms)



  subsection \<open>spfDom\<close>


(* spfDom is monotonic. Used to show that spfDom is continuous *)
lemma spf_dom_mono[simp]: "monofun (\<lambda>f. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF f)))"
  proof(rule monofunI)
  fix x y:: "'m SPF"
  assume "x\<sqsubseteq>y"
  thus "sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF x)) \<sqsubseteq> sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF y))"
  by (metis (no_types, lifting) po_eq_conv someI spf_below_sbdom spf_dom_not_empty)
qed

(* used to show that spfDom is continuous *)
lemma spf_dom_contlub [simp]: assumes "chain Y" 
  shows "sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF (\<Squnion>i. Y i))) 
         \<sqsubseteq> (\<Squnion>i. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF (Y i))))"
  by (metis (mono_tags, lifting)  Rep_SPF assms below_refl 
            is_ub_thelub lub_chain_maxelem mem_Collect_eq po_eq_conv someI_ex spf_below_sbdom 
            spf_dom_not_empty spf_well_def2)


(* spfDom is continuous *)
lemma spf_dom_cont [simp]:"cont (\<lambda>f. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF f)))"
  by(simp add: contI2)

  subsubsection \<open>equalities\<close>
    
lemma spfdom_insert: "spfDom\<cdot>f = sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF f))"
by(simp add: spfDom_def)

(* if 2 elements are in a below relation they have the same Input-channel-Set *)
lemma spfdom_eq: assumes "x\<sqsubseteq>y"
  shows "spfDom\<cdot>x = spfDom\<cdot>y"
  by (metis (no_types, lifting) assms someI_ex spf_below_sbdom spf_dom_not_empty spfdom_insert)

(* the lub of an chain has the same input-set as all elements in the chain *)
lemma spfdom_eq_lub: assumes "chain Y"
  shows "spfDom\<cdot>(\<Squnion>i. Y i) = spfDom\<cdot>(Y i)"
  using assms is_ub_thelub spfdom_eq by blast

(* the inputs of an 'm SPF all have the channel set "In" *)
lemma spfdom2sbdom [simp]: assumes "(Rep_CSPF S) a = Some b"
  shows "spfDom\<cdot>S = sbDom\<cdot>a"
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms domI someI_ex spfDom_def 
            spf_dom2sbdom spf_dom_cont)

lemma spfLeastIDom: "(sbLeast (spfDom\<cdot>f)) \<in> dom (Rep_CSPF f)"
by (metis domD sbleast_sbdom spf_dom_not_empty spf_sbdom2dom spfdom2sbdom)

lemma spf_belowI: assumes "spfDom\<cdot>f = spfDom\<cdot>g"
          and "\<And>x. (sbDom\<cdot>x = spfDom\<cdot>f \<Longrightarrow> (Rep_CSPF f)\<rightharpoonup>x \<sqsubseteq> (Rep_CSPF g)\<rightharpoonup>x)"
       shows "f \<sqsubseteq> g"
proof -
  have "dom (Rep_CSPF f) = dom (Rep_CSPF g)"
    by (metis (no_types, lifting) Collect_cong  assms(1) dom_def mem_Collect_eq 
              rep_spf_well spfLeastIDom spf_well_def)
  thus ?thesis
    by (metis  assms(2) below_SPF_def below_cfun_def domIff option.collapse part_below spfdom2sbdom) 
qed

lemma spfDomAbs: assumes "cont (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))" 
                     and "spf_well (\<Lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))"
    shows "spfDom\<cdot>(Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
apply(simp add: spfDom_def)
apply(simp_all add: assms)
proof -
  have "\<forall>p s pa. (\<not> p (s::'a SB) \<or> (\<exists>s. p s \<and> \<not> pa s)) \<or> pa (Eps p)"
    by (metis someI2)
  hence "(SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)"
    by (metis (no_types) assms(1) assms(2) rep_abs_cspf spf_dom_not_empty)
  hence "(sbDom\<cdot> (SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) = cs)
                 \<leadsto>f (SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) \<noteq> None"
    by blast
  thus "sbDom\<cdot> (SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) = cs"
    by meson
qed
    
  subsection \<open>spfRan\<close>

text{* @{thm spfRan_def} is monotone *}
lemma spf_ran_mono[simp]: "monofun (\<lambda> f.  sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF f)))"
  proof(rule monofunI)
  fix x y :: "'m SPF"
  assume "x\<sqsubseteq>y"
  thus "sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF x)) \<sqsubseteq> sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF y))"
  by (metis (no_types, lifting) po_eq_conv someI spf_below_ran spf_ran_not_empty)
qed

text{* contlub properties of @{thm spfRan_def} *}
lemma spf_ran_contlub [simp]: assumes "chain Y"
  shows "sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF (\<Squnion>i. Y i))) 
          \<sqsubseteq> (\<Squnion>i. sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF (Y i))))"
  by (metis (no_types, lifting) assms below_refl is_ub_thelub po_class.chain_def 
             someI_ex spf_below_ran spf_ran_not_empty)

text{* @{thm spfRan_def} is continuous *}
lemma spf_ran_cont[simp]: "cont (\<lambda>f. sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF f)))"
  apply(rule contI2)
   by simp_all

lemma spfran_insert: "spfRan\<cdot>f = sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF f))"
by(simp add: spfRan_def)

(* In a chain all elements have the same Out-channel set *)
lemma spfran_eq: assumes "x\<sqsubseteq>y"
  shows "spfRan\<cdot>x = spfRan\<cdot>y"
  by (smt Abs_cfun_inverse2 assms someI_ex spfRan_def spf_below_ran spf_ran_cont spf_ran_not_empty)

(* the Lub of a chain has the same spfRan as the elements in the chain *)
lemma spfran_eq_lub: assumes "chain Y"
  shows "spfRan\<cdot>(\<Squnion>i. Y i) = spfRan\<cdot>(Y i)"
  using assms is_ub_thelub spfran_eq by blast


(* output produced by "S" has sbDom = Out *)
lemma spfran2sbdom [simp]: assumes "(Rep_CSPF S) a = Some b"
  shows "spfRan\<cdot>S = sbDom\<cdot>b"
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms ranI someI_ex spfRan_def spf_ran2sbdom 
            spf_ran_cont)

lemma spfran_least: "spfRan\<cdot>f = sbDom\<cdot>(f \<rightleftharpoons> (spfDom\<cdot>f)^\<bottom>)"
  apply(simp add: spfRan_def)
  by (metis (no_types, lifting) domIff option.exhaust_sel ranI someI_ex spfLeastIDom spf_ran2sbdom)

lemma spfran2sbdom2: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" and "spfDom\<cdot>f \<noteq> {}"
  shows "sbDom\<cdot>((Rep_CSPF f) \<rightharpoonup> sb) = spfRan\<cdot>f"
  apply(simp add: spfran_insert)
  by (metis (no_types, lifting) assms(1) domIff option.collapse ran2exists spf_ran_not_empty 
            spf_sbdom2dom spfdom2sbdom spfran2sbdom tfl_some)

lemma spf_ran_2_tsbdom2 [simp]: assumes "sbDom\<cdot>tb = spfDom\<cdot>f"
  shows "sbDom\<cdot>(f\<rightleftharpoons>tb) = spfRan\<cdot>f"
  by (metis assms rep_spf_well sbleast_sbdom spfLeastIDom spf_well_def spfran_least)
    

subsection \<open>spfType\<close>
  
  (* spftype is cont since spfDom and spfRan are cont *)
lemma spftype_cont: "cont (\<lambda>f. (spfDom\<cdot>f, spfRan\<cdot>f))"
  by simp

lemma spftype_insert: "spfType\<cdot>f = (spfDom\<cdot>f, spfRan\<cdot>f)"
  by (simp add: spfType_def)




  subsection \<open>spfSbLift\<close>


(* continuity of spfSbLift is allready in simp *)
  (* I define it nevertheless, to be used by sledgi *)
lemma spfsblift_cont[simp]: "cont (\<lambda>b. (sbDom\<cdot>b=In) \<leadsto> (\<up>f\<cdot>b) \<bar> Out)"
  by simp

(* the function produced by spfSbLift is wellformed *)
lemma spfsblift_well[simp]: "spf_well  (\<Lambda> b. (sbDom\<cdot>b=In) \<leadsto> (\<up>f\<cdot>b) \<bar> Out)"
  proof(rule spf_wellI)
    fix b::"'a SB"
    assume "b \<in> dom (Rep_cfun (\<Lambda> b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(f\<cdot>b))\<bar>Out)))"
    hence b_def:" b \<in> dom (\<lambda> b. (sbDom\<cdot>b = In)\<leadsto>(\<up>f\<cdot>b)\<bar>Out)" by simp
    thus "sbDom\<cdot>b = In"
      proof -
        show ?thesis
        by (meson b_def if_then_sbDom)
      qed
   thus "sbDom\<cdot>(the ((\<Lambda> b. (sbDom\<cdot>b = In)\<leadsto>(\<up>f\<cdot>b)\<bar>Out)\<cdot>b)) = Out" by simp
  next
  fix b2::"'a SB"
  assume "sbDom\<cdot>b2 = In"
  thus "b2 \<in> dom (Rep_cfun (\<Lambda> b. (sbDom\<cdot>b = In)\<leadsto>(\<up>f\<cdot>b)\<bar>Out))" by (simp add: domIff)
qed

lemma spfsblift_sbdom[simp]: "spfDom\<cdot>(spfSbLift F In Out) = In"
  apply(simp add: spfSbLift_def spfDom_def)
  apply(simp add: domIff)
  by (metis (mono_tags) SB_def mem_Collect_eq sb_exists someI_ex)


lemma if_then_ran:
  assumes "d \<in> ran (\<lambda>b. (P b)\<leadsto>((\<up>(F b))\<bar> Out))"
  shows "sbDom\<cdot>d = Out"
  by (smt assms inf.orderE inf_commute option.sel option.simps(3) ran2exists sbrestrict_sbdom 
          sbup_sbdom subset_UNIV)

lemma spfsblift_dom [simp]: "(\<exists> d. (d \<in> (dom (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(F\<cdot>b))\<bar>Out)))))"
  proof
  show "(sbLeast In) \<in> (dom (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(F\<cdot>b))\<bar>Out)))" by auto
qed





(* ----------------------------------------------------------------------- *)
  subsection \<open>spfComp\<close>
(* ----------------------------------------------------------------------- *)
    
    
  subsubsection \<open>spfCompHelp\<close>
(* ----------------------------------------------------------------------- *)    

lemma spfCompHelp_cont [simp]: "cont (\<lambda> last. (b \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(last \<bar> spfDom\<cdot>f1))
                                   \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(last \<bar> spfDom\<cdot>f2))))"
proof -
  have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  hence "cont (\<lambda>s. sbUnion\<cdot> (b \<uplus> Rep_cfun (Rep_SPF f1)\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))) 
                    \<and> cont (\<lambda>s. Rep_SPF f2\<cdot>(s\<bar>spfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda>s. b \<uplus> (Rep_cfun (Rep_SPF f1)\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) 
                     \<uplus> (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s\<bar>spfDom\<cdot>f2))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed

lemma spfCompHelp_monofun2 [simp]: 
  "monofun (\<lambda> b. \<Lambda> last. (b \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(last \<bar> spfDom\<cdot>f1))
                                   \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(last \<bar> spfDom\<cdot>f2))))"
  apply(rule monofunI)
  apply (simp add: below_cfun_def)
  by (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun)
    
lemma spfRanRestrict [simp]: assumes "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>b"
  shows "sbDom\<cdot>(Rep_CSPF f2\<rightharpoonup>(b\<bar>spfDom\<cdot>f2)) = spfRan\<cdot>f2"
proof -
  have "sbDom\<cdot>(b\<bar>spfDom\<cdot>f2) = spfDom\<cdot>f2" 
    using assms by auto 
  hence "(b\<bar>spfDom\<cdot>f2) \<in> dom (Rep_CSPF f2)" 
    by (metis domD spf_dom_not_empty spf_sbdom2dom spfdom2sbdom) 
  thus ?thesis 
    by (metis domIff option.collapse spfran2sbdom) 
qed

lemma "chain Y \<Longrightarrow> (\<Squnion>i. g\<cdot>(Y i)) = (g\<cdot>(\<Squnion>i. Y i))"
  by (simp add: contlub_cfun_arg)
    

  subsubsection \<open>ChannelSets\<close>
 
text{* Input channels are a subset of all channels *}
lemma spfcomp_I_subset_C [simp]: "(spfCompI f1 f2) \<subseteq> (spfCompC f1 f2)"
  using spfCompI_def spfCompC_def by blast

text{* Internal channels are a subset of all channels *}
lemma spfcomp_L_subset_C [simp]: "(spfCompL f1 f2) \<subseteq> (spfCompC f1 f2)"
  using spfCompL_def spfCompC_def by blast
 
text{* Output channels are a subset of all channels *}
lemma spfcomp_Oc_subset_C [simp]: "(spfCompOc f1 f2) \<subseteq> (spfCompC f1 f2)"
  using spfCompOc_def spfCompC_def by blast

text{* Internal channels are a subset of output channels *}
lemma spfcomp_L_subset_Oc [simp]: "(spfCompL f1 f2) \<subseteq> (spfCompOc f1 f2)"
  using spfCompL_def spfCompOc_def by blast

text{* Input channels and Internal channels do not intersect *}
lemma spfcomp_I_inter_L_empty [simp]: "(spfCompI f1 f2) \<inter> (spfCompL f1 f2) = {}"
  using spfCompI_def spfCompL_def by blast

text{* Input channels and Output channels do not intersect *}
lemma spfcomp_I_inter_Oc_empty [simp]: "(spfCompI f1 f2) \<inter> (spfCompOc f1 f2) = {}"
  using spfCompI_def spfCompOc_def by blast
    

    
subsubsection \<open>commutativness\<close> 
  
text{* Input channels are commutative *}
lemma spfcomp_I_commu: "(spfCompI f1 f2) = (spfCompI f2 f1)"
  using spfCompI_def by blast

text{* Internal channels are commutative *}
lemma spfcomp_L_commu: "(spfCompL f1 f2) = (spfCompL f2 f1)"
  using spfCompL_def by blast

text{* Output channels are commutative *}
lemma spfcomp_Oc_commu: "(spfCompOc f1 f2) = (spfCompOc f2 f1)"
  using spfCompOc_def by blast

text{* All channels are commutative *}
lemma spfcomp_C_commu: "(spfCompC f1 f2) = (spfCompC f2 f1)"
  using spfCompC_def by blast
    




  subsubsection \<open>Serial_Composition\<close> 

(* lub equalities *)
lemma sbIterate_chain: "sbDom\<cdot>(f\<cdot>(sbLeast cs)) = cs \<Longrightarrow>chain (\<lambda>i. iterate i\<cdot>f\<cdot>(sbLeast cs))"
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by simp


subsection \<open>hide\<close>  
  
lemma hide_cont[simp]:  
  shows "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"
apply(subst if_then_cont, simp_all)
by (simp add: cont_compose)

lemma hidespfwell_helper: assumes "sbDom\<cdot>b = spfDom\<cdot>f" shows "sbDom\<cdot>(f\<rightleftharpoons>b) = spfRan\<cdot>f"
  by (metis assms domIff option.exhaust_sel sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom)
  
lemma hide_spfwell[simp]: "spf_well ((\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs))))"
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  by (auto simp add: sbdom_rep_eq)

lemma spfDomHide: "spfDom\<cdot>(f \<h> cs) = spfDom\<cdot>f"
  apply(simp add: hide_def)
    by(simp add: spfDomAbs hide_cont hide_spfwell)

lemma hideSbRestrict: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" 
   shows "(hide f cs)\<rightleftharpoons>sb = (f\<rightleftharpoons>sb)\<bar>(spfRan\<cdot>f - cs)"
  apply(simp add: hide_def)
  by (simp add: assms)

lemma hideSbRestrictCh: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" and "c \<notin> cs"
   shows "((hide f cs)\<rightleftharpoons>sb) . c = (f\<rightleftharpoons>sb) . c"
  apply(simp add: hide_def)
  apply(simp add: assms)
  by (metis DiffI Int_lower1 assms(1) assms(2) hidespfwell_helper sbrestrict2sbgetch 
            sbrestrict_sbdom sbunion_getchL sbunion_idL)
   
lemma hideSpfRan: "spfRan\<cdot>(hide f cs) = spfRan\<cdot>f - cs"
  apply(subst spfran_least)
  apply(simp add: spfDomHide)
  by (metis (no_types, lifting) Int_commute Un_Diff_Int hideSbRestrict inf_sup_absorb 
            sbleast_sbdom sbrestrict_sbdom spfDomHide spfran_least)

lemma hideSubset: "spfRan\<cdot>(hide f cs) \<subseteq> spfRan\<cdot>f"
  using hideSpfRan by auto  
  

 
subsection \<open>sbFix2\<close>     
  (* This is the base for following difficult cont and monofun proofs for spfComp *)
     (* Please Note sbFix2 is just a special case of sbFix which will be evaluated later *)

  (* sbFix2 is just a special case of sbFix *)
lemma sbfix_2_sbfix2: "sbFix (F x) cs = sbFix2 F x cs"
  by (metis (mono_tags, lifting) lub_eq sbFix2_def sbFix_def)  
  
   (* sbFix2 can be unfolded as follows *)
lemma tsbfix2iter_eq: "sbFix2 F x cs = (\<Squnion> i. iter_sbfix2 F i cs x)"
  using sbFix2_def by force  
  
  
  
(* the proof strategy is very similar to the one in SPF_Feedback_JB, but as this 
   comes first in the composition theory move the explanations here  *)




lemma sbfix2_iter_eq: "sbFix2 F x cs = (\<Squnion>i. iter_sbfix2 F i cs x)"
  by (simp add: sbFix2_def)
    

    
subsubsection \<open>iter_sbfix2\<close>
  
lemma iter_sbfix2_cont[simp]: assumes "cont F"
 shows "cont (\<lambda> x. iter_sbfix2 F i cs x)"
  by (simp add: assms)
    
lemma iter_sbfix2_mono[simp]: assumes "cont F"
 shows "monofun (\<lambda> x. iter_sbfix2 F i cs x)"
  by (simp add: assms cont2mono)
    
    
lemma iter_sbfix2_mono2: assumes "cont F" and "x \<sqsubseteq> y"
  shows "\<forall>i . (iter_sbfix2 F i cs x) \<sqsubseteq> (iter_sbfix2 F i cs y)"
  by (simp add: assms(1) assms(2) cont2monofunE monofun_cfun_fun)
    
lemma iter_sbfix2_chain: assumes "sbfun_io_eq (F x) cs"
  shows "chain (\<lambda>i. iter_sbfix2 F i cs x)"
    apply (rule sbIterate_chain)
  by (simp add: assms)
    
lemma iter_sbfix2_dom: assumes "sbfun_io_eq (F x) cs"
  shows "sbDom\<cdot>(iter_sbfix2 F i cs x) =  sbDom\<cdot>((F x)\<cdot>(cs^\<bottom>))"
  apply (induct_tac i)
   apply (simp_all add: assms)
  by (metis (no_types, lifting) assms cfcomp2 cfcomp2 monofun_cfun_arg rev_below_trans 
            sbdom_eq sbleast_least sbleast_sbdom sbtake_zero)
          
 
subsubsection \<open>lub_iter_sbfix2\<close>

paragraph \<open>mono\<close>
  
lemma lub_iter_sbfix2_mono_req: assumes "x \<sqsubseteq> y" and "cont F" and "sbfun_io_eq (F x) cs"
  shows "(\<Squnion>i. (iter_sbfix2 F i cs) x) \<sqsubseteq> (\<Squnion>i. (iter_sbfix2 F i cs) y)"
proof -
  have "\<forall>i. ((iter_sbfix2 F i cs) x) \<sqsubseteq> ((iter_sbfix2 F i cs) y)"
    by (simp add: iter_sbfix2_mono2 assms(1) assms(2))
  moreover
  have "sbDom\<cdot>x = sbDom\<cdot>y"
    using assms(1) sbdom_eq by auto
  moreover
  have "sbfun_io_eq (F y) cs"
    by (metis assms(1) assms(2) assms(3) cont2monofunE monofun_cfun_fun sbdom_eq)
  ultimately
  show ?thesis
    by (simp add: lub_mono assms iter_sbfix2_mono2 iter_sbfix2_chain)
qed
  
  
paragraph \<open>cont\<close>
  
lemma chain_lub_iter_sbfix2: assumes "chain Y" and "cont F" and "sbfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_sbfix2 F ia cs (Y i))"
proof -
  have f1: "\<forall>i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chain_def by blast
  have f2: "\<forall>ia. sbfun_io_eq (F (Y ia)) cs"
    proof -
      have "(\<Squnion>n. F (Y n)\<cdot>(cs^\<bottom>)) = F (Lub Y)\<cdot>(cs^\<bottom>)"
      by (metis (no_types) assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_fun)
    thus ?thesis
      by (metis (no_types) assms(1) assms(2) assms(3) ch2ch_Rep_cfunL ch2ch_cont sbChain_dom_eq2)
  qed
    
  thus ?thesis
    apply(subst chainI,  simp_all add: assms)
    by (rule lub_iter_sbfix2_mono_req, simp_all add: f1 assms)
qed
 
lemma chain_if_lub_iter_sbfix2_req: assumes "chain Y" and "cont F" 
                                   and "sbfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "(\<Squnion>i ia. iter_sbfix2 F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_sbfix2 F ia cs (Y i))"
proof -
  have f1: "\<And>i. cont (\<lambda>x. iter_sbfix2 F i cs x)"
    by (simp add: assms(2))
  moreover
  have f2: "(\<Squnion>i. iter_sbfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_sbfix2 F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  moreover
  have f3: "\<forall>ia. sbfun_io_eq (F (Y ia)) cs"
    proof -
      have "(\<Squnion>n. F (Y n)\<cdot>(cs^\<bottom>)) = F (Lub Y)\<cdot>(cs^\<bottom>)"
      by (metis (no_types) assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_fun)
    thus ?thesis
      by (metis (no_types) assms(1) assms(2) assms(3) ch2ch_Rep_cfunL ch2ch_cont sbChain_dom_eq2)
    qed
  ultimately
  show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_sbfix2_chain)
qed
  
  
paragraph \<open>dom\<close>
  
lemma lub_iter_sbfix2_dom: assumes "sbfun_io_eq (F x) cs"
  shows "sbDom\<cdot>(\<Squnion>i. iter_sbfix2 F i cs x) =  sbDom\<cdot>((F x)\<cdot>(cs^\<bottom>))"
  by (metis (mono_tags, lifting) assms iter_sbfix2_chain iter_sbfix2_dom 
        lub_eq sbChain_dom_eq2)

      
subsubsection \<open>if_lub_iter_sbfix2\<close>   
  

paragraph \<open>mono\<close> 
  
lemma if_lub_iter_sbfix2_mono_req: assumes "x \<sqsubseteq> y" and "cont F" 
                                  and "(P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                                  and "sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) x)) x)
         \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) x)) y)"
proof (cases "(P x)")
  case True
  hence f1: "sbfun_io_eq (F x) cs"  
    by (simp add: assms(3))
  have "\<forall>i. ((iter_sbfix2 F i cs) x) \<sqsubseteq> ((iter_sbfix2 F i cs) y)"
    by (simp add: assms(1) assms(2) iter_sbfix2_mono2)
  moreover
  have f2: "sbDom\<cdot>x = sbDom\<cdot>y"
    using assms(1) sbdom_eq by auto
  ultimately
  have "(\<Squnion>i.(iter_sbfix2 F i cs) x) \<sqsubseteq> (\<Squnion>i.(iter_sbfix2 F i cs) y)"
    by (simp add: assms(1) assms(2) f1 lub_iter_sbfix2_mono_req)
  thus ?thesis
    using f2 some_below assms by auto
next
  case False
  have "sbDom\<cdot>y = sbDom\<cdot>x"
    by (metis assms(1) sbdom_eq)
  thus ?thesis     
    using False assms(4) by auto
qed
  
(* Intro lemma for sbFix based SPF is mono *) 
lemma sbfix_monoI [simp]: assumes  "cont F"  and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                          and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "monofun (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) x) )"
proof -
  have "\<And> x. \<And> y. x \<sqsubseteq> y \<Longrightarrow> ((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) x)) x) 
                              \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) x)) y)"
    proof -
      fix x :: "'a SB" and y :: "'a SB"
      assume a1: "x \<sqsubseteq> y"
      hence f2: "\<And>f p C. \<not> cont f \<or> \<not> p y \<or> \<not> p x \<or> sbDom\<cdot>(f x\<cdot>(C^\<bottom>)) \<noteq> C 
                          \<or> (p x)\<leadsto>\<Squnion>n. iter_sbfix2 f n C x \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix2 f n C y"
      using if_lub_iter_sbfix2_mono_req by blast
    have f3: "\<And>f p C. \<not> cont f \<or> p x \<or> (p x)\<leadsto>\<Squnion>n. iter_sbfix2 f n C x 
                                        \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix2 f n C y \<or> sbDom\<cdot>y = sbDom\<cdot>x"
      using a1 by (metis if_lub_iter_sbfix2_mono_req)
    have f4: "\<And>p. (p x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y \<or> p y \<or> p x"
      using a1 assms(1) if_lub_iter_sbfix2_mono_req by blast
    have f5: "\<And>p. sbDom\<cdot>(F x\<cdot>(cs^\<bottom>)) \<noteq> cs \<or> 
              (p x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x 
              \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y \<or> sbDom\<cdot>y = sbDom\<cdot>x"
      using a1 by (metis assms(1) if_lub_iter_sbfix2_mono_req)
      { assume "P x"
        moreover
        { assume "sbfun_io_eq (F x) cs 
                            \<and> \<not>(Some (\<Squnion>n. iter_sbfix2 F n cs x) 
                               \<sqsubseteq> Some (\<Squnion>n. iter_sbfix2 F n cs y))"
          moreover
          { assume "P y \<and> P x \<and> sbfun_io_eq (F x) cs 
                             \<and> \<not>(True\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x 
                                \<sqsubseteq> Some (\<Squnion>n. iter_sbfix2 F n cs y))"
            hence "\<not> P x"
            using f2 assms(1) by auto }
        ultimately have "\<not> P y \<or> \<not> P x"
          by metis }
      ultimately have "P x \<and> P y \<longrightarrow> (P x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x 
                                   \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y"
        using assms(2) by auto
      hence "sbDom\<cdot>y = sbDom\<cdot>x \<and> P x \<longrightarrow> (P x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x 
                                          \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y"
        by (meson assms(3)) }
    moreover
    { assume "\<not> P x"
      moreover
      { assume "\<exists>s. P y \<and> sbDom\<cdot>x = sbDom\<cdot>s \<and> \<not> P s"
        hence "sbDom\<cdot>y \<noteq> sbDom\<cdot>x"
          by (metis assms(3)) }
      ultimately have "sbDom\<cdot>y = sbDom\<cdot>x \<longrightarrow> (P x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x 
                                          \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y"
        using f4 by blast }
    moreover
    { assume "sbDom\<cdot>y \<noteq> sbDom\<cdot>x"
      moreover
      { assume "\<not> P x \<and> sbDom\<cdot>y \<noteq> sbDom\<cdot>x \<and> \<not> P x"
        hence "(P x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y"
          using f3 assms(1) by blast }
      ultimately have "(P x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y"
        using f5 assms(2) by blast }
    ultimately show "(P x)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix2 F n cs y"
      by satx
  qed (* :) *)
  thus ?thesis
    by (simp add: monofunI)
qed


paragraph \<open>cont\<close>   
  
  (* the second property for the cont proof of the sbFix SPF holds if "P (\<Squnion>i. Y i)" is true *)
lemma chain_if_lub_iter_sbfix2_case: assumes "chain Y" and "cont F" and "P (\<Squnion>i. Y i)"
                                  and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                                  and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_sbfix2 F ia cs) (Y i)))"
proof -
  have f1: "sbfun_io_eq (F (\<Squnion>i. Y i)) cs"
    by (simp add: assms(3) assms(4))
  have f2: "(\<Squnion>i. iter_sbfix2 F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_sbfix2 F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f3: "\<forall>ia. sbfun_io_eq (F (Y ia)) cs"
    proof -
      have "(\<Squnion>n. F (Y n)\<cdot>(cs^\<bottom>)) = F (Lub Y)\<cdot>(cs^\<bottom>)"
        by (metis (no_types) assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_fun)
      thus ?thesis
        by (metis (no_types) assms(1) assms(2) f1 ch2ch_Rep_cfunL ch2ch_cont sbChain_dom_eq2)
    qed
  have f4: "(\<Squnion>i ia. iter_sbfix2 F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_sbfix2 F ia cs (Y i))"
    by (rule chain_if_lub_iter_sbfix2_req, simp_all add: assms)
      
      
   (* PART II: show the equality for the packaging with some *)
  have f10: "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i. iter_sbfix2 F i cs (\<Squnion>i. Y i)) 
              = Some (\<Squnion>i. iter_sbfix2 F i cs (\<Squnion>i. Y i))"
    by (simp add: assms(3))
  have f11: "(\<Squnion>i. (P (Y i)) \<leadsto>  \<Squnion>ia. iter_sbfix2 F ia cs (Y i)) 
              = Some (\<Squnion>i ia. iter_sbfix2 F ia cs (Y i))"
  proof -
    have f111: "(\<Squnion>i. (P (Y i)) \<leadsto>   \<Squnion>ia. iter_sbfix2 F ia cs (Y i)) 
                 = (\<Squnion>i. Some(\<Squnion>ia. iter_sbfix2 F ia cs (Y i)))"
      by (meson assms(1) assms(3) assms(5) sbChain_dom_eq2)
    have f112_chain: "chain (\<lambda>i. \<Squnion>ia. iter_sbfix2 F ia cs (Y i))"
      by (simp add: assms(1) assms(2) chain_lub_iter_sbfix2 f1)
    have f112: "(\<Squnion>i. Some(\<Squnion>ia. iter_sbfix2 F ia cs (Y i))) 
                = Some (\<Squnion>i ia. iter_sbfix2 F ia cs (Y i))"
      by (simp add: some_lub_chain_eq3 f112_chain)
    thus ?thesis
      using f111 by auto
  qed
    
  show ?thesis
    apply(subst f10, subst f11)
    by (simp add: some_below f2 f4)
qed
  
 
(* based on the previous we can now show that the second property of contI2 holds independet of 
   the input domain *)
lemma chain_if_lub_iter_sbfix2: assumes "chain Y" and "cont F"
                               and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                               and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y" 
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_sbfix2 F ia cs) (Y i)))"
proof (cases "P (\<Squnion>i. Y i)")
  case True
  thus ?thesis
    using  chain_if_lub_iter_sbfix2_case assms by blast
next
  case False
  hence f1: "(P (\<Squnion>i. Y i)) = False"
    by simp
  thus ?thesis
  proof -
    have f2: "\<forall>i. sbDom\<cdot>(Y i) = sbDom\<cdot>(\<Squnion>i. Y i)"
      by (simp add: sbChain_dom_eq2 assms(1))
    hence f3: "\<forall>i. (P (Y i)) = (P (\<Squnion>i. Y i))"
      by (metis assms(4))
    thus ?thesis
      by (simp add: f3 f1)
  qed
qed
  

(* Insertion lemma for cont proofs sbfix *)
lemma sbfix_contI [simp]: assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                          and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "cont (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix2 F i cs) x) )"
  apply (rule contI2)
   apply (rule sbfix_monoI, simp add: assms(1), simp add: assms(2), metis assms(3))
  using chain_if_lub_iter_sbfix2 assms by blast  
    

subsection \<open>sbFix\<close>  

subsubsection \<open>compatibility lemmas\<close>

(* cont in X intro rule for SPFs based on sbFix  *)
lemma sbfix_contI2 [simp]: fixes F :: "'m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB"
                            assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs"
                            and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
                            shows "cont (\<lambda> x. (P x) \<leadsto> sbFix (F x) cs)"
proof -
  have f1: "(\<lambda> x. (P x) \<leadsto> sbFix (F x) cs) = (\<lambda> x. (P x) \<leadsto> sbFix2 F x cs)"
    apply (subst sbfix_2_sbfix2)
    by simp
  show ?thesis
    apply (subst f1, subst sbFix2_def)
    using sbfix_contI assms by blast
qed

(* the domain is always the same if io_eq holds *)
lemma iter_sbfix_dom: assumes "sbfun_io_eq F cs"
  shows "sbDom\<cdot>(iterate i\<cdot>F\<cdot>(sbLeast cs)) = cs"
    proof (induction i)
      case 0
      thus ?case
        by (simp add: assms(1))
    next
      case (Suc i)
      thus ?case
      proof -
        have "\<And>c. (c\<cdot>(sbLeast cs)::'a SB) \<sqsubseteq> c\<cdot>(F\<cdot>(sbLeast cs))"
          by (simp add: assms monofun_cfun_arg)
        thus ?thesis
          by (metis (no_types) Suc iterate_Suc2 sbdom_eq)
      qed
qed

  (* if input und output of F is equals cs sbFix of f has the same domain *)
lemma sbfix_dom: assumes "sbfun_io_eq (F) cs"
  shows "sbDom\<cdot>(sbFix F cs) =  cs"
proof -
  have "\<And>n. sbfun_io_eq (iterate n\<cdot>(F)) cs"
    by (simp add: assms iter_sbfix_dom)
  thus ?thesis
    by (metis (no_types, lifting) assms sbChain_dom_eq2 sbFix_def sbIterate_chain)
qed


subsubsection \<open>fixed point properties\<close>
  (* show that sbFix works similar to the fix operator which works on a pcpo function
     hence "sbfun_io_eq F cs" is a crucial assumptions for the following lemmas, because for
     a fixed domain cs there exists a least sb *)

  (* sbFix calculates the fixed point *)
lemma sbfix_eq: assumes io_eq: "sbfun_io_eq F cs"
  shows "(sbFix F cs) = F\<cdot>(sbFix F cs)"
  apply (simp add: sbFix_def)
   (* perform an chain index shift by 1 *)
  apply (subst lub_range_shift [of _ 1, symmetric])
    apply (simp add: io_eq sbIterate_chain)
    apply (subst contlub_cfun_arg)
      apply (simp add: io_eq sbIterate_chain)
      by simp

  (* the fixed point calculated bs sbFix is smaller than any other fixed point*)
lemma sbfix_least_below: assumes "sbfun_io_eq F cs" and "sbDom\<cdot>x = cs"
  shows "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> (sbFix F cs) \<sqsubseteq> x"
  apply (simp add: sbFix_def)
  apply (rule lub_below)
    apply (simp add: assms sbIterate_chain)
    apply (induct_tac i)
      apply (simp add: assms(2))
      apply (simp add: assms(1))
      apply (erule rev_below_trans)
      by (erule monofun_cfun_arg)


  (* sbFix calculates the least fixed point *)
lemma sbfix_least: assumes "sbfun_io_eq F cs" and "sbDom\<cdot>x = cs"
                    and "F\<cdot>x = x"
  shows "(sbFix F cs) \<sqsubseteq> x"
  by (simp add: assms(1) assms(2) assms(3) sbfix_least_below)

 (* Intro rule for sbfix_eq *)
lemma sbfix_eqI: assumes fp: "F\<cdot>x = x" and lst: "\<And>z. sbDom\<cdot>z = cs \<Longrightarrow> F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
                 and "sbfun_io_eq F cs" and "sbDom\<cdot>x = cs"
  shows "(sbFix F cs) = x"
proof -
  have f1: "sbFix F cs \<sqsubseteq> x"
    by (simp add: assms(3) assms(4) fp sbfix_least)
  have f2: "sbDom\<cdot>(sbFix F cs) = cs"
    using assms(3) sbfix_dom by blast
  have "sbFix F cs \<sqsubseteq> x"
    using f1 by meson
  thus ?thesis
    using f2 by (metis assms(3) below_antisym lst sbfix_eq)
qed


  (* if sbFix = \<bottom> then F \<bottom> = \<bottom> where \<bottom> = sbLeast cs *)
lemma sbfix_least_iff: assumes "sbfun_io_eq F cs"
  shows "((sbFix F cs) = sbLeast cs) = (F\<cdot>(sbLeast cs) = sbLeast cs)"
proof -
  have "F\<cdot>(sbFix F cs) = sbFix F cs"
    by (metis (full_types) assms sbfix_eq)
  thus ?thesis
    by (metis assms po_eq_conv sbfix_dom sbfix_least sbleast_least)
qed

  (* sbFix is "strict" concerning the least sb with domain cs *)
lemma sbfix_strict: assumes "sbfun_io_eq F cs" and "F\<cdot>(sbLeast cs) = (sbLeast cs)"
  shows "(sbFix F cs) = sbLeast cs"
  by (simp add: assms(2) sbfix_least_iff)

  (* if sbLeast is not a fixed point sbFix does not calculate it *)
lemma sbfix_defined: assumes "sbfun_io_eq F cs" and "F\<cdot>(sbLeast cs) \<noteq> (sbLeast cs)"
  shows "(sbFix F cs) \<noteq> sbLeast cs"
  by (metis assms(1) assms(2) sbfix_eq)

  (* sbFix applied to identity delivers sbLeast *)
lemma sbfix_id [simp]: "(sbFix (\<Lambda> x. x) cs) = (sbLeast cs)"
  by (simp add: sbfix_strict)

  (* sbFix applied to a constant function is the constant *)
lemma sbfix_const [simp]: assumes "sbDom\<cdot>c = cs"
  shows "(sbFix (\<Lambda> x. c) cs) = c"
proof -
  have "sbfun_io_eq (\<Lambda> x. c) cs"
    by (simp add: assms)
  thus ?thesis
    by (metis (no_types) beta_cfun cont_const sbfix_eq)
qed

  (* if P holds for sbLeast and every "F\<cdot>x" it also holds for sbFix F *)
lemma sbfix_ind: assumes "sbfun_io_eq F cs"
                  and "adm P" and "P (sbLeast cs)"
                  and "\<And> x. \<lbrakk>(sbDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F\<cdot>x)"
  shows "P (sbFix F cs)"
proof -
  have f1: "\<And> n. sbDom\<cdot>(iterate n\<cdot>F\<cdot>(sbLeast cs)) = cs"
    by (simp add: assms(1) iter_sbfix_dom)
  show ?thesis
    unfolding sbFix_def
    apply (subst admD, simp_all add: assms)
      apply (simp add: assms(1) sbIterate_chain)
      apply (rule nat_induct, simp add: assms(3))
      by (simp add: assms(4) f1)
qed

  (* the previous also holds if F is not a cfun but cont *)
lemma cont_sbfix_ind: assumes "cont F" and "sbfun_io_eq (Abs_cfun F) cs"
                       and "adm P" and "P (sbLeast cs)"
                       and "\<And> x. \<lbrakk>(sbDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F x)"
  shows "P (sbFix (Abs_cfun F) cs)"
  apply (rule sbfix_ind, simp_all add: assms)
  using assms(1) assms(2) by auto

  (* the same holds if the induction starts at F\<cdot>F\<cdot>x*)
lemma sbfix_ind2:  assumes "sbfun_io_eq F cs"
                    and "adm P" and s0: "P ((sbLeast cs))" and s1: "P (F\<cdot>(sbLeast cs))"
                    and s2: "\<And> x. \<lbrakk>(sbDom\<cdot>x) = cs; P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
  shows "P (sbFix F cs)"
  unfolding sbFix_def
  apply (subst admD, simp_all add: assms)
    apply (simp add: assms(1) sbIterate_chain)
    apply (rule nat_less_induct)
    apply (case_tac n)
      apply (simp add: s0)
      apply (case_tac nat)
        apply (simp add: s1)
        apply (frule_tac x=nat in spec)
        by (simp add: assms(1) iter_sbfix_dom s2)  
  
          
subsection \<open>spfLeast\<close>
        
lemma spfLeast_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = In) \<leadsto> (sbLeast Out))" 
  by simp  
  
lemma spfLeast_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = In) \<leadsto> (sbLeast Out))" 
  by simp
  
lemma spfLeast_well: "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = In) \<leadsto> (sbLeast Out))"        
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by(auto)       

lemma spfLeast_dom [simp]: "spfDom\<cdot>(spfLeast In Out) = In"
  by(simp add: spfLeast_def spfDomAbs spfLeast_cont spfLeast_well)

lemma spfLeast_ran[simp]: "spfRan\<cdot>(spfLeast In Out) = Out"
proof - 
  have "sbDom\<cdot>(sbLeast Out) = Out"
    by simp
  thus ?thesis
    apply(simp add: spfLeast_def)
    apply(simp add: spfRan_def spfLeast_cont spfLeast_well)
    by (smt option.distinct(1) option.inject ran2exists ranI sbleast_sbdom someI)
qed
 
lemma spfLeast_bottom: assumes "spfDom\<cdot>f = In" and "spfRan\<cdot>f = Out"
  shows "(spfLeast In Out) \<sqsubseteq> f"
proof - 
  have f0: "\<And>sb c. sbDom\<cdot>sb = In \<and> c \<in> sbDom\<cdot>(spfLeast In Out \<rightleftharpoons> sb) \<longrightarrow> (spfLeast In Out \<rightleftharpoons> sb) . c = \<epsilon>"
  proof
    fix sb
    fix c
    assume f01: "sbDom\<cdot>sb = In \<and> c \<in> sbDom\<cdot>(spfLeast In Out \<rightleftharpoons> sb)"
    show "(spfLeast In Out \<rightleftharpoons> sb) . c = \<epsilon>"
      apply(simp add: spfLeast_def spfLeast_cont spfLeast_well)
      by (metis (full_types) f01 sbleast_getch spfLeast_dom spfLeast_ran spf_ran_2_tsbdom2)
  qed
  have f1: "\<And>sb. sbDom\<cdot>sb = In \<longrightarrow> (spfLeast In Out)\<rightleftharpoons>sb \<sqsubseteq> f\<rightleftharpoons>sb"
    apply(subst sb_below)
     apply (metis assms(1) assms(2) option.collapse spfLeast_dom spfLeast_ran spf_ran_2_tsbdom2 spfdom2sbdom)
    apply (metis (no_types, lifting) assms(1) assms(2) f0 monofun_cfun_arg monofun_cfun_fun option.collapse po_eq_conv sbleast_getch sbleast_least spfLeast_dom spfLeast_ran spf_ran_2_tsbdom2 spfdom2sbdom)  
    by simp
  show ?thesis
    apply(simp add: spfLeast_def)  
      by (metis assms(1) f1 spfLeast_def spfLeast_dom spf_belowI)
qed  
    
    
subsection \<open>spfRestrict\<close>
  
lemma spfRestrict_mono: "monofun (\<lambda> f. if (spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out) then f else (spfLeast In Out))"
  by (simp add: monofun_def spfdom_eq spfran_eq)

lemma spfRestrict_cont: "cont (\<lambda> f. if (spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out) then f else (spfLeast In Out))"
  by (smt Cont.contI2 lub_eq monofun_def po_eq_conv spfLeast_bottom spfLeast_dom spfLeast_ran spfdom_eq spfdom_eq_lub spfran_eq spfran_eq_lub)    
  
lemma spfRestrict_apply: assumes "spfDom\<cdot>f = In" and "spfRan\<cdot>f = Out" shows "spfRestrict In Out\<cdot>f = f"
  apply(simp add: spfRestrict_def)  
  by (simp add: spfRestrict_cont assms)  
    
lemma spfRestrict_dom[simp]: "spfDom\<cdot>(spfRestrict In Out\<cdot>f) = In" 
proof(cases "spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out")
  case True
  then show ?thesis 
    by (simp add: spfRestrict_apply)
next
  case False
  then show ?thesis 
    by (simp add: spfLeast_dom spfRestrict_cont spfRestrict_def)
qed 
  
lemma spfRestrict_ran[simp]: "spfRan\<cdot>(spfRestrict In Out\<cdot>f) = Out" 
proof(cases "spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out")
  case True
  then show ?thesis 
    by (simp add: spfRestrict_apply)
next
  case False
  then show ?thesis 
    by (simp add: spfLeast_ran spfRestrict_cont spfRestrict_def)
qed 
    
    
    
    
    
section \<open>Lemmas for Composition\<close>
  (* this is only a part of the composition related lemmata, see SPF_Comp.thy *)
    
subsection \<open>spfCompH\<close>
(* ----------------------------------------------------------------------- *)
  (* similar to spfCompH2 but does not output the input, nevertheless its lub 
     is equal to the one of spfCompH2 as shown later *)

subsubsection \<open>basic properties\<close>
  
paragraph \<open>cont\<close>
  
lemma spfCompH_cont[simp]: 
  shows "cont (\<lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"
proof -
  have f1: "cont (\<lambda> z. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  moreover 
  have f2: "cont (\<lambda> z. (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>z. sbUnion\<cdot>(Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1))) 
        \<and> cont (\<lambda>z. Rep_SPF f2\<cdot>((x \<uplus> z)\<bar>spfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> z. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)) 
                          \<uplus> (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed
  
lemma spfCompH_cont2[simp]: 
  shows "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"
proof -
  have f0: "cont (\<lambda>x. (x \<uplus> z))"
    by simp
      
  have f1: "cont (\<lambda> x. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  moreover
  have f2: "cont (\<lambda> x. (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>x. sbUnion\<cdot>(Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1))) 
        \<and> cont (\<lambda>x. Rep_SPF f2\<cdot>((x \<uplus> z)\<bar>spfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> x. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)) 
                                                   \<uplus> (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by simp
qed
  
lemma spfCompH_continX[simp]: "cont (\<lambda> x. spfCompH f1 f2 x)"
proof -
  have "cont (\<lambda> x. \<Lambda> z. ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2))))"
    by (simp add: cont2cont_LAM)
  thus ?thesis
    by (simp add: spfCompH_def)
qed
   
paragraph \<open>dom\<close>
  
lemma spfCompH_dom [simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
                            and "sbDom\<cdot>sb = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
                          shows "sbDom\<cdot>((spfCompH f1 f2 x)\<cdot>sb) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
proof -
  have f1: "sbDom\<cdot>(f1 \<rightleftharpoons> ((x \<uplus> sb)  \<bar> spfDom\<cdot>f1)) = spfRan\<cdot>f1"
    by (simp add: spfCompI_def assms(1) assms(2) inf_sup_aci(6))
      moreover
  have f2: "sbDom\<cdot>(f2 \<rightleftharpoons> ((x \<uplus> sb)  \<bar> spfDom\<cdot>f2)) = spfRan\<cdot>f2"
    by (simp add: spfCompI_def assms(1) assms(2) sup.coboundedI1)
      ultimately
  show ?thesis
    by (simp add: f1 f2 spfCompH_def assms)
qed
  
paragraph \<open>commu\<close>  
  
lemma spfcomph_commu: assumes  "spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"
                       and "sbDom\<cdot>tb = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
                       and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(spfCompH f1 f2 x)\<cdot>tb = (spfCompH f2 f1 x)\<cdot>tb"
proof -
  have "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>(x \<uplus> tb)"
    by (simp add: assms(2) assms(3) inf_sup_aci(6) spfCompI_def)
  hence f1:  "sbDom\<cdot>(f1\<rightleftharpoons>((x \<uplus> tb)  \<bar> spfDom\<cdot>f1)) = spfRan\<cdot>f1"
    using spfRanRestrict by blast
   
    
  have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>(x \<uplus> tb)"
    by (simp add: assms(2) assms(3) sup.absorb_iff2 sup.commute sup_left_commute spfCompI_def)   
  hence f2:  "sbDom\<cdot>(f2\<rightleftharpoons>((x \<uplus> tb)  \<bar> spfDom\<cdot>f2)) = spfRan\<cdot>f2"
    using spfRanRestrict by blast
      
  from f1 f2 have f3: "sbDom\<cdot>(f1\<rightleftharpoons>((x \<uplus> tb)  \<bar> spfDom\<cdot>f1)) 
                        \<inter>  sbDom\<cdot>(f2\<rightleftharpoons>((x \<uplus> tb)  \<bar> spfDom\<cdot>f2)) = {}"
    by (simp add: assms(1))
  
  thus ?thesis
    apply (simp add: spfCompH_def)
    apply (rule sbunion_commutative)
    by simp
qed

 
subsubsection \<open>iterate spfCompH\<close>  
  
lemma iter_spfCompH_cont[simp]: "cont (\<lambda>x. iter_spfCompH f1 f2 i x)"
  by simp
    
lemma iter_spfCompH_mono[simp]: "monofun (\<lambda>x. iter_spfCompH f1 f2 i x)"
  by (simp add: cont2mono)
    
lemma iter_spfCompH_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_spfCompH f1 f2 i) x) \<sqsubseteq> ((iter_spfCompH f1 f2 i) y)"
  using assms monofun_def by fastforce
  
lemma iter_spfCompH_chain[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "chain (\<lambda> i. iter_spfCompH f1 f2 i x)"
  by (simp add: assms sbIterate_chain)
    
lemma iter_spfCompH_dom[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "sbDom\<cdot>(iter_spfCompH f1 f2 i x) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  by (simp add: assms iter_sbfix2_dom)

lemma iter_spfcomph_commu: assumes "spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"
                           and "sbDom\<cdot>tb = spfCompI f1 f2" 
  shows "(iter_spfCompH f1 f2 i tb) = (iter_spfCompH f2 f1 i tb)"
proof (induction i)
  case 0
  then show ?case
    by (simp add: sup_commute)
next
  case (Suc i)
  then show ?case
   apply (unfold iterate_Suc)
   apply (subst spfcomph_commu, simp_all add: assms)
   by (metis (no_types) assms(2) iter_spfCompH_dom)
qed
  
subsubsection \<open>lub iterate spfCompH\<close> 
  
lemma lub_iter_spfCompH_dom[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "sbDom\<cdot>(\<Squnion>i. iter_spfCompH f1 f2 i x) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  by (simp add: lub_iter_sbfix2_dom assms) 
    
    
    
subsection \<open>spfCompH2\<close>
(* ----------------------------------------------------------------------- *)
  (* WARNING this helper is obsolete *)
  
subsubsection \<open>basic properties\<close>  

  
(* Proof comphelper properties by referring to original comphelper *)
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

lemma helpermonoinX[simp]: shows "monofun (\<lambda> x. spfCompH2 f1 f2 x)"
  by(simp add: spfCompH2_def)

lemma helpercontinX [simp]: shows "cont (\<lambda> x. spfCompH2 f1 f2 x)"
  proof -
     have "\<forall>x. cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons>(z \<bar> spfDom\<cdot>f2)))"
     by simp
     hence "cont (\<lambda>x. \<Lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
       by (simp add: cont2cont_LAM)
     thus ?thesis
       by (simp add: spfCompH2_def)
  qed

lemma spfCompOld_tospfH2: "(spfCompOld f1 f2) 
 = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> 
                  (\<Squnion>i. iterate i\<cdot>(spfCompH2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))) \<bar> spfCompOc f1 f2)"
  apply (subst spfCompOld_def, subst spfCompH2_def, subst spfCompC_def, 
                subst (1 2) spfCompI_def, subst spfCompOc_def)    
  by (metis (no_types) spfCompC_def spfCompI_def spfCompOc_def)
    
    
lemma spfCompH2_getch_outofrange: assumes "c \<notin> spfRan\<cdot>f1" 
                                and "c \<notin> spfRan\<cdot>f2" 
                                and "sbDom\<cdot>sb = spfCompC f1 f2"
  shows "((spfCompH2 f1 f2 x)\<cdot>sb) . c = x . c"
  apply (simp add: spfCompH2_def)
  apply (subst sbunion_getchL)
  apply (simp add: spfCompC_def assms(2) assms(3) subsetI)
  by (simp add: spfCompC_def Un_assoc assms(1) assms(3))

lemma spfCompH2_dom [simp]: assumes "sbDom\<cdot>sb = spfCompC f1 f2"
  shows "sbDom\<cdot>((spfCompH2 f1 f2 x)\<cdot>sb) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (simp add: spfCompH2_def)
  proof -
    have f1: "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb"
      by (simp add: spfCompC_def Un_commute Un_left_commute assms)
    have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb"
      using spfCompC_def assms by auto
    thus "sbDom\<cdot>x \<union> (sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) \<union> (sbDom\<cdot> (f2 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f2))) 
                = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
qed
 
  
subsubsection \<open>iterate spfCompH2\<close>
  
  
(* for all i the i'th iteration on spfCompOld is cont as application iterate is cont on cont fun *) 
lemma iter_spfcompH2_cont2[simp]: "cont (iter_spfcompH2 f1 f2 i)"
  by simp
    
lemma iter_spfcompH2_mono[simp]:  "monofun (iter_spfcompH2 f1 f2 i)"
  by simp
    
(* replaced iter_spfcompH2_chain *)
lemma iter_spfcompH2_chain [simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "chain  (\<lambda>i. iter_spfcompH2 f1 f2 i x)"
  apply(rule sbIterate_chain)
  by (simp add: spfCompC_def spfCompI_def assms inf_sup_aci(6))
    
  
lemma spfCompH2_itDom[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "sbfun_io_eq (iterate i\<cdot>(spfCompH2 f1 f2 x)) (spfCompC f1 f2)"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: spfCompC_def spfCompI_def assms inf_sup_aci(6))
  
  
lemma spfCompH2_itgetChI: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
                      and "spfComp_well f1 f2"
                      and "c \<in> spfCompI f1 f2"
  shows "iter_spfcompH2 f1 f2 (Suc i) x . c = x .c"
  apply (unfold iterate_Suc, subst spfCompH2_def)
  apply (simp)
  apply (subst sbunion_getchL)
  apply (metis spfCompC_def DiffD2 spfCompI_def UnI2 assms(1) assms(3) inf_sup_ord(4) 
               le_supI1 spfCompH2_itDom spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis spfCompC_def DiffD2 spfCompI_def UnI1 Un_upper1 assms(1) assms(3) 
                le_supI1 spfCompH2_itDom spfRanRestrict)
   by (simp)


lemma spfCompH2_itResI: assumes "sbDom\<cdot>x = spfCompI f1 f2"             
  shows "(iter_spfcompH2 f1 f2 (Suc i) x) \<bar> (spfCompI f1 f2) = x"
  apply (rule sb_eq)
   apply (simp add: assms(1) inf_sup_aci(1) inf_sup_aci(6))
   using assms(1)  spfCompH2_itgetChI by fastforce
  

subsubsection \<open>lub iterate spfCompH2\<close>
   
(* the lub over the iterations of spfCompOldH2 is monotone if the assumtions hold *)
  (* requires chain property, hence the input must have the right domain *)
lemma lub_iter_spfCompH2_mono_req: assumes "x \<sqsubseteq> y" and  "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) y)"
    apply (rule lub_iter_sbfix2_mono_req)
    by (simp_all add: assms inf_sup_aci(6) spfCompI_def spfCompC_def)

(* the lub over the iteration is always mono, the correct domain is assured via \<leadsto> *)
lemma if_lub_iter_spfCompH2_mono_req: assumes "x \<sqsubseteq> y" 
  shows "((\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x)) x) 
              \<sqsubseteq> ((\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x)) y)"
  apply (rule if_lub_iter_sbfix2_mono_req)
    by (simp_all add: assms inf_sup_aci(6) spfCompI_def spfCompC_def)
    
(* the lub of iter_spfcompH2, when applied to a chain, is again a chain *)
  (* this property follows from the monotonicy of lub_iter_spfCompH2 *)
lemma chain_lub_iter_spfcompH2: assumes  "chain Y" 
                                and  "(sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))"   
  apply (rule chain_lub_iter_sbfix2)
  by (simp_all add: assms inf_sup_aci(6) spfCompI_def spfCompC_def)
  
  
  
  
  
  
  
  
section \<open>Legacy\<close>
  (* please do not use the lemmas below anymore *)

subsection \<open>Alternative definition of 'm SPF\<close>

(* show that the original definition is equivalent with mine *)

(* Original definition used before *)
definition spf_mono :: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> bool" where
"spf_mono f \<equiv> \<forall>b1 b2. (b1 \<in> dom f \<and> b2 \<in> dom f \<and> b1 \<sqsubseteq> b2) \<longrightarrow> the (f b1) \<sqsubseteq> the (f b2)"

definition spf_contlub :: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> bool" where
"spf_contlub f \<equiv> \<forall>K. (chain K \<and> (K 0) \<in> dom f) \<longrightarrow> the (f (\<Squnion> i. K i)) \<sqsubseteq> (\<Squnion> i. the (f (K i)))"


lemma spf_monoI: assumes "\<And>b1 b2. b1 \<in> dom f \<Longrightarrow> b2 \<in> dom f \<Longrightarrow> b1 \<sqsubseteq> b2 \<Longrightarrow> (f\<rightharpoonup>b1) \<sqsubseteq> f\<rightharpoonup>b2"
  shows "spf_mono f"
  by (simp add: assms spf_mono_def)


lemma spf_contlubI: assumes " \<And>Y. chain Y \<Longrightarrow> (Y 0) \<in> dom f \<Longrightarrow>  
                                    (f \<rightharpoonup>(\<Squnion> i. Y i)) \<sqsubseteq> (\<Squnion> i. (f\<rightharpoonup>(Y i)))"
  shows "spf_contlub f"
by (meson assms spf_contlub_def sbChain_dom_eq2 sbdom_eq)

(* show that "spf_mono" implies "monofun". the second assumtions comes from spf_well *)
lemma spf_mono2monofun [simp]: assumes "spf_mono f" and "\<forall>b. b \<in> dom f \<longleftrightarrow> sbDom\<cdot>b = In"
  shows "monofun f"
  proof (rule monofunI)
    fix x y :: "'a SB"
    assume "x\<sqsubseteq>y"
    hence "sbDom\<cdot>x = sbDom\<cdot>y" 
      using sbdom_eq by blast
    hence "x\<in> dom f \<longleftrightarrow> y\<in>dom f" 
      by (simp add: assms(2))
    thus "f x \<sqsubseteq> f y "
      by (metis (no_types, lifting) \<open>x \<sqsubseteq> y\<close> assms(1) domD domIff option.sel po_eq_conv 
            some_below spf_mono_def)
  qed

  (* monofun implies spf_mono *)
  lemma monofun2spf_mono: assumes "monofun f"
  shows "spf_mono f"
  by (metis assms monofun_def op_the_mono spf_mono_def)

(* ToDo: entweder löschen oder schöner machen *)
lemma spf_contlub2contlub: assumes "spf_contlub f" and "\<forall>b. b \<in> dom f \<longleftrightarrow> sbDom\<cdot>b = In" 
  and "chain Y" and "monofun f"
  shows "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
  proof (cases "Y 0 \<in> dom f")
   case True
   hence "\<forall>i. Y i \<in> dom f" by (simp add: assms(2) assms(3) sbChain_dom_eq2)
   hence f1: "the (f (\<Squnion> i. Y i)) \<sqsubseteq> (\<Squnion> i. the (f (Y i)))"
    using assms(1) assms(3) spf_contlub_def by fastforce
   hence "sbDom\<cdot>(Y 0) = In" using assms(2) True  by blast
   hence "sbDom\<cdot>((\<Squnion>i. Y i)) = In" by (simp add: assms(3) sbChain_dom_eq2)
   hence "(\<Squnion>i. Y i) \<in> dom f" by (simp add: assms(2))
   hence n1:"f (\<Squnion>i. Y i) \<noteq> None" by blast
   have "chain (\<lambda>i. f (Y i))" by (simp add: assms(3) assms(4) ch2ch_monofun)
   hence "\<forall>i. (f (Y i) \<noteq> None)" using \<open>\<forall>i. Y i \<in> dom f\<close> by blast
   hence "(\<Squnion> i. (f (Y i))) \<noteq> None" by (simp add: \<open>chain (\<lambda>i. f (Y i))\<close> op_is_lub optionLub_def)
   hence "the (f (\<Squnion> i. Y i)) \<sqsubseteq> the (\<Squnion> i. (f (Y i)))" 
     using \<open>chain (\<lambda>i. f (Y i))\<close> local.f1 op_the_lub by fastforce
   thus ?thesis using below_option_def by (metis \<open>(\<Squnion>i. f (Y i)) \<noteq> None\<close> n1)
  next
  case False
  hence "\<forall>i. Y i \<notin> dom f" by (simp add: assms(2) assms(3) sbChain_dom_eq2)
  hence "sbDom\<cdot>(Y 0) \<noteq> In" using assms(2) by blast
  hence "sbDom\<cdot>((\<Squnion>i. Y i)) \<noteq> In" by (simp add: assms(3) sbChain_dom_eq2)
  hence "(\<Squnion>i. Y i) \<notin> dom f" by (simp add: assms(2))
  thus ?thesis by (metis \<open>\<forall>i. Y i \<notin> dom f\<close> below_refl domIff is_ub_thelub po_class.chainI)
qed


(* spf_contlub + more implies cont *)
lemma spf_cont2cont: assumes "spf_contlub f" and "spf_mono f" and "\<forall>b. b \<in> dom f \<longleftrightarrow> sbDom\<cdot>b = In"
  shows "cont f"
  proof (rule contI2)
    show "monofun f" 
      using assms(2) assms(3) spf_mono2monofun by blast
   thus "\<forall>Y. chain Y \<longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))" 
     using assms(1) assms(3) spf_contlub2contlub by blast
qed

  
  


(*
definition no_selfloops:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"no_selfloops f1 f2 \<equiv> spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1 = {}
                    \<and> spfDom\<cdot>f2 \<inter> spfRan\<cdot>f2 = {}"
*)
(* set of feedback channels *) (* TODO: rename *)


  
(* for legacy purposes *)
text \<open>Dummy patterns for abstraction\<close>
translations
  "\<LL> _ . t" => "CONST Abs_CSPF (\<lambda> _ . t)"  
  
definition pL :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"pL f1 f2 \<equiv> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f1)
                      \<union> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2)"
  
  

definition spfComp_well:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"spfComp_well f1 f2 \<equiv> spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"  
  
  
lemma spfsblift_ran [simp]: "(\<exists> d. (d \<in> (ran (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(F\<cdot>b))\<bar>Out)))))"
  oops


lemma spfsblift_sbran[simp]: "spfRan\<cdot>(spfSbLift F In Out) = Out"
  apply(simp add: spfSbLift_def spfRan_def)
  oops

lemma spfsbliftE[simp]: assumes "sbDom\<cdot>g = In"
  shows "(Rep_SPF (spfSbLift f In Out))\<cdot>g = Some ((\<up>f\<cdot>g) \<bar> Out)"
  oops
(* using  assms rep_abs_cspf spfSbLift_def by auto *)  
  
  
  
 (* LEGACY
text{* pL channels are a subset of internal channels *}
lemma spfcomp_pl_subset_L [simp]: "(pL f1 f2) = (spfCompL f1 f2)"
  using pL_def spfCompL_def apply simp

text{* pL channels are a subset of all channels *}    
lemma spfcomp_pL_subset_C [simp]: "(pL f1 f2) \<subseteq> (spfCompC f1 f2)"
  using pL_def spfCompC_def by blast
*) 
  
(* LEGACY *)
lemma spfI_sub_C[simp]: "spfCompI f1 f2 \<subseteq> spfCompC f1 f2"
  by simp

lemma spfOc_sub_C[simp]: "spfCompOc f1 f2 \<subseteq> spfCompC f1 f2"
  by simp 
  
  
end