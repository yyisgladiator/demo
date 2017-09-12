(*  Title:        SPF
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Stream Processing Functions"
*)

theory SPF
imports SB

begin
  default_sort message 

    (* REMOVE THIS ASAP *)
(* instatiate our message space*)
instantiation nat :: message
begin
  definition ctype_nat :: "channel \<Rightarrow> nat set" where
  "ctype c = range nat"

instance ..
end

lemma [simp]: "cs \<subseteq> ((ctype c) :: nat set)"
  apply(simp add: ctype_nat_def)
  by(metis subset_UNIV subset_image_iff transfer_int_nat_set_return_embed)


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
    by (simp add: below_option_def chY is_lub_maximal lub_eqI po_class.chainE rangeI stbundle_allempty ub_rangeI)
  next
  case False
  hence "\<forall>i. (sbDom\<cdot>(Y i) \<noteq> {})" by (metis empty_iff rangeI sbleast_sbdom sb_eq)
  hence "(\<Squnion>i. Y i) \<noteq> sbLeast {}" using chY by (auto simp add: sbChain_dom_eq2)
  thus ?thesis
   by (metis (mono_tags, lifting) False below_option_def fun_upd_apply is_lub_maximal rangeI ub_rangeI)
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
  lemma spf_well_adm2[simp]: "adm (\<lambda>f. \<exists>Out. \<forall>b. b \<in> dom (Rep_cfun f) \<longrightarrow> sbDom\<cdot>(the (f\<cdot>b)) = Out)" (is "adm( ?P )")   
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
            then have "\<exists>C. Rep_cfun (Y i)\<rightharpoonup>aa C \<sqsubseteq> Rep_cfun (Lub Y)\<rightharpoonup>aa (CC i)"
              by (meson below_option_def chY is_ub_thelub monofun_cfun_fun)
            then have "(\<exists>C. sbDom\<cdot>Rep_cfun (Y i)\<rightharpoonup>aa C \<noteq> CC i) \<or> (\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> sbDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C)"
              by (metis (no_types) sbdom_eq) }
          ultimately have "(\<exists>C. sbDom\<cdot>Rep_cfun (Y i)\<rightharpoonup>aa C \<noteq> CC i) \<or> (\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> sbDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C)"
            by fastforce }
        ultimately have "\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> sbDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C"
          by (metis \<open>dom (Rep_cfun (Y i)) = dom (Rep_cfun (\<Squnion>i. Y i))\<close>) }
      then show ?thesis
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
definition Rep_CSPF:: "'m SPF \<Rightarrow> ('m SB \<rightharpoonup> 'm SB)" where
"Rep_CSPF F \<equiv>  Rep_cfun (Rep_SPF F) "

(* Shorter version to get from normal functions to 'm SPF's *)
  (* of course the argument should be "spf_well" and "cont" *)
definition Abs_CSPF:: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> 'm SPF" where
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

(* for legacy purposes *)
text \<open>Dummy patterns for abstraction\<close>
translations
  "\<LL> _ . t" => "CONST Abs_CSPF (\<lambda> _ . t)"

subsection \<open>apply\<close>

(* harpoon and Rep operation all in one for simpler SPF on SB applications *)
abbreviation theRep_abbrv :: "'a SPF \<Rightarrow> 'a SB \<Rightarrow> 'a SB " ("_\<rightleftharpoons>_") where
"(f \<rightleftharpoons> s) \<equiv> the ((Rep_CSPF f) s)"


subsection \<open>fix\<close>

definition sbFix :: "('m SB \<rightarrow> 'm SB) \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix F cs \<equiv>  (\<Squnion>i. iterate i\<cdot>F\<cdot>(cs^\<bottom>))"

(* adds the input to the original sbFix definition *)
definition sbFix2 :: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> 'm SB  \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation iter_sbfix2:: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_sbfix2 F i cs \<equiv> (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation sbfun_io_eq :: "('m SB \<rightarrow> 'm SB)  \<Rightarrow> channel set \<Rightarrow> bool" where
"sbfun_io_eq f cs \<equiv> sbDom\<cdot>(f\<cdot>(cs^\<bottom>)) = cs"


subsection \<open>composition\<close>

(* redefined composition channel sets *)
definition spfCompI :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompI f1 f2 \<equiv> (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

definition spfCompOc :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompOc f1 f2 \<equiv> (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

definition spfCompL :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompL f1 f2 \<equiv> (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<inter> (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

definition spfCompC :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompC f1 f2 \<equiv> spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"

(* newer spfcopmp definition: input is not iterated *)
definition spfCompH :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompH f1 f2 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"

abbreviation iter_spfCompH :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfCompH f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompH f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>))" 


text {* The general composition operator for TSPFs, 
        \textbf{NOTE:} does not always deliver an TSPF *}
definition spfComp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" (infixl "\<otimes>" 40) where
"spfComp f1 f2 \<equiv>
let I = spfCompI f1 f2;
    Oc = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> sbFix (spfCompH f1 f2 x) Oc)"

definition spfComp_well:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"spfComp_well f1 f2 \<equiv> spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"
(*
definition no_selfloops:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"no_selfloops f1 f2 \<equiv> spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1 = {}
                    \<and> spfDom\<cdot>f2 \<inter> spfRan\<cdot>f2 = {}"
*)
(* set of feedback channels *) (* TODO: rename *)

 (* LEGACY *)
definition pL :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"pL f1 f2 \<equiv> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f1)
                      \<union> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f2)"


(* This should be integrated in the spfcompOld definition *)
definition spfCompHelp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompHelp2 f1 f2 x \<equiv> (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                 \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"

definition spfcompOld :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF"  (infixl "\<otimes>" 40) where
"spfcompOld f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    O1 = spfRan\<cdot>f1; 
    O2 = spfRan\<cdot>f2; 
    I  = spfCompI f1 f2;
    Oc = spfCompOc f1 f2;
    C  = spfCompC f1 f2   
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. x \<uplus> (f1\<rightleftharpoons>(z \<bar> I1)) \<uplus> (f2\<rightleftharpoons>(z \<bar> I2)))\<cdot>(sbLeast C)) \<bar> Oc)"

(* SWS: rename to spfComp *) 
(* and by the way, the composition function itself should be cont, right? *) 
definition spfcompOldOld2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" where
"spfcompOldOld2 f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    I  = spfCompI f1 f2; (* SWS: Replace this directly with the definition ? *)
    C  = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)  (* SWS: Why name it C? O (or Out) would be a better name *)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> I1)) \<uplus> (f2\<rightleftharpoons>((x \<uplus> z) \<bar> I2)))\<cdot>(C^\<bottom>)))"



(*
(* Another spfComp definition ... Yaaayy :D *)
definition spfCompOld3 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" where
"spfCompOld3 f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    I  = spfCompI f1 f2; (* SWS: Replace this directly with the definition ? *)
    C  = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)   (* SWS: Why name it C? O (or Out) would be a better name *)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> sbFix (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> I1)) \<uplus> (f2\<rightleftharpoons>((x \<uplus> z) \<bar> I2))) C)"

*)

text {* "spflift" takes a "simple stream processing function" and two channel names where the streams flow, and lifts it to a stream bundle processing function.*}
definition spfLift :: "('m stream \<rightarrow> 'm stream) => channel => channel => 'm SPF" where
"spfLift f ch1 ch2  \<equiv> Abs_CSPF (\<lambda>b. ( (b\<in>{c1}^\<Omega>) \<leadsto> ([ch2 \<mapsto> f\<cdot>(b . ch1)]\<Omega>)))" 

(* takes a fully defined 'm SPF-function and changes it to an 'm SPF with given In & Out channels *)
definition spfSbLift:: "('m SB \<rightarrow> 'm SB) \<Rightarrow> channel set \<Rightarrow> channel set \<Rightarrow> 'm SPF" where
"spfSbLift f In Out \<equiv> Abs_CSPF (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto> (\<up>f\<cdot>b) \<bar> Out)"

definition hide :: "'m SPF \<Rightarrow>  channel set \<Rightarrow> 'm SPF" ("_\<h>_") where
"hide f cs \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"



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
  by (simp add: Rep_CSPF_def)

lemma rep_cspf_well[simp]: "spf_well (Abs_cfun (Rep_CSPF x))"
  by (metis Rep_CSPF_def Rep_SPF eta_cfun mem_Collect_eq)

lemma rep_cspf_cont2 [simp]: "cont (Rep_CSPF x)"
  by (simp add: Rep_CSPF_def)

lemma rep_abs_cspf[simp]: assumes "cont f" and "spf_well (Abs_cfun f)" 
  shows "Rep_CSPF (Abs_CSPF f) = f"
  by (simp add: Abs_CSPF_def Abs_SPF_inverse Rep_CSPF_def assms(1) assms(2))

lemma [simp]: "spf_well f \<Longrightarrow> Rep_SPF (Abs_SPF f) = f"
by (simp add: Abs_SPF_inverse)



  subsection \<open>Generel Lemmas about the 'm SPF_definition\<close>



(* Show that Map.empty is not an 'm SPF *)
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
  by (metis (no_types) Rep_CSPF_def assms rep_spf_well spf_well_def2)

(* only 'm SBs with the same domain are in an 'm SPF *)
lemma spf_dom2sbdom: assumes "x\<in>dom (Rep_CSPF f)" and "y\<in>dom (Rep_CSPF f)" 
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  by (metis Rep_CSPF_def assms rep_spf_well spf_well_def)

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
  by (metis Cfun.cfun.Rep_cfun_inverse Rep_CSPF_def sx_def domI option.sel rep_cspf_well spf_well_def2)
qed

(* An easy to use introduction rule for spf_well. *)
lemma spf_wellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (sbDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> sbDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (sbDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  shows "spf_well f"
  by (meson assms spf_well_def)

(* if 2 'm SPF's are in a below-relation their Input-Channels are equal *)
lemma spf_below_sbdom: assumes "a\<sqsubseteq>b" and "x \<in> dom (Rep_CSPF b)" and "y \<in> dom (Rep_CSPF a)"
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  by (metis Rep_CSPF_def assms(1) assms(2) assms(3) below_SPF_def below_cfun_def part_dom_eq spf_dom2sbdom)

(* if 2 'm SPF's are in a below-relation their Output-Channels are equal *)
lemma spf_below_ran: assumes "a\<sqsubseteq>b" and "x \<in> ran (Rep_CSPF b)" and "y \<in> ran (Rep_CSPF a)"
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
  proof -
  obtain sx where sx_def: "((Rep_CSPF b) sx) =  (Some x)" using assms ran2exists by fastforce
  obtain sy where sy_def: "((Rep_CSPF a) sy) =  (Some y)" using assms ran2exists by fastforce

  have "dom (Rep_CSPF a) = dom (Rep_CSPF b) " by (metis Rep_CSPF_def assms(1) below_SPF_def below_cfun_def part_dom_eq)
  thus ?thesis
  by (metis (no_types, lifting) Rep_CSPF_def assms(1) assms(3) below_SPF_def below_cfun_def domD domI fun_below_iff ranI sbdom_eq some_below2 spf_ran2sbdom sx_def)
qed





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
  shows "sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF (\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF (Y i))))"
  by (metis (mono_tags, lifting) Rep_CSPF_def Rep_SPF assms below_refl is_ub_thelub lub_chain_maxelem mem_Collect_eq po_eq_conv someI_ex spf_below_sbdom spf_dom_not_empty spf_well_def2)


(* spfDom is continuous *)
lemma spf_dom_cont [simp]:"cont (\<lambda>f. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF f)))"
  by(simp add: contI2)

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
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms domI someI_ex spfDom_def spf_dom2sbdom spf_dom_cont)

lemma spfLeastIDom: "(sbLeast (spfDom\<cdot>f)) \<in> dom (Rep_CSPF f)"
by (metis domD sbleast_sbdom spf_dom_not_empty spf_sbdom2dom spfdom2sbdom)

lemma spf_belowI: assumes "spfDom\<cdot>f = spfDom\<cdot>g"
          and "\<And>x. (sbDom\<cdot>x = spfDom\<cdot>f \<Longrightarrow> (Rep_CSPF f)\<rightharpoonup>x \<sqsubseteq> (Rep_CSPF g)\<rightharpoonup>x)"
       shows "f \<sqsubseteq> g"
proof -
  have "dom (Rep_CSPF f) = dom (Rep_CSPF g)"
    by (metis (no_types, lifting) Collect_cong Rep_CSPF_def assms(1) dom_def mem_Collect_eq rep_spf_well spfLeastIDom spf_well_def)
  thus ?thesis
    by (metis Rep_CSPF_def assms(2) below_SPF_def below_cfun_def domIff option.collapse part_below spfdom2sbdom) 
qed

lemma spfDomAbs: assumes "cont (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))" and "spf_well (\<Lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))"
    shows "spfDom\<cdot>(Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
apply(simp add: spfDom_def)
apply(simp_all add: assms)
proof -
  have "\<forall>p s pa. (\<not> p (s::'a SB) \<or> (\<exists>s. p s \<and> \<not> pa s)) \<or> pa (Eps p)"
    by (metis someI2)
  then have "(SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)"
    by (metis (no_types) assms(1) assms(2) rep_abs_cspf spf_dom_not_empty)
  then have "(sbDom\<cdot> (SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) = cs)\<leadsto>f (SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) \<noteq> None"
    by blast
  then show "sbDom\<cdot> (SOME s. s \<in> dom (\<lambda>s. (sbDom\<cdot>s = cs)\<leadsto>f s)) = cs"
    by meson
qed
    
  subsection \<open>spfRan\<close>

(* Shows that "spfRan" is "monofun". Used to show that spfRan is cont *)
lemma spf_ran_mono[simp]: "monofun (\<lambda> f.  sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF f)))"
  proof(rule monofunI)
  fix x y :: "'m SPF"
  assume "x\<sqsubseteq>y"
  thus "sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF x)) \<sqsubseteq> sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF y))"
  by (metis (no_types, lifting) po_eq_conv someI spf_below_ran spf_ran_not_empty)
qed

(* used to show that spfRan is cont *)
lemma spf_ran_contlub [simp]: assumes "chain Y"
  shows "sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF (\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF (Y i))))"
  by (metis (no_types, lifting) assms below_refl is_ub_thelub po_class.chain_def someI_ex spf_below_ran spf_ran_not_empty)

(* Shows that "spfRan" is "cont" *)
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
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms ranI someI_ex spfRan_def spf_ran2sbdom spf_ran_cont)

lemma spfran_least: "spfRan\<cdot>f = sbDom\<cdot>((Rep_CSPF f) \<rightharpoonup> (sbLeast (spfDom\<cdot>f)))"
apply(simp add: spfRan_def)
by (metis (no_types, lifting) domIff option.exhaust_sel ranI someI_ex spfLeastIDom spf_ran2sbdom)

lemma spfran2sbdom2: assumes "sbDom\<cdot>sb = spfDom\<cdot>f"
  and "spfDom\<cdot>f \<noteq> {}"
  shows "sbDom\<cdot>((Rep_CSPF f) \<rightharpoonup> sb) = spfRan\<cdot>f"
  apply(simp add: spfran_insert)
by (metis (no_types, lifting) assms(1) domIff option.collapse ran2exists spf_ran_not_empty spf_sbdom2dom spfdom2sbdom spfran2sbdom tfl_some)


  subsection \<open>spfType\<close>
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
  by (smt assms inf.orderE inf_commute option.sel option.simps(3) ran2exists sbrestrict_sbdom sbup_sbdom subset_UNIV)

lemma spfsblift_dom [simp]: "(\<exists> d. (d \<in> (dom (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(F\<cdot>b))\<bar>Out)))))"
  proof
  show "(sbLeast In) \<in> (dom (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(F\<cdot>b))\<bar>Out)))" by auto
qed

lemma spfsblift_ran [simp]: "(\<exists> d. (d \<in> (ran (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>((\<up>(F\<cdot>b))\<bar>Out)))))"
  oops


lemma spfsblift_sbran[simp]: "spfRan\<cdot>(spfSbLift F In Out) = Out"
  apply(simp add: spfSbLift_def spfRan_def)
  oops

lemma spfsbliftE[simp]: assumes "sbDom\<cdot>g = In"
  shows "(Rep_SPF (spfSbLift f In Out))\<cdot>g = Some ((\<up>f\<cdot>g) \<bar> Out)"
  oops
(* using Rep_CSPF_def assms rep_abs_cspf spfSbLift_def by auto *)



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
  then have "cont (\<lambda>s. sbUnion\<cdot> (b \<uplus> Rep_cfun (Rep_SPF f1)\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))) \<and> cont (\<lambda>s. Rep_SPF f2\<cdot>(s\<bar>spfDom\<cdot>f2))"
    by simp
  then have "cont (\<lambda>s. b \<uplus> (Rep_cfun (Rep_SPF f1)\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) \<uplus> (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s\<bar>spfDom\<cdot>f2))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis by(simp add: Rep_CSPF_def)
qed

lemma spfCompHelp_monofun2 [simp]: "monofun (\<lambda> b. \<Lambda> last. (b \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(last \<bar> spfDom\<cdot>f1))
                                   \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(last \<bar> spfDom\<cdot>f2))))"
  apply(rule monofunI)
  apply (simp add: below_cfun_def)
  by (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun)
    
lemma spfRanRestrict [simp]: assumes "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>b"
  shows "sbDom\<cdot>(Rep_CSPF f2\<rightharpoonup>(b\<bar>spfDom\<cdot>f2)) = spfRan\<cdot>f2"
proof -
  have "sbDom\<cdot>(b\<bar>spfDom\<cdot>f2) = spfDom\<cdot>f2" using assms by auto 
  hence "(b\<bar>spfDom\<cdot>f2) \<in> dom (Rep_CSPF f2)" by (metis domD spf_dom_not_empty spf_sbdom2dom spfdom2sbdom) 
  thus ?thesis by (metis domIff option.collapse spfran2sbdom) 
qed

lemma "chain Y \<Longrightarrow> (\<Squnion>i. g\<cdot>(Y i)) = (g\<cdot>(\<Squnion>i. Y i))"
  by (simp add: contlub_cfun_arg)
    

  subsubsection \<open>ChannelSets\<close>
(* ----------------------------------------------------------------------- *)    
 
text{* Input channels are a subset of all channels *}
lemma spfcomp_I_subset_C [simp]: "(spfCompI f1 f2) \<subseteq> (spfCompC f1 f2)"
  using spfCompI_def spfCompC_def by blast

text{* Internal channels are a subset of all channels *}
lemma spfcomp_L_subset_C [simp]: "(spfCompL f1 f2) \<subseteq> (spfCompC f1 f2)"
  using spfCompL_def spfCompC_def by blast
 
(* LEGACY
text{* pL channels are a subset of internal channels *}
lemma spfcomp_pl_subset_L [simp]: "(pL f1 f2) = (spfCompL f1 f2)"
  using pL_def spfCompL_def apply simp

text{* pL channels are a subset of all channels *}    
lemma spfcomp_pL_subset_C [simp]: "(pL f1 f2) \<subseteq> (spfCompC f1 f2)"
  using pL_def spfCompC_def by blast
*)

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
    
(* LEGACY *)
lemma spfI_sub_C[simp]: "spfCompI f1 f2 \<subseteq> spfCompC f1 f2"
  by simp

lemma spfOc_sub_C[simp]: "spfCompOc f1 f2 \<subseteq> spfCompC f1 f2"
  by simp



  subsubsection \<open>Serial_Composition\<close>
(* ----------------------------------------------------------------------- *)    

(* TODO: improve this, needed since sledgi does not work effective without this *)
lemma num3_eq[simp] : " 3 = (Suc(Suc(Suc 0)))"
  using numeral_3_eq_3 by blast


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
  apply(auto simp add: sbdom_rep_eq)
  apply(simp add: hidespfwell_helper)
  by auto  

lemma spfDomHide: "spfDom\<cdot>(f \<h> cs) = spfDom\<cdot>f"
  apply(simp add: hide_def)
    by(simp add: spfDomAbs hide_cont hide_spfwell)

lemma hideSbRestrict: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" 
   shows "(hide f cs)\<rightleftharpoons>sb = (f\<rightleftharpoons>sb)\<bar>(spfRan\<cdot>f - cs)"
  apply(simp add: hide_def)
  by (simp add: assms)

lemma hideSbRestrictCh: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" and "c \<notin> cs"
   shows "(hide f cs)\<rightleftharpoons>sb . c = (f\<rightleftharpoons>sb) . c"
  apply(simp add: hide_def)
  apply(simp add: assms)
  by (metis DiffI Int_lower1 assms(1) assms(2) hidespfwell_helper sbrestrict2sbgetch sbrestrict_sbdom sbunion_getchL sbunion_idL)
   
lemma hideSpfRan: "spfRan\<cdot>(hide f cs) = spfRan\<cdot>f - cs"
  apply(subst spfran_least)
  apply(simp add: spfDomHide)
  apply(subst hideSbRestrict)
  apply(simp)
  apply(subst sbrestrict_sbdom)
  by (simp add: Diff_subset Int_absorb1 spfran_least)

lemma hideSubset: "spfRan\<cdot>(hide f cs) \<subseteq> spfRan\<cdot>f"
  using hideSpfRan by auto  
  
  

subsection \<open>Alternative definition of 'm SPF\<close>





(* show that the original definition is equivalent with mine *)

(* Original definition used bevore *)
definition spf_mono :: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> bool" where
"spf_mono f \<equiv> \<forall>b1 b2. (b1 \<in> dom f \<and> b2 \<in> dom f \<and> b1 \<sqsubseteq> b2) \<longrightarrow> the (f b1) \<sqsubseteq> the (f b2)"

definition spf_contlub :: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> bool" where
"spf_contlub f \<equiv> \<forall>K. (chain K \<and> (K 0) \<in> dom f) \<longrightarrow> the (f (\<Squnion> i. K i)) \<sqsubseteq> (\<Squnion> i. the (f (K i)))"


lemma spf_monoI: assumes "\<And>b1 b2. b1 \<in> dom f \<Longrightarrow> b2 \<in> dom f \<Longrightarrow> b1 \<sqsubseteq> b2 \<Longrightarrow> (f\<rightharpoonup>b1) \<sqsubseteq> f\<rightharpoonup>b2"
  shows "spf_mono f"
using assms spf_mono_def by blast

lemma spf_contlubI: assumes " \<And>Y. chain Y \<Longrightarrow> (Y 0) \<in> dom f \<Longrightarrow>  (f \<rightharpoonup>(\<Squnion> i. Y i)) \<sqsubseteq> (\<Squnion> i. (f\<rightharpoonup>(Y i)))"
  shows "spf_contlub f"
by (meson assms spf_contlub_def sbChain_dom_eq2 sbdom_eq)

(* show that "spf_mono" implies "monofun". the second assumtions comes from spf_well *)
lemma spf_mono2monofun [simp]: assumes "spf_mono f" and "\<forall>b. b \<in> dom f \<longleftrightarrow> sbDom\<cdot>b = In"
  shows "monofun f"
  proof (rule monofunI)
    fix x y :: "'a SB"
    assume "x\<sqsubseteq>y"
    hence "sbDom\<cdot>x = sbDom\<cdot>y" using sbdom_eq by blast
    hence "x\<in> dom f \<longleftrightarrow> y\<in>dom f" by (simp add: assms(2))
    thus "f x \<sqsubseteq> f y "
    by (metis (no_types, lifting) \<open>x \<sqsubseteq> y\<close> assms(1) domD domIff option.sel po_eq_conv some_below spf_mono_def)
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
   hence "the (f (\<Squnion> i. Y i)) \<sqsubseteq> the (\<Squnion> i. (f (Y i)))" using \<open>chain (\<lambda>i. f (Y i))\<close> local.f1 op_the_lub by fastforce
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
   show "monofun f" using assms(2) assms(3) spf_mono2monofun by blast
  thus "\<forall>Y. chain Y \<longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))" using assms(1) assms(3) spf_contlub2contlub by blast
qed

end