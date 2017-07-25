(*  Title:        SPF
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Stream Processing Functions"
*)

theory SPF
imports SB

begin
  default_sort message 

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




(* Shorter version to get to normal functions from 'm SPF's *)
definition Rep_CSPF:: "'m SPF \<Rightarrow> ('m SB \<rightharpoonup> 'm SB)" where
"Rep_CSPF F \<equiv>  Rep_cfun (Rep_SPF F) "

(* Shorter version to get from normal functions to 'm SPF's *)
  (* of course the argument should be "spf_well" and "cont" *)
definition Abs_CSPF:: "('m SB \<rightharpoonup> 'm SB) \<Rightarrow> 'm SPF" where
"Abs_CSPF F \<equiv> Abs_SPF (Abs_cfun F)"


  (* get input channel set for given 'm SPF *)
definition spfDom :: "'m SPF \<rightarrow> channel set" where
"spfDom \<equiv> \<Lambda> f. sbDom\<cdot>(SOME b. b \<in> dom (Rep_CSPF f))" 

  (* get output channel set for given 'm SPF *)
definition spfRan :: "'m SPF \<rightarrow> channel set" where
"spfRan \<equiv> \<Lambda> f.  sbDom\<cdot>(SOME b. b \<in> ran (Rep_CSPF f))"

(*
  (* get "Internal" channels *)
definition spfInternal:: "'m SPF \<Rightarrow> channel set" where
"spfInternal f \<equiv> spfRan f \<inter> spfDom f"

definition spfIn :: "'m SPF \<Rightarrow> channel set" where
"spfIn f \<equiv> spfDom f - spfInternal f"

definition spfOut :: "'m SPF \<Rightarrow> channel set" where
"spfOut f \<equiv> spfRan f - spfInternal f "
*)


text {* spftype" returns the type of the stream processing function.*}
definition spfType :: "'m SPF \<rightarrow> (channel set \<times> channel set)" where
"spfType \<equiv> \<Lambda> f . (spfDom\<cdot>f, spfRan\<cdot>f)"

  (* All 'm SPF's with "In" as Input and "Out" as Output set *)
definition spfIO :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm SPF set" where
"spfIO In Out = {f. spfDom\<cdot>f = In \<and> spfRan\<cdot>f = Out}"


text \<open>Dummy patterns for abstraction\<close>
translations
  "\<LL> _ . t" => "CONST Abs_CSPF (\<lambda> _ . t)"

(*?*)

(* harpoon and Rep operation all in one for simpler SPF on SB applications *)
abbreviation theRep_abbrv :: "'a SPF \<Rightarrow> 'a SB \<Rightarrow> 'a SB " ("_\<rightleftharpoons>_") where
"(f \<rightleftharpoons> s) \<equiv> the ((Rep_CSPF f) s)"

(*
definition spfCompAll :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompAll f1 f2 = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"

definition spfCompInternal :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompInternal f1 f2 = ((spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f1))"

definition spfCompIn :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompIn f1 f2 = (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) - ((spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f1))"

definition spfCompOut :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"spfCompOut f1 f2 = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2) - ((spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f1))"

definition spfComp_well:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"spfComp_well f1 f2 \<equiv> spfDom\<cdot>f2 \<inter>spfRan\<cdot>f2 = {}
                \<and>  spfDom\<cdot>f1 \<inter>spfRan\<cdot>f1 = {} 
                \<and> spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"

(* (f1 \<otimes> f2) x = [fix\<cdot>(\<Lambda> z. x \<uplus> f1(z\<bar>I1) \<uplus> f2(z\<bar>I2))]\<bar>O  *)
definition spfComp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF"  (infixl "\<otimes>" 40) where
"spfComp2 f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfCompIn f1 f2) \<leadsto> 
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))
                   \<cdot>(sbLeast (spfCompAll f1 f2))) \<bar> spfCompOut f1 f2)"



definition spfCompHelp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompHelp f1 f2 x \<equiv> \<Lambda> last. x  \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(last \<bar> spfDom\<cdot>f1))
                                   \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(last \<bar> spfDom\<cdot>f2))"


(* Meine Version *)
(* assumes O1 \<inter> O2 = {}, otherwise arbitrary behaviour *)
(* Do i know that (I1 \<inter> O1) = {} ? ? ? *)
  (* because otherwise "(z \<bar> O1) = the (Rep_CSPF f1 (z \<bar> I1))" .... is strange/wrong/not useful  *)
definition spfComp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF"  (infixl "\<otimes>" 40) where
"spfComp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfCompIn f1 f2) \<leadsto> 
    (\<Squnion>i. iterate i\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))) \<bar> spfCompOut f1 f2)"

(* equality lemmas *)
lemma spfcompC_eq : "spfCompAll f1 f2 = C f1 f2"
by (simp add: Cc_def spfCompAll_def)

lemma spfcompI_eq : "(spfCompIn f1 f2) = I f1 f2"
oops (* lemma specification incorrect! *)

lemma spfcompL_eq : "(spfCompInternal f1 f2) = L f1 f2"
oops (* lemma specification incorrect! *)

lemma spfcompOc_eq : "(spfCompOut f1 f2) = Oc f1 f2"
oops (* lemma specification incorrect! *)

(* Orginale Version *)
text {* composition operator *}
definition spfcomp :: "'m SPF => 'm SPF => 'm SPF"  where
"spfcomp f1 f2 \<equiv> (*?*)
let I1  = spfDom\<cdot> f1;
    I2  = spfDom\<cdot> f2;
    O1  = spfRan\<cdot> f1; 
    O2  = spfRan\<cdot> f2; 
    L   =(spfDom\<cdot> f2 \<inter> spfRan\<cdot> f1) \<union> (spfDom\<cdot> f1 \<inter> spfRan\<cdot> f2);
    In  =(spfDom\<cdot> f1 \<union> spfDom\<cdot> f2) - L;
    Out =(spfRan\<cdot> f1 \<union> spfRan\<cdot> f2) - L    
in (Abs_CSPF (\<lambda> b . ((sbDom\<cdot>b = In) \<leadsto>  (THE y . y\<in>{ z \<bar> Out   | z .  
      (z \<bar> In) = b
    \<and> (z \<bar> O1) = the (Rep_CSPF f1 (z \<bar> I1))
    \<and> (z \<bar> O2) = the (Rep_CSPF f2 (z \<bar> I2))}))))"
*)

(* redefined composition channel sets *)
definition I :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"I f1 f2 \<equiv> (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

definition Oc :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"Oc f1 f2 \<equiv> (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"   (* old: (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2) - (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)"*)

definition L :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"L f1 f2 \<equiv> (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<inter> (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"

definition C :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"C f1 f2 \<equiv> spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"

definition spfComp_well:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"spfComp_well f1 f2 \<equiv> spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"

definition no_selfloops:: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"no_selfloops f1 f2 \<equiv> spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1 = {}
                    \<and> spfDom\<cdot>f2 \<inter> spfRan\<cdot>f2 = {}"

(* This should be integrated in the spfcomp definition *)
definition spfCompHelp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompHelp2 f1 f2 x \<equiv> (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                 \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"

definition spfcomp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF"  (infixl "\<otimes>" 40) where
"spfcomp f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    O1 = spfRan\<cdot>f1; 
    O2 = spfRan\<cdot>f2; 
    I  = I f1 f2;
    Oc = Oc f1 f2;
    C  = C f1 f2   
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. x \<uplus> (f1\<rightleftharpoons>(z \<bar> I1)) \<uplus> (f2\<rightleftharpoons>(z \<bar> I2)))\<cdot>(sbLeast C)) \<bar> Oc)"

(* SWS: rename to spfComp *) 
(* and by the way, the composition function itself should be cont, right? *) 
definition spfcomp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" where
"spfcomp2 f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    I  = I f1 f2; (* SWS: Replace this directly with the definition ? *)
    C  = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)  (* SWS: Why name it C? O (or Out) would be a better name *)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> I1)) \<uplus> (f2\<rightleftharpoons>((x \<uplus> z) \<bar> I2)))\<cdot>(C^\<bottom>)))"


(* this function is not cont, because for 'strange' functions it is not cont *)
(* strange = the domain changes from input to output *)
definition sbFix :: "('m SB \<rightarrow> 'm SB) \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix F cs \<equiv>  (\<Squnion>i. iterate i\<cdot>F\<cdot>(cs^\<bottom>))"

(* Another spfComp definition ... Yaaayy :D *)
definition spfComp3 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" where
"spfComp3 f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    I  = I f1 f2; (* SWS: Replace this directly with the definition ? *)
    C  = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)   (* SWS: Why name it C? O (or Out) would be a better name *)
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> sbFix (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> I1)) \<uplus> (f2\<rightleftharpoons>((x \<uplus> z) \<bar> I2))) C)"


(*(* (f1 \<otimes> f2) x = [fix\<cdot>(\<Lambda> z. x \<uplus> f1(z\<bar>I1) \<uplus> f2(z\<bar>I2))]\<bar>O  *)
definition spfComp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF"  (infixl "\<otimes>" 40) where
"spfComp2 f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
    ((\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2))))
                   \<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"


definition spfcomp :: "'m SPF => 'm SPF => 'm SPF"  where
"spfcomp f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    O1 = spfRan\<cdot>f1; 
    O2 = spfRan\<cdot>f2; 
    I  = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2);
    Oc = spfRan\<cdot>f1 \<union> spfRan\<cdot>f2 - (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2);
    C  = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2    
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> I1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> I2)))\<cdot>(sbLeast C)) \<bar> Oc)"
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
  apply (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun)
  done
    
lemma spfRanRestrict [simp]: assumes "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>b"
  shows "sbDom\<cdot>(Rep_CSPF f2\<rightharpoonup>(b\<bar>spfDom\<cdot>f2)) = spfRan\<cdot>f2"
proof -
  have "sbDom\<cdot>(b\<bar>spfDom\<cdot>f2) = spfDom\<cdot>f2" using assms by auto 
  hence "(b\<bar>spfDom\<cdot>f2) \<in> dom (Rep_CSPF f2)" by (metis domD spf_dom_not_empty spf_sbdom2dom spfdom2sbdom) 
  thus ?thesis by (metis domIff option.collapse spfran2sbdom) 
qed

lemma "chain Y \<Longrightarrow> (\<Squnion>i. g\<cdot>(Y i)) = (g\<cdot>(\<Squnion>i. Y i))"
  by (simp add: contlub_cfun_arg)
    
(*
lemma spfCompHelp_cont2 [simp]: "cont (\<lambda> b. \<Lambda> last. (b \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(last \<bar> spfDom\<cdot>f1))
                                   \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(last \<bar> spfDom\<cdot>f2))))"
apply(rule contI2)
apply simp
apply auto
apply(simp add: below_cfun_def)
oops
*)


  subsubsection \<open>ChannelSets\<close>
(* ----------------------------------------------------------------------- *)    
  
lemma spfI_sub_C[simp]: "I f1 f2 \<subseteq> C f1 f2"
  using I_def C_def by fastforce

lemma spfOc_sub_C[simp]: "Oc f1 f2 \<subseteq> C f1 f2"
  using Oc_def C_def by fastforce  

lemma Oc_commu: "Oc f1 f2 = Oc f2 f1"
  by (simp add: Oc_def Un_commute)
    
lemma I_commu: "I f1 f2 = I f2 f1"
  by (simp add: I_def Un_commute)
    
lemma C_commu: "C f1 f2 = C f2 f1"
  using C_def by blast


  subsubsection \<open>Serial_Composition\<close>
(* ----------------------------------------------------------------------- *)    

(* TODO: improve this, needed since sledgi does not work effective without this *)
lemma num3_eq[simp] : " 3 = (Suc(Suc(Suc 0)))"
  using numeral_3_eq_3 by blast

(* set of feedback channels *) (* TODO: rename *)
definition pL :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"pL f1 f2 \<equiv> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1) \<union> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f2)"

lemma spfpl_sub_L[simp]: "pL f1 f2 \<subseteq> L f1 f2"
  by (simp add: L_def pL_def subset_iff)


(* lub equalities *)
lemma sbIterate_chain: "sbDom\<cdot>(f\<cdot>(sbLeast cs)) = cs \<Longrightarrow>chain (\<lambda>i. iterate i\<cdot>f\<cdot>(sbLeast cs))"
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by simp

   

(*    
lemma spfcomp_spfcompwithhelper: assumes "sbDom\<cdot>sb = I f1 f2"
shows "Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> (f1\<rightleftharpoons>(z\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(z\<bar>spfDom\<cdot>f2)))\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2) \<rightleftharpoons>sb = (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> (f1\<rightleftharpoons>(z\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(z\<bar>spfDom\<cdot>f2)))\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2"
 oops (* valid as long as spfcomp is cont *)
    *)
     

  
    

(*
thm spfCompHelp_def
lemma tsconc_assoc: "sb1 \<uplus> (sb2 \<uplus> sb3) = (sb1 \<uplus> sb2) \<uplus> sb3"
by(simp add: sbunion_insert)

lemma spfCompHelp_commutative: assumes "spfComp_well f1 f2" and "sbDom\<cdot>b = spfCompAll f1 f2"
  shows "spfCompHelp f1 f2 x\<cdot>b = spfCompHelp f2 f1 x\<cdot>b"
proof -
  have "spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}" using assms spfComp_well_def by blast
  hence "sbDom\<cdot>((Rep_CSPF f1)\<rightharpoonup>(b\<bar>spfDom\<cdot>f1)) \<inter> sbDom\<cdot>(Rep_CSPF f2\<rightharpoonup>(b\<bar>spfDom\<cdot>f2)) = {}"
    by (metis Un_subset_iff assms(2) spfCompAll_def spfRanRestrict sup_ge1)
  hence "((Rep_CSPF f1)\<rightharpoonup>(b\<bar>spfDom\<cdot>f1)) \<uplus> (Rep_CSPF f2\<rightharpoonup>(b\<bar>spfDom\<cdot>f2)) 
    = ((Rep_CSPF f2)\<rightharpoonup>(b\<bar>spfDom\<cdot>f2)) \<uplus> (Rep_CSPF f1\<rightharpoonup>(b\<bar>spfDom\<cdot>f1))"
    using sbunion_commutative by blast
  thus ?thesis 
    by (metis (no_types, lifting) Abs_cfun_inverse2 spfCompHelp_cont spfCompHelp_def tsconc_assoc)
qed

lemma spfCompHelper_in: assumes "c\<notin>spfRan\<cdot>f1" and "c\<notin>spfRan\<cdot>f2" and "sbDom\<cdot>b = spfCompAll f1 f2"
  shows "(spfCompHelp f1 f2 x)\<cdot>b . c = x . c"
apply(simp add: spfCompHelp_def)
apply (subst sbunion_getchL)
apply (simp add: assms(2) assms(3) spfCompAll_def subsetI)
apply (subst sbunion_getchL)
apply (simp add: assms(1) assms(3) spfCompAll_def subsetI)
apply simp
done

lemma spfCompH_dom [simp]: assumes "sbDom\<cdot>b = spfCompAll f1 f2"
  shows "sbDom\<cdot>(spfCompHelp f1 f2 x\<cdot>b) = sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"
apply(simp add: spfCompHelp_def)
by (metis Un_assoc assms le_supI1 spfCompAll_def spfRanRestrict sup.cobounded2 sup.left_idem)


lemma spfCompHelper_in1: assumes "sbDom\<cdot>b = spfCompAll f1 f2" and "spfComp_well f1 f2" and "sbDom\<cdot>x = spfCompIn f1 f2"
  shows "(spfCompHelp f1 f2 x)\<cdot>b \<bar> spfCompIn f1 f2 = x \<bar> spfCompIn f1 f2 "
  apply(rule sb_eq)
   apply (simp add: assms(1) spfCompIn_def assms)
   apply blast
  apply auto
  by (metis DiffD1 DiffD2 Int_iff Un_iff assms(1) assms(2) spfCompHelper_in spfCompIn_def spfComp_well_def)


lemma spfInSubAll[simp]: "spfCompIn f1 f2 \<subseteq> spfCompAll f1 f2"
using spfCompAll_def spfCompIn_def by fastforce


lemma spfCompHelper_dom[simp]: assumes "sbDom\<cdot>x = spfCompIn f1 f2"
  shows "sbDom\<cdot>(iterate i\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))) = spfCompAll f1 f2"
  apply(induction i)
   apply (simp add: assms sup_absorb1)
  apply simp
  apply(simp add: assms spfCompIn_def spfCompAll_def)
  apply blast
done


lemma spfCompInt: assumes "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          and "c\<in>spfCompIn f1 f2"
  shows "(iterate (Suc i)\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))) . c = x . c" 
  apply(unfold iterate_Suc, subst spfCompHelp_def)
  apply simp
  apply (subst sbunion_getchL)
   apply (metis DiffD1 DiffD2 Int_iff Un_commute Un_iff assms(1) assms(2) assms(3) inf_sup_ord(3) le_supI1 spfCompAll_def spfCompHelper_dom spfCompIn_def spfComp_well_def spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis DiffD1 DiffD2 Int_iff Un_commute Un_iff assms(1) assms(2) assms(3) inf_sup_ord(3) le_supI1 spfCompAll_def spfCompHelper_dom spfCompIn_def spfComp_well_def spfRanRestrict)
  by simp

lemma spfCompInt_res: assumes "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
  shows "(iterate (Suc i)\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))) \<bar> spfCompIn f1 f2 = x" 
  apply(rule sb_eq)
   apply (simp add: assms Int_absorb1 spfCompIn_def)
   apply blast
  apply (simp)
  apply(subst spfCompHelp_def)
  apply simp
  apply (subst sbunion_getchL)
   apply (metis DiffD1 DiffD2 Int_iff Un_commute Un_iff assms(1) assms(2) inf_sup_ord(3) le_supI1 spfCompAll_def spfCompHelper_dom spfCompIn_def spfComp_well_def spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis DiffD1 DiffD2 Int_iff Un_commute Un_iff assms(1) assms(2)  inf_sup_ord(3) le_supI1 spfCompAll_def spfCompHelper_dom spfCompIn_def spfComp_well_def spfRanRestrict)
  by (simp)

lemma spfComp_parallel1: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot> x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          and "c\<in>spfRan\<cdot>f2"
        shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))) . c 
                      = (Rep_CSPF f2) \<rightharpoonup> (x \<bar>spfDom\<cdot>f2) . c"
  apply(subst iterate_Suc)
  apply(subst spfCompHelp_def)
  apply simp
  apply (subst sbunion_getchR)
   apply (metis Diff_empty Un_subset_iff assms(1) assms(2) assms(4) iterate_Suc spfCompHelper_dom spfCompIn_def spfCompInternal_def spfInSubAll spfRanRestrict)
  by (smt Diff_empty Int_absorb1 Un_subset_iff assms(1) assms(2) assms(3) iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom spfCompHelper_dom spfCompIn_def spfCompInt_res spfCompInternal_def spfInSubAll subsetCE sup.cobounded2)

lemma spfComp_parallel2: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          and "c\<in>spfRan\<cdot>f1"
        shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))) . c 
                      = (Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1) . c"
  apply(subst iterate_Suc)
  apply(subst spfCompHelp_def)
  apply simp
  apply (subst sbunion_getchL)
   apply (metis Diff_empty Un_subset_iff assms(1) assms(2) assms(3) assms(4) disjoint_iff_not_equal iterate_Suc spfCompHelper_dom spfCompIn_def spfCompInternal_def spfComp_well_def spfInSubAll spfRanRestrict)
  apply (subst sbunion_getchR)
   apply (metis Diff_empty Un_subset_iff assms(1) assms(2) assms(4) iterate_Suc spfCompHelper_dom spfCompIn_def spfCompInternal_def spfInSubAll spfRanRestrict)
  by (smt Diff_empty Int_absorb1 Un_subset_iff assms(1) assms(2) assms(3) inf_sup_ord(3) iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom spfCompHelper_dom spfCompIn_def spfCompInt_res spfCompInternal_def spfInSubAll subsetCE)


lemma spfComp_parallel: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
        shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2)))
                      = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> (Rep_CSPF f2) \<rightharpoonup> (x \<bar>spfDom\<cdot>f2)" (is "?L = ?R")
proof(rule sb_eq)
  have r_dom: "sbDom\<cdot>?R = spfCompAll f1 f2"
    by (metis Diff_empty Un_upper1 assms(1) assms(2) sbunionDom spfCompAll_def spfCompIn_def spfCompInternal_def spfRanRestrict sup_ge2) 
  have l_dom: "sbDom\<cdot>?L = spfCompAll f1 f2" by (simp only: spfCompHelper_dom assms)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" using l_dom r_dom by blast

  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence c_def: "c\<in>spfCompAll f1 f2" using l_dom by blast
  thus "?L . c = ?R . c"
    by (metis Diff_empty UnE assms(1) assms(2) assms(3) sbunion_getchL sbunion_getchR spfCompAll_def spfCompIn_def spfCompInt spfCompInternal_def spfComp_parallel1 spfComp_parallel2 spfRanRestrict sup_ge1 sup_ge2)
qed

thm spfComp_def


(* legacy Comp and Comp2 equality *)
lemma comp12_eq: "spfComp f1 f2 = spfComp2 f1 f2"
apply (simp add: spfComp_def spfComp2_def)
by (metis (no_types) spfCompHelp_def)
*)





(*
(* the function returned by "spfcompMy" is monotonic. used in cont-proof *)
(* STUPID *)
lemma "monofun (spfcompMyHelper S1 S2)"
  proof -
  obtain I1 where i1: "I1 = spfDom\<cdot>S1" by simp
  obtain I2 where i2: "I2 = spfDom\<cdot>S2" by simp
  obtain O1 where o1: "O1 = spfRan\<cdot>S1" by simp
  obtain O2 where o2: "O2 = spfRan\<cdot>S2" by simp

  obtain L  where l: "L  = (I1 \<inter> O2) \<union> (I2 \<inter> O1)" by simp  (* Internal Channels *)
  obtain In where in_def: "In = (I1 \<union> I2) - L" by simp (* Input channels of the composed component *)
  obtain Out where out: " Out = (O1 \<union> O2) - L" by simp  (* Output channels of the composed component *)
  have "monofun (\<lambda>b. (THE y. \<exists>z. z\<bar> Out = y \<and>
                    z\<bar>In = b \<and> z\<bar>O1 = the (Rep_CSPF S1 (z\<bar>I1)) \<and> z\<bar>O2 = the (Rep_CSPF S2 (z\<bar>I2))))" sorry
  hence "monofun ((\<lambda> b . ((sbDom\<cdot>b = In) \<leadsto> (THE y.(
  \<exists>z. (z \<bar> Out) = y  
    \<and> (z \<bar> In) = b
    \<and> (z \<bar> O1) = the (Rep_CSPF S1 (z \<bar> I1))
    \<and> (z \<bar> O2) = the (Rep_CSPF S2 (z \<bar> I2)))))))" using if_then_mono out by blast
  hence "monofun (
  let I1 = spfDom\<cdot>S1; 
      I2 = spfDom\<cdot>S2; 
      O1 = spfRan\<cdot>S1; 
      O2 = spfRan\<cdot>S2; 
      L = I1 \<inter> O2 \<union> I2 \<inter> O1; 
      In = I1 \<union> I2 - L;
      Out = O1 \<union> O2 - L
    in (\<lambda>b. ((sbDom\<cdot>b =In) \<leadsto> 
    THE y. \<exists>z. z\<bar>Out = y \<and> z\<bar>In = b \<and> z\<bar>O1 = the (Rep_CSPF S1 (z\<bar>I1)) \<and> z\<bar>O2 = the (Rep_CSPF S2 (z\<bar>I2)))))"
  proof -
  have "monofun (\<lambda>s. (sbDom\<cdot>s = In)\<leadsto>THE sa. \<exists>sb. sb\<bar>Out = sa \<and> sb\<bar>In = s \<and> sb\<bar>O1 = the (Rep_CSPF S1 (sb\<bar>I1)) \<and> sb\<bar>O2 = the (Rep_CSPF S2 (sb\<bar>I2)))"
  using \<open>monofun (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>THE y. \<exists>z. z\<bar>Out = y \<and> z\<bar>In = b \<and> z\<bar>O1 = the (Rep_CSPF S1 (z\<bar>I1)) \<and> z\<bar>O2 = the (Rep_CSPF S2 (z\<bar>I2)))\<close> by blast
  then show ?thesis
  by (metis (no_types) i1 i2 in_def l o1 o2 out)
qed

  thus ?thesis using spfcompMyHelper_def sorry 
qed


lemma spfcomp_cont[simp]:"cont (spfcompMyHelper S1 S2)"
  sorry

lemma spfcomp_well [simp]: "spf_well (Abs_cfun (spfcompMyHelper S1 S2))"
  sorry

lemma spfcomp_spfdom [simp]: "spfDom\<cdot>(Abs_CSPF (spfcompMyHelper S1 S2)) = 
  (spfDom\<cdot>S1\<inter>spfRan\<cdot>S2)\<union>(spfDom\<cdot>S2\<inter>spfRan\<cdot>S1)" (*checken ob die menge stimmt *)
  oops

*)

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



(*
thm spfComp_parallel

lemma spfComp_parallel_max: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          shows "max_in_chain 2 (\<lambda>i. iterate i\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2)))"
apply(rule max_in_chainI)
apply(simp only: numerals(2))
apply(subst spfComp_parallel, simp_all add: assms)
by (metis Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) less_Suc_eq_le spfComp_parallel)
*)



(*
lemma spfComp_parallel_chain: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          shows "chain (\<lambda>i. iterate i\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2)))"
apply(rule sbIterate_chain)
apply (simp add: assms spfCompAll_def spfCompIn_def)
by blast


lemma spfComp_parallel3 [simp]: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2)))
            = iterate 2\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2))"
using assms(1) assms(2) assms(3) maxinch_is_thelub spfComp_parallel_chain spfComp_parallel_max by blast

lemma spfComp_parallel4 [simp]: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>x = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
          shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp f1 f2 x)\<cdot>(sbLeast (spfCompAll f1 f2)))
              = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> (Rep_CSPF f2) \<rightharpoonup> (x \<bar>spfDom\<cdot>f2) "
apply(simp add: assms)
by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) spfComp_parallel)

lemma spfApply_below: "b1 \<sqsubseteq> b2  \<Longrightarrow> sbDom\<cdot>b1 = spfDom\<cdot>f1 \<Longrightarrow> (Rep_CSPF f1)\<rightharpoonup>b1 \<sqsubseteq>  (Rep_CSPF f1)\<rightharpoonup>b2"
by (metis Rep_CSPF_def below_option_def below_refl monofun_cfun_arg)


lemma spfComp_parallelCont: assumes "spfCompInternal f1 f2 = {}"
          and "spfComp_well f1 f2"
          shows "cont (\<lambda> b. (sbDom\<cdot>b = spfCompIn f1 f2) 
          \<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp f1 f2 b)\<cdot>(sbLeast (spfCompAll f1 f2))) \<bar> spfCompOut f1 f2)"
oops
(*
apply(rule spf_mono2monofun)
apply(simp add: spf_mono_def assms domIff2)
apply rule+
apply auto[1]
apply(rule monofun_cfun_arg)
apply(simp only: numerals(2) assms spfComp_parallel)

apply auto
apply(rule +)
*)



lemma spfComp_parallel1: assumes "spfCompInternal f1 f2 = {}"
          and "sbDom\<cdot>b = spfCompIn f1 f2"
          and "spfComp_well f1 f2"
        shows "Rep_CSPF(f1 \<otimes> f2)\<rightharpoonup>b = ((Rep_CSPF f1) \<rightharpoonup> (b \<bar>spfDom\<cdot>f1)) \<uplus> (Rep_CSPF f2) \<rightharpoonup> (b \<bar>spfDom\<cdot>f2) "
apply(simp add: spfComp_def Rep_CSPF_def Abs_CSPF_def)
oops

*)


end