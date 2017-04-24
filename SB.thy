(*  Title:        SBTheorie
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Stream Bundles" 
*)

theory SB
imports Channel OptionCpo Streams

begin
default_sort message


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)


  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition sb_well :: "(channel \<rightharpoonup> 'm stream) => bool" where
"sb_well f \<equiv> \<forall>c \<in> dom f. sdom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c"

  (* sb_well is admissible, used to define 'm SB with cpodef *)
lemma sb_well_adm[simp]: "adm sb_well"
by (simp add: adm_def sb_well_def part_dom_lub lub_fun the_subset_cont)

lemma sb_well_exists[simp]: "sb_well empty"
by (simp add: sb_well_def)


  (* Definition: Stream Bundle. *)
cpodef 'm :: message SB = "{b :: channel \<rightharpoonup> 'm stream . sb_well b}"
  using sb_well_exists apply blast
 by auto

setup_lifting type_definition_SB





(* ----------------------------------------------------------------------- *)
  section \<open>Function Definition\<close>
(* ----------------------------------------------------------------------- *)


(* Syntactic sugar for Abs_SB *)
abbreviation Abs_abbr :: "(channel \<rightharpoonup> 'm stream) \<Rightarrow> 'm SB" ("_\<Omega>" [65] 65) where 
"f \<Omega> \<equiv> Abs_SB f"


text \<open>@{text "sbDom"} returns the domain of the stream bundle \<close>
definition sbDom :: "'m SB \<rightarrow> channel set" where
"sbDom \<equiv> \<Lambda> b. dom (Rep_SB b)"



text {* @{text "sbGetCh"} returns the stream flowing on a channel of a stream bundle *}
definition sbGetCh :: "'m SB \<rightarrow> channel \<rightarrow> 'm stream"  where
"sbGetCh \<equiv> \<Lambda> b c. ((Rep_SB b) \<rightharpoonup> c)"

abbreviation sbGetch_abbr :: "'m SB \<Rightarrow> channel \<Rightarrow> 'm stream" (infix "." 65) where 
"b . c \<equiv> sbGetCh\<cdot>b\<cdot>c"


text {* For a given channel set, "sbLeast" is the smallest stream bundle with empty streams. *}
definition sbLeast :: "channel set \<Rightarrow> 'm SB" ("_^\<bottom>" [1000] 999) where
"sbLeast cs \<equiv> (\<lambda>c. (c \<in> cs) \<leadsto> \<epsilon> )\<Omega>"


text {* @{text "sbunion"} the channel-domains are merged *}
(* the second argument has priority *)
definition sbUnion:: " 'm SB \<rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbUnion \<equiv> \<Lambda> b1 b2.  (Rep_SB b1 ++ Rep_SB b2)\<Omega>"

abbreviation sbUnion_abbr :: " 'm SB \<Rightarrow> 'm SB \<Rightarrow> 'm SB" (infixl "\<uplus>" 100) where 
"b1 \<uplus> b2 \<equiv> sbUnion\<cdot>b1\<cdot>b2"


text {* @{text "sbsetch"} adds a channel or replaces its content *}
definition sbSetCh:: " 'm SB \<rightarrow> channel \<Rightarrow> 'm stream \<Rightarrow> 'm SB" where
"sbSetCh \<equiv> \<Lambda> b. (\<lambda> c s. b \<uplus> ([c \<mapsto> s]\<Omega>))"




 (* Channels not in the channel set are set to "None". *)
definition sbRestrict:: "channel set \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbRestrict cs  \<equiv> \<Lambda> b. (Rep_SB b |` cs)\<Omega>"

abbreviation sbRestrict_abbr :: " 'm SB \<Rightarrow> channel set \<Rightarrow> 'm SB" ("(_\<bar>_)" [66,65] 65)
where "b\<bar>cs \<equiv> sbRestrict cs\<cdot>b"


text {* @{text "sbRemCh"} removes a channel from a stream bundle *}
definition sbRemCh:: " 'm SB \<rightarrow> channel \<rightarrow> 'm SB" where
"sbRemCh \<equiv> \<Lambda> b c.  b \<bar> -{c}" 


text {* @{text "sbrenamech"} renaming channels  *}
(* stream is moved from "ch1" to "ch2" *)
definition sbRenameCh :: " 'm SB => channel => channel => 'm SB" where
"sbRenameCh b ch1 ch2 \<equiv> (sbSetCh\<cdot>(sbRemCh\<cdot>b\<cdot>ch1)) ch2 (b .ch1)"



  (* Replaces all "None" channels with \<epsilon>. *)
definition sbUp:: " 'm SB \<rightarrow> 'm SB"  where
"sbUp \<equiv> \<Lambda> b . (\<lambda>c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b) c else Some \<epsilon>)\<Omega>"

abbreviation sbUp_abbr:: " 'm SB \<Rightarrow> 'm SB"  ("\<up>_" 70) where
"\<up>b \<equiv> sbUp\<cdot>b"


text {* @{text "sbeqch"} equality on specific channels *}
definition sbEqSelected:: " channel set \<Rightarrow> 'm SB => 'm SB => bool" where
"sbEqSelected cs b1 b2 \<equiv>  (b1\<bar>cs) = (b2\<bar>cs)"

text {* @{text "sbeq"} equality on common channels *}
definition sbEqCommon:: " 'm SB => 'm SB => bool" where
"sbEqCommon b1 b2\<equiv> sbEqSelected (sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2) b1 b2"


(*The function 'm SB creates the set of all bundles b with a fixed set of channels C.*)
definition SB :: "channel set \<Rightarrow> 'm SB set" ("_^\<Omega>" [1000] 999) where
"SB cs = {b. sbDom\<cdot>b = cs}"



  (* Prefix relation, but only on selected channels. *)
definition sbPrefixSelected:: "channel set \<Rightarrow> 'm SB \<Rightarrow> 'm SB \<Rightarrow> bool" where
"sbPrefixSelected cs b1 b2 \<equiv> (b1\<bar>cs \<sqsubseteq> b2\<bar>cs)" 

  (* Prefix relation, but only on common channels. *)
definition sbPrefixCommon:: " 'm SB \<Rightarrow> 'm SB \<Rightarrow> bool" where
"sbPrefixCommon b1 b2 \<equiv> sbPrefixSelected (sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2) b1 b2" 



  (* Concatination on all Channels in the 'm SB. "None" is interpreted as \<epsilon>. *)
definition sbConc:: " 'm SB \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbConc b1 \<equiv> \<Lambda> b2. ((\<lambda>c. Some ((\<up>b1. c) \<bullet> \<up>b2. c))\<Omega>) \<bar> sbDom\<cdot>b1 \<union> sbDom\<cdot>b2"

abbreviation sbConc_abbr :: " 'm SB \<Rightarrow> 'm SB \<Rightarrow> 'm SB" ("(_ \<bullet> _)" [66,65] 65)
where "b1 \<bullet> b2 \<equiv> sbConc b1\<cdot>b2"


  (* Concatination on common Channels in the 'm SB. *)
definition sbConcCommon:: " 'm SB \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbConcCommon b1 \<equiv> \<Lambda> b2. (b1 \<bullet> b2) \<bar>  sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2"




  (* Applies a (Stream-)function to all streams. *)
definition sbMapStream:: "('m stream \<Rightarrow> 'm stream) \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbMapStream f b =  (\<lambda>c. (c\<in>sbDom\<cdot>b) \<leadsto> f (b .c))\<Omega>"


  (* Retrieves the first n Elements of each Stream. *)
definition sbTake:: "nat \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbTake n \<equiv> \<Lambda> b . sbMapStream (\<lambda>s. stake n\<cdot>s) b"


  (* Retrieves the first Element of each Stream. *)
definition sbHd:: " 'm SB \<rightarrow> 'm SB" where
"sbHd \<equiv> sbTake 1"


  (* Deletes the first n Elements of each Stream *)
definition sbDrop:: "nat \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbDrop n \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. sdrop n\<cdot>s) b"


  (* Deletes the first Elements of each stream *)
definition sbRt:: " 'm SB \<rightarrow> 'm SB" where
"sbRt \<equiv> sbDrop 1"


  (* Retrieves the n-th element of each Stream *)
definition sbNth:: "nat \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbNth n \<equiv> \<Lambda> sb.  sbHd\<cdot>(sbDrop n\<cdot>sb)"


(* I tried to make this function cont, look at SBCase_Study *)
  (* Length of the selected stream. *)
definition sbLen:: " 'm SB \<Rightarrow> lnat " (* ("#_") *)where
"sbLen b \<equiv> LEAST ln. ln\<in> {#(b. c) | c. c\<in>sbDom\<cdot>b}"  

  (* Iterates the streams n-times. *)
definition sbNTimes:: "nat \<Rightarrow> 'm SB \<Rightarrow> 'm SB" ("_\<star>_" [60,80] 90) where
"sbNTimes n b \<equiv> sbMapStream (sntimes n) b"


  (* Iterates the streams \<infinity>-times. *)
definition sbInfTimes:: " 'm SB \<Rightarrow> 'm SB" ("_\<infinity>") where
"sbInfTimes sb = sbMapStream sinftimes sb"



  (* Applies a (Element-)function to each stream. *)
definition sbMap:: "('m \<Rightarrow> 'm) \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbMap f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. smap f\<cdot>s) b"


  (* Applies a filter to all Elements in each stream. *)
definition sbFilter:: "'m set \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbFilter f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. sfilter f\<cdot>s) b "

abbreviation sbfilter_abbr :: "'m set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" ("(_ \<ominus> _)" [66,65] 65)
where "F \<ominus> s \<equiv> sbFilter F\<cdot>s"


  (* Applies a filter to each stream. If the stream is not in the filter it is replaces by "None"  *)
definition sbFilterStreams:: "'m stream set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbFilterStreams f b \<equiv> (\<lambda>c. (c\<in>sbDom\<cdot>b \<and> (b. c)\<in>f) \<leadsto> (b .c) )\<Omega> "


  (* Applies the function to the first Element in each Streams and returns only the first Element *)
definition sbLookahd:: "('m \<Rightarrow> 'm) \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbLookahd f \<equiv> \<Lambda> sb. sbMap f\<cdot>(sbHd\<cdot>sb)"


  (* Prefix while predicate holds. *)
definition sbTakeWhile:: "('m \<Rightarrow> bool) \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbTakeWhile f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. stakewhile f\<cdot>s) b"


  (* Drop prefix while predicate holds. *)
definition sbDropWhile:: "('m \<Rightarrow> bool) \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbDropWhile f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. sdropwhile f\<cdot>s) b"


  (* Remove successive duplicate values from each stream. *)
definition sbRcdups:: " 'm SB \<rightarrow> 'm SB" where
"sbRcdups \<equiv> \<Lambda> sb. sbMapStream (\<lambda>s. srcdups\<cdot>s) sb"



(* Ugly AF, schöner machen\<And>! *)
(* Ich kann nicht "fix" verwendne da 'm SB kein pcpo ist. 
  Statdessen verwende ich "(sbTake 0\<cdot>b)" als künstliches kleinstes element *)

primrec myiterate :: "nat \<Rightarrow> 'm SB set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
    "myiterate 0 bs b = sbLeast (sbDom\<cdot>b)"
  | "myiterate (Suc n) bs b = (let rest = (myiterate n bs (sbRt\<cdot>b)) in
          if (sbHd\<cdot>b\<in>bs) then sbHd\<cdot>b \<bullet> rest else rest )"

  (* (if (sbHd\<cdot>b\<in>bs) then sbHd\<cdot>b \<bullet>(myiterate n bs (sbRt\<cdot>b)) else (myiterate n bs (sbRt\<cdot>b))) *)

definition sbFilterTupel:: " 'm SB set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbFilterTupel bs b \<equiv> \<Squnion>i. myiterate i bs b"

thm fix_def
definition sbFilterTupel2:: " 'm SB set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbFilterTupel2 A \<equiv> (\<Lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>(\<lambda>s. sbTake 0\<cdot>s))\<cdot>
      (\<Lambda> h. (\<lambda> b. if (sbHd\<cdot>b\<in>A) then sbHd\<cdot>b \<bullet> h (sbRt\<cdot>b) else h (sbRt\<cdot>b)))"
(* \<Squnion>i. iterate i\<cdot>(\<Lambda> f. (\<lambda>b. 
  if (b=sbLeast (sbDom\<cdot>b)) then sbLeast (sbDom\<cdot>b) else
    if (sbHd\<cdot>b\<in>bs) then (sbHd\<cdot>b) \<bullet> f (sbRt\<cdot>b) else f (sbRt\<cdot>b) ))\<cdot>(\<lambda>x. empty \<Omega>)"  *)



(* ----------------------------------------------------------------------- *)
section \<open>Lemmas\<close>
(* ----------------------------------------------------------------------- *)



subsection \<open>General Lemmas\<close>
(* Lemmas about Rep_SB, Abs_SB or 'm SBLub *)

(*Streambundles are sb_well by definition*)
theorem rep_well[simp]: "sb_well (Rep_SB x)"
using Rep_SB by auto

(*Rep und Abs - Theorems*)
theorem rep_abs[simp]: assumes "sb_well f" shows "Rep_SB (Abs_SB f) = f"
by (simp add: Abs_SB_inverse assms)

(* a chain of 'm SBs is also a chain after applying Rep_SB *)
lemma rep_chain[simp]: assumes "chain S"
  shows "chain (\<lambda>n. Rep_SB (S n))"
by (meson assms below_SB_def po_class.chain_def)

lemma theRep_chain[simp]: assumes "chain S" 
  shows "chain (\<lambda>n. the (Rep_SB (S n) c))"
using assms part_the_chain rep_chain by fastforce

lemma lub_well[simp]: assumes "chain S"
  shows "sb_well (\<Squnion>n. Rep_SB (S n))"
by (metis rep_chain adm_def sb_well_adm assms rep_well)

lemma rep_lub:assumes "chain Y"
  shows "(\<Squnion>i. Rep_SB (Y i)) = Rep_SB (\<Squnion>i.  Y i)"
using assms lub_SB by fastforce

lemma rep_cont [simp]: "cont Rep_SB"
by (metis rep_chain contI cpo_lubI rep_lub)

lemma rep_SB_up_lub[simp]: assumes "chain Y"
  shows "range (\<lambda>n. the (Rep_SB (Y n) c)) <<| the (\<Squnion>n. Rep_SB (Y n) c)"
by (metis rep_chain assms cpo_lubI part_the_cont2 theRep_chain)

(* an easy to use introduction rule for "sb_well" *)
lemma sb_wellI[simp]: assumes "\<And>c. c \<in> dom f \<Longrightarrow> sdom\<cdot>(the(f c)) \<subseteq> ctype c"
  shows "sb_well f"
by (simp add: assms sb_well_def)

lemma cont_Abs_SB[simp]: assumes "cont g" and "\<forall>x. sb_well (g x)"
  shows "cont (\<lambda>x. (g x)\<Omega>)"
by (simp add: assms(1) assms(2) cont_Abs_SB)

lemma [simp]: "(Rep_SB b2)\<Omega> = b2"
by (simp add: Rep_SB_inverse)

lemma wt2[simp]: assumes "c \<in> dom (Rep_SB (S k))" 
  shows "sdom\<cdot>(the (Rep_SB (S k) c)) \<subseteq> ctype c"
using assms rep_well sb_well_def by blast

lemma l400[simp]: assumes "chain S" and "c \<in> dom (Rep_SB (S k))"
  shows "c\<in>dom (Rep_SB (S j))"
by (metis assms(1) assms(2) below_SB_def is_ub_thelub part_dom_eq)

lemma l460: assumes "chain S" and "c \<in> dom (Rep_SB (S k))"
  shows "sdom\<cdot>(the (Rep_SB (S i) c)) \<subseteq> ctype c"
using assms(1) assms(2) l400 rep_well sb_well_def by blast

lemma l500: assumes "chain S" and "c \<in> dom (Rep_SB (S k))"
       shows "sdom\<cdot>(\<Squnion>j. the (Rep_SB (S j) c)) \<subseteq> ctype c"
by (smt assms(1) assms(2) l44 theRep_chain l460 lub_eq)

text {* Equivalence of evaluation of 'm SBLub based on lub of function values.*}
lemma lub_eval: assumes "chain S" 
  shows "the (Rep_SB (\<Squnion>i. S i) c) = (\<Squnion>j. the (Rep_SB (S j) c))"
using assms part_the_lub rep_chain rep_lub by fastforce

lemma l1: assumes "chain S" 
  shows "dom (Rep_SB (S i)) = dom (Rep_SB (\<Squnion>i. S i))"
by (meson assms below_SB_def is_ub_thelub part_dom_eq)

lemma less_SBI: assumes "dom (Rep_SB b1) = dom (Rep_SB b2)" 
    and "\<And>c. c\<in>dom (Rep_SB b1) \<Longrightarrow>  the ((Rep_SB b1) c) \<sqsubseteq> the ((Rep_SB b2) c)"
  shows "b1 \<sqsubseteq> b2"
by (metis assms(1) assms(2) below_SB_def below_option_def domIff fun_belowI)

lemma less_sbLub1: assumes "chain S" 
  shows "the (Rep_SB (S i) c) \<sqsubseteq> the (Rep_SB (\<Squnion>i. S i) c)"
by (metis assms(1) is_ub_thelub theRep_chain lub_eval)

lemma less_sbLub2: assumes "chain S"  and "range S <| u"
  shows "the (Rep_SB (\<Squnion>i. S i) c) \<sqsubseteq> the (Rep_SB u c)"
by (metis assms below_SB_def below_option_def eq_imp_below fun_below_iff is_lub_thelub)




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbDom\<close>
(* ----------------------------------------------------------------------- *)


(* sbDom continuous *)
lemma sbdom_cont [simp]: "cont (\<lambda> b. dom (Rep_SB b))"
by (simp add: cont_compose)

(* sbDom insert rule *)
lemma sbdom_insert: "sbDom\<cdot>b = dom (Rep_SB b)"
by (simp add: sbDom_def)

lemma sbdom_rep_eq: "sb_well b \<Longrightarrow> sbDom\<cdot>(Abs_SB b) = dom b"
by (simp add: sbDom_def)


(* in a below relation the sbDom's have to be equal *)
lemma sbdom_eq: assumes "a\<sqsubseteq>b"
  shows "sbDom\<cdot>a = sbDom\<cdot>b"
by (metis assms below_SB_def part_dom_eq sbdom_insert)

lemma sbdom_empty [simp]: "sbDom\<cdot>(empty \<Omega>) = {}"
by (simp add: sbdom_insert sb_well_def)




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbGetCh\<close>
(* ----------------------------------------------------------------------- *)

(* helper lemma for the continuous proof *)
lemma sbgetch_cont2[simp]: "cont (\<lambda> b c. the ((Rep_SB b) c))"
by (smt cont2cont_lambda contI cpo_lubI image_cong lub_eval theRep_chain) 

(* sbGetCh is cont *)
lemma sbgetch_cont [simp]: "cont (\<lambda> b. \<Lambda> c. the ((Rep_SB b) c))"
using cont2cont_LAM cont2cont_fun sbgetch_cont2 channel_cont by force

(* insert rule for sbGetCh *)
lemma sbgetch_insert: "b. c = the (Rep_SB b c)"
by (simp add: sbGetCh_def)

lemma sbgetch_rep_eq: "sb_well b \<Longrightarrow> (Abs_SB b . c) = (b \<rightharpoonup> c)"
by (simp add: sbGetCh_def)

lemma sbgetchE: assumes "(c\<in>sbDom\<cdot>b)"
  shows "Some (b .c) =  (Rep_SB b) c"
apply (simp add: domIff sbdom_insert sbgetch_insert)
using assms domIff sbdom_insert by force

lemma sbgetch_lub: "chain Y \<Longrightarrow> ((\<Squnion>i. Y i) . c) =  (\<Squnion>i. (Y i) . c)"
  by (metis (mono_tags, lifting) lub_eq lub_eval sbgetch_insert)





(* Zwischenteil, wird später gebraucht *)
(* verwendet sbDom && sbGetCh *)
lemma sbchain_dom_eq: assumes "chain S"
  shows "sbDom\<cdot>(S i) = sbDom\<cdot>(S j)"
by (simp add: assms l1 sbdom_insert)

lemma sbChain_dom_eq2: assumes "chain S"
  shows "sbDom\<cdot>(S i) = sbDom\<cdot>(\<Squnion>j. S j)"
by (simp add: assms l1 sbdom_insert)

lemma sb_eq: assumes "sbDom\<cdot>x = sbDom\<cdot>y" and "\<And>c. c\<in>(sbDom\<cdot>x) \<Longrightarrow> (x .c) = (y .c)"
  shows "x = y"
by (metis assms(1) assms(2) less_SBI po_eq_conv sbdom_insert sbgetch_insert)

(* the fact that this lemma is proven for lubs is only of secondary importance *)
lemma sbLub[simp]: fixes S:: "nat \<Rightarrow> 'm SB"
  assumes "chain S"
  shows "(\<lambda>c. (c \<in> sbDom\<cdot>(S i)) \<leadsto> (\<Squnion>j. (S j). c))\<Omega> = (\<Squnion>i. S i)" (is "?L = ?R")
proof (rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" by (smt Abs_cfun_inverse2 rep_abs assms domIff equalityI sbgetch_insert lub_eq lub_eval option.sel option.simps(3) sbChain_dom_eq2 sbDom_def sbGetCh_def sbdom_cont subsetI rep_well sb_well_def)
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  show "?L . c = ?R . c" 
  proof -
    have "?R . c = (\<Squnion>i. (S i) .c)" by (smt assms lub_eq lub_eval sbgetch_insert)  
    thus ?thesis by (smt Abs_cfun_inverse2 rep_abs assms domIff sbgetch_insert lub_eq lub_eval option.sel sbChain_dom_eq2 sbDom_def sbGetCh_def sbdom_cont rep_well sb_well_def)
  qed
qed

lemma sb_below[simp]: assumes "sbDom\<cdot>x = sbDom\<cdot>y" and "\<And>c. c\<in>sbDom\<cdot>x \<Longrightarrow> (x .c) \<sqsubseteq> (y .c)"
  shows "x \<sqsubseteq> y"
by (metis assms(1) assms(2) less_SBI sbdom_insert sbgetch_insert)


lemma [simp]: "(\<lambda>c. (c \<in> sbDom\<cdot>b)\<leadsto>b . c)\<Omega> = b"
  apply(rule sb_eq)
   apply(subst sbdom_rep_eq)
    apply (smt domIff rep_well sb_well_def sbgetchE)
   apply simp
  by (smt domIff option.distinct(1) option.sel rep_abs rep_well sbgetchE sb_well_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbLeast\<close>
(* ----------------------------------------------------------------------- *)

(* sbLeast produces a sb_well partial-function *)
lemma sbleast_well[simp]: "sb_well (\<lambda>c. (c \<in> cs)\<leadsto>\<epsilon>)"
by(auto simp add: sb_well_def)

lemma sbleast_sbdom [simp]: "sbDom\<cdot>(sbLeast cs) = cs"
by(simp add: sbDom_def sbLeast_def)

(* in all channels "c" in the channel set "cs" flows the stream "\<epsilon>" *)
lemma sbleast_getch [simp]: assumes "c \<in> cs" shows "sbLeast cs . c = \<epsilon>"
by (simp add: assms sbLeast_def sbgetch_insert)

(* sbLeast returns the smalles 'm SB with the given domain *)
lemma sbleast_least [simp]: assumes "cs = sbDom\<cdot>b"
  shows "sbLeast cs \<sqsubseteq> b"
by (metis (full_types) assms minimal sbleast_getch sbleast_sbdom sb_below)

lemma sbleast_empty: "sbLeast {} = Map.empty \<Omega>"
by (simp add: sbLeast_def)

(* if sbLeast{} (or empty\<Omega>) is in an chain, all elements are equal *)
lemma stbundle_allempty: assumes "chain Y" and "sbLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = sbLeast {}"
by (smt Rep_SB_inject assms(1) assms(2) dom_eq_empty_conv image_iff sbchain_dom_eq sbdom_insert sbleast_sbdom)



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbUnion\<close>
(* ----------------------------------------------------------------------- *)


(* sbUnion produces a sb_well partial-function *)
lemma sbunion_well[simp]: assumes "sb_well b1" and "sb_well b2"
  shows "sb_well (b1 ++ b2)"
by (metis assms(1) assms(2) domIff mapadd2if_then sb_well_def)

(* helper function for continuity proof *)
lemma sbunion_contL[simp]: "cont (\<lambda>b1. (Rep_SB b1) ++ (Rep_SB b2))"
using cont_compose part_add_contL rep_cont by blast

(* helper function for continuity proof *)
lemma sbunion_contR[simp]: "cont (\<lambda>b2. (Rep_SB b1) ++ (Rep_SB b2))"
using cont_compose part_add_contR rep_cont by blast

(* sbUnion is an coninuous function *)
lemma sbunion_cont[simp]: "cont (\<lambda> b1. \<Lambda> b2.((Rep_SB b1 ++ Rep_SB b2)\<Omega>))"
by(simp add: cont2cont_LAM)

(* insert rule for sbUnion *)
lemma sbunion_insert: "(b1 \<uplus> b2) = (Rep_SB b1 ++ Rep_SB b2)\<Omega>"
by(simp add: sbUnion_def)


(* if all channels in b1 are also in b2 the union produces b2 *)
lemma sbunion_idL [simp]: assumes "sbDom\<cdot>b1\<subseteq>sbDom\<cdot>b2" shows "b1 \<uplus> b2 = b2"
using assms apply(simp add: sbunion_insert)
by(simp add: sbdom_insert)

lemma sbunion_idR [simp]: "b \<uplus> (sbLeast {}) = b"
by(simp add: sbunion_insert sbLeast_def)

(* if b1 and b2 have no common channels, sbUnion is commutative *)
lemma sbunion_commutative: assumes "sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2 = {}"
  shows "b1\<uplus>b2 = b2\<uplus>b1"
using assms apply(simp add: sbunion_insert)
  by (metis map_add_comm sbdom_insert)
    
lemma sbunion_associative: "sb1 \<uplus> (sb2 \<uplus> sb3) = (sb1 \<uplus> sb2) \<uplus> sb3"
  by(simp add: sbunion_insert)

(* the second argument has priority in sbUnion *)
lemma sbunion_getchR [simp]: assumes "c\<in>sbDom\<cdot>b2"
  shows "b1\<uplus>b2 . c = b2 . c"
apply(simp add: sbunion_insert sbgetch_insert)
by (metis (full_types) assms map_add_find_right sbgetchE)

lemma sbunion_getchL [simp]: assumes "c\<notin>sbDom\<cdot>b2"
  shows "b1\<uplus>b2 . c = b1 . c"
apply(simp add: sbunion_insert sbgetch_insert)
by (metis assms map_add_dom_app_simps(3) sbdom_insert)

lemma sbunionDom [simp] : "sbDom\<cdot>(b1 \<uplus> b2) = sbDom\<cdot>b1 \<union> sbDom\<cdot>b2"
by(auto simp add: sbdom_insert sbunion_insert)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbSetCh\<close>
(* ----------------------------------------------------------------------- *)

  (*Welltyped is preserved after setting new sb_well channels.*)
lemma sbset_well [simp]: assumes "sdom\<cdot>s \<subseteq> ctype c"
  shows "sb_well ((Rep_SB b) (c \<mapsto> s) )"
by (metis assms dom_fun_upd fun_upd_apply insert_iff option.sel option.simps(3) rep_well sb_well_def)

(* sbSetCh is continuous on the first argument, if the second two arguments form a sb_well bundle *)
lemma sbsetch_insert: assumes "sdom\<cdot>s \<subseteq> ctype c"
  shows "(sbSetCh\<cdot>b) c s = b \<uplus> ([c \<mapsto> s]\<Omega>)"
by(simp add: assms sbSetCh_def)




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRestrict\<close>
(* ----------------------------------------------------------------------- *)

lemma sbrestrict_well [simp]: "sb_well (Rep_SB b |` cs)"
by (metis (no_types, lifting) domIff rep_well restrict_map_def sb_well_def)

lemma sbrestrict_monofun[simp]: "monofun  (\<lambda>b. Rep_SB b |` cs)"
by (smt below_SB_def fun_below_iff monofunI not_below2not_eq restrict_map_def )

lemma sbrestrict_cont1[simp]: "cont  (\<lambda>b. ((Rep_SB b) |` cs))"
apply(rule contI2)
apply(auto)
by (smt below_option_def fun_below_iff is_ub_thelub lub_eq lub_fun po_class.chain_def rep_chain rep_lub restrict_in restrict_out)

(* sbRestrict is continuous on the second argument *)
lemma sbrestrict_cont[simp]: "cont  (\<lambda>b. ((Rep_SB b) |` cs)\<Omega>)"
by (simp)

lemma sbrestrict_insert: "b \<bar> cs = (Rep_SB b) |` cs \<Omega>"
by(simp add: sbRestrict_def)

lemma sbrestrict_sbdom[simp]: "sbDom\<cdot>(b \<bar> cs) = sbDom\<cdot>b \<inter> cs"
by (simp add: sbDom_def sbrestrict_insert)

lemma sbrestrict_id [simp]: assumes "sbDom\<cdot>b \<subseteq> cs" shows "b \<bar> cs = b"
using assms apply(simp add: sbrestrict_insert sbdom_insert)
by (metis (no_types, lifting) IntD2 dom_restrict inf.orderE rep_abs restrict_in sbdom_insert sbgetch_insert sbrestrict_well sb_eq)

lemma sbrestrict_least[simp]: "b \<bar> {} = sbLeast {}"
by(simp add: sbrestrict_insert sbLeast_def)

lemma sbrestrict_least2[simp]: assumes "cs \<inter>sbDom\<cdot>b = {}" shows "b \<bar> cs = sbLeast {}"
by (metis assms ex_in_conv inf_commute sbleast_sbdom sbrestrict_sbdom sb_eq)

lemma sbrestrict2sbgetch[simp]: assumes "c\<in>cs"
  shows "(b\<bar>cs) . c = b. c"
by(simp add: assms sbgetch_insert sbrestrict_insert)

(* if h is continuous then so is the composition of h with a restriction *)
lemma sbrestrict_below [simp]:  assumes "chain Y" and "cont h"
      shows "(h (\<Squnion>i. Y i) \<bar> g (sbDom\<cdot>(\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. (h (Y i) \<bar> g (sbDom\<cdot>(Y i)) ))"
by (smt assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_arg lub_eq po_eq_conv sbChain_dom_eq2)

lemma sbunion_restrict [simp]: assumes "sbDom\<cdot>b2 = cs"
  shows "(b1 \<uplus> b2) \<bar> cs = b2"
apply(simp add: sbunion_insert sbrestrict_insert )
by (metis (no_types) Rep_SB_inverse assms map_union_restrict2 sbdom_insert)

lemma sbunion_restrict2 [simp]: assumes "sbDom\<cdot>b2 \<inter> cs = {}"
  shows "(b1 \<uplus> b2) \<bar> cs = b1 \<bar> cs" 
  apply(rule sb_eq)
   apply (simp add: Int_Un_distrib2 assms)
  using assms sbunion_getchL by fastforce

lemma sbunion_restrict3: "(b1 \<uplus> b2) \<bar> cs = (b1 \<bar> cs) \<uplus> (b2 \<bar> cs)"
apply(simp add: sbrestrict_insert sbunion_insert)
by (metis (full_types) mapadd2if_then restrict_map_def)  
  

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRemCh\<close>
(* ----------------------------------------------------------------------- *)

lemma sbremch_monofun[simp]:"monofun (\<lambda> b. \<Lambda> c.  b \<bar> -{c})"
by(simp add: below_cfun_def monofun_cfun_arg fun_belowI monofunI )

(* das gehört woanders hin, eigentlich in cfun definition... also vllt Prelude *)
lemma rep_cfun_cont: assumes "chain Y"
  shows "Rep_cfun (\<Squnion>i. (Y i)) = (\<Squnion>i. (Rep_cfun ((Y i))))"
proof -
  have "\<And>f. chain (\<lambda>n. Rep_cfun (f n::'a \<rightarrow> 'b)) \<or> \<not> chain f"
    by (meson below_cfun_def po_class.chain_def)
  then have "\<And>f a. (\<Squnion>n. Rep_cfun (f n)) (a::'a) = (Lub f\<cdot>a::'b) \<or> \<not> chain f"
    by (metis contlub_cfun_fun lub_fun)
  then show ?thesis
    by (metis (no_types) assms fun_belowI po_eq_conv)
qed

(* removing the channel c from the lub of the chain Y of SBs is less than or equal to removing c from
   every element of the chain and then taking the lub *)
lemma sbremch_cont1[simp]: assumes "chain Y"
  shows "(\<Lambda> c. (\<Squnion>i. Y i)\<bar>- {c}) \<sqsubseteq> (\<Squnion>i. \<Lambda> c. Y i\<bar>- {c})"
proof -
  have lub_cont:"cont (\<Squnion>i. (\<lambda> c. Y i\<bar>- {c}))" using channel_cont by blast
  hence eq: "Rep_cfun (\<Squnion>i. \<Lambda> c. Y i\<bar>- {c}) =  (\<Squnion>i. Rep_cfun (\<Lambda> c. Y i\<bar>- {c}))" by(simp add: rep_cfun_cont assms)
  have "(\<lambda> c. (\<Squnion>i. Y i)\<bar>- {c}) \<sqsubseteq> (\<Squnion>i. (\<lambda> c. Y i\<bar>- {c}))"
    by (smt assms contlub_cfun_arg eq_imp_below fun_belowI lub_eq lub_fun monofun_cfun_arg po_class.chain_def)
  thus ?thesis
    by (metis (no_types, lifting) Abs_cfun_inverse2 below_cfun_def channel_cont eq lub_eq)
qed

lemma sbremch_cont[simp]: "cont (\<lambda> b. \<Lambda> c.  b \<bar> -{c})"
by(rule contI2, auto)

(* insert rule for sbRemCh *)
lemma sbremch_insert: "sbRemCh\<cdot>b\<cdot>c =  b \<bar> -{c}"
by (simp add: sbRemCh_def)

lemma sbremch_sbdom[simp]: "sbDom\<cdot>(sbRemCh\<cdot>b\<cdot>c) = sbDom\<cdot>b - {c}"
by(simp add: sbremch_insert diff_eq)

lemma sbrem2sbrestrict: "sbRemCh\<cdot>b\<cdot>c = b \<bar> (sbDom\<cdot>b - {c})"
by (smt Int_absorb1 Int_commute Int_lower2 Set.basic_monos(7) sbremch_insert sbremch_sbdom sbrestrict2sbgetch sbrestrict_sbdom sb_eq)





(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRenameCh\<close>
(* ----------------------------------------------------------------------- *)
lemma sbrenamech_id: assumes "c\<in>sbDom\<cdot>b"
  shows "sbRenameCh b c c = b"
apply(simp add: sbRenameCh_def sbgetch_insert sbSetCh_def sbremch_insert sbrestrict_insert)
by (smt Rep_SB_inverse assms dom_empty dom_fun_upd fun_upd_same fun_upd_triv fun_upd_upd map_add_empty map_add_upd option.distinct(1) option.sel rep_abs rep_well restrict_complement_singleton_eq sbdom_insert sbgetchE sbrestrict_well sbunion_insert singletonD sb_well_def)





(* ----------------------------------------------------------------------- *)
  subsection \<open>sbUp\<close>
(* ----------------------------------------------------------------------- *)
lemma sbup_well[simp]: "sb_well (\<lambda>c. if c \<in> sbDom\<cdot>b then (Rep_SB b)c else Some \<epsilon>)"
by (smt domIff rep_well sbleast_well sb_well_def)
 
  lemma sbup_cont1[simp]: "cont (\<lambda>b. (\<lambda> c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b)c else Some \<epsilon>))"
  by (smt Prelude.contI2 below_SB_def eq_imp_below fun_below_iff is_ub_thelub lub_eq lub_fun monofunI po_class.chainE po_class.chainI rep_lub sbdom_eq sbgetchE)

lemma sbup_cont[simp]: "cont (\<lambda>b. (\<lambda> c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b)c else Some \<epsilon>)\<Omega>)"
by simp

lemma sbup_insert: "\<up>b = (\<lambda>c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b) c else Some \<bottom>)\<Omega>"
by(simp add: sbUp_def)



lemma sbup_sbdom [simp]: "sbDom\<cdot>(\<up>b) = UNIV"
apply(simp add: sbdom_insert )
apply(simp add: sbup_insert)
by (smt CollectD Collect_cong UNIV_def dom_def optionLeast_def optionleast_dom sbdom_insert)

lemma sbup_sbgetch[simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "\<up>b . c = b .c"
by (simp add: assms sbgetch_insert sbup_insert)

lemma sbup_sbgetch2[simp]: assumes "c\<notin>sbDom\<cdot>b"
  shows "\<up>b . c = \<epsilon>"
by (simp add: assms sbgetch_insert sbup_insert)

lemma [simp]: "\<up>(sbLeast cs) . c = \<epsilon>"
by (metis sbleast_getch sbleast_sbdom sbup_sbgetch sbup_sbgetch2)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbEqSelected\<close>
(* ----------------------------------------------------------------------- *)
lemma [simp]: "sbEqSelected {} b1 b2"
by(simp add: sbEqSelected_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbEqCommon\<close>
(* ----------------------------------------------------------------------- *)

lemma assumes "sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2 = {}"
  shows "sbEqCommon b1 b2"
by(simp add: sbEqCommon_def assms)



(* ----------------------------------------------------------------------- *)
  subsection \<open>SB\<close>
(* ----------------------------------------------------------------------- *)

lemma sb_exists[simp]: "(sbLeast cs)\<in>(cs^\<Omega>)"
by (simp add: SB_def)

(* all 'm SBs in cs^\<Omega> have the domain cs *)
lemma sb_sbdom[simp]: "sbDom\<cdot>(SOME b. b \<in> cs^\<Omega>) = cs"
by (metis (mono_tags, lifting) SB_def mem_Collect_eq sb_exists someI_ex)

lemma sb_empty: "{}^\<Omega> = {sbLeast {} }"
apply(simp add: SB_def sbdom_insert sbLeast_def)
apply rule
apply (metis (mono_tags, lifting) Rep_SB_inverse mem_Collect_eq singleton_iff subsetI)
by auto





(* ----------------------------------------------------------------------- *)
  subsection \<open>sbConc\<close>
(* ----------------------------------------------------------------------- *)
lemma sbconc_well[simp]: "sb_well (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>b2. c))) "
apply(rule sb_wellI)
apply(simp add: sbdom_insert )
by (smt UNIV_I Un_least dual_order.trans rep_well sb_well_def sbdom_insert sbgetch_insert sbup_sbdom sconc_sdom)

(* From here: coninuity proof for sbConc *)
lemma sbconct_mono1[simp]: "monofun (\<lambda>b2. (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>b2. c))))"
apply(rule monofunI)
by (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun) 

(* helper function to proof coninuity *)
lemma channel_insert: assumes "chain Y"
  fixes x:: channel
  shows  "(\<Squnion>n. (\<lambda>c :: channel. Some ((\<up>b1 . c) \<bullet> (\<up>Y n) . c))) x = (\<Squnion>n. Some ((\<up>b1 . x) \<bullet> (\<up>Y n) . x))"
proof -
  have "chain (\<lambda>n. (\<lambda>c. Some ((\<up>b1 . c) \<bullet> \<up>Y n . c)))"
    by (smt UNIV_I assms below_SB_def below_option_def fun_below_iff monofun_cfun_arg option.distinct(1) option.sel po_class.chain_def rep_abs sbchain_dom_eq sbgetchE sbup_insert sbup_sbdom sbup_well)
  thus ?thesis using lub_fun by fastforce 
qed

(* for any chain Y of SBs prepending to the lub never produces a SB that is strictly greater than prepending
   to every element and then taking the lub *)
lemma sbconc_lub: assumes "chain Y"
  shows "(\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>(\<Squnion>n. Y n)). c)) \<sqsubseteq> (\<Squnion>n. (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>Y n). c)))" (is "?L \<sqsubseteq> ?R")
proof (rule fun_belowI)
  fix c
  have "Some ((\<up>b1 . c) \<bullet> \<up>\<Squnion>n. Y n . c) \<sqsubseteq> (\<Squnion>n.  Some ((\<up>b1 . c) \<bullet> \<up>Y n . c))"
    by (smt assms contlub_cfun_arg if_then_lub lub_eq lub_eval monofun_cfun_arg po_class.chain_def sbgetch_insert theRep_chain) 
  thus "Some ((\<up>b1 . c) \<bullet> \<up>\<Squnion>n. Y n . c) \<sqsubseteq> (\<Squnion>n. (\<lambda>c. Some ((\<up>b1 . c) \<bullet> \<up>Y n . c))) c"
    by (simp add: assms channel_insert)  
qed

lemma sbconct_cont1[simp]: "cont (\<lambda>b2. (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>b2. c))))"
apply(rule contI2)
using sbconct_mono1 apply blast
using sbconc_lub by blast


lemma cont_restrict_sbdom[simp]: "cont (\<lambda>b. g\<cdot>b \<bar> h (sbDom\<cdot>b))"
apply(rule contI)
by (smt ch2ch_Rep_cfunR contlub_cfun_arg cpo_lubI image_cong sbChain_dom_eq2)

(* sbConc is continuous on the second argument *)
lemma sbconct_monofun[simp]: "monofun (\<lambda> b2. ((\<lambda>c. Some ((\<up>b1. c) \<bullet> \<up>b2. c))\<Omega>) \<bar> (sbDom\<cdot>b1 \<union> sbDom\<cdot>b2))"
proof (rule monofunI)
  fix x :: "'a SB" and y :: "'a SB"
  assume a1: "x \<sqsubseteq> y"
  then have f2: "sbDom\<cdot>y = sbDom\<cdot>x"
    by (metis sbdom_eq)
  have f3: "\<And>f. \<not> cont f \<or> (f x::'a SB) \<sqsubseteq> f y"
    using a1 by (metis (no_types) Abs_cfun_inverse2 monofun_cfun_arg)
  have "\<And>s. cont (\<lambda>sa. (\<lambda>c. Some ((\<up>s::'a SB . c) \<bullet> \<up>sa . c))\<Omega>)"
    using SBTheorie.cont_Abs_SB sbconc_well sbconct_cont1 by blast
  then have "(\<lambda>c. Some ((\<up>b1 . c) \<bullet> \<up>x . c))\<Omega> \<sqsubseteq> (\<lambda>c. Some ((\<up>b1 . c) \<bullet> \<up>y . c))\<Omega>"
    using f3 by blast
  then show "((\<lambda>c. Some ((\<up>b1 . c) \<bullet> \<up>x . c))\<Omega>)\<bar>sbDom\<cdot>b1 \<union> sbDom\<cdot>x \<sqsubseteq> ((\<lambda>c. Some ((\<up>b1 . c) \<bullet> \<up>y . c))\<Omega>)\<bar>sbDom\<cdot>b1 \<union> sbDom\<cdot>y"
    using f2 monofun_cfun_arg by auto
qed

(* restricting the concatenation of the SBs b1 and b2 by the union of their domains has no effect,
   so the function is continuous based on previously established results for concatenation *)
lemma sbconct_cont[simp]: "cont (\<lambda> b2. ((\<lambda>c. Some ((\<up>b1. c) \<bullet> \<up>b2. c))\<Omega>) \<bar> (sbDom\<cdot>b1 \<union> sbDom\<cdot>b2))"
apply(rule contI2)
using sbconct_monofun apply blast
apply rule+
apply(rule sbrestrict_below)
by (simp_all)

(* insert rule for sbConc *)
lemma sbconc_insert: "b1 \<bullet> b2 = ((\<lambda>c. Some ((\<up>b1. c) \<bullet> \<up>b2. c))\<Omega>) \<bar> (sbDom\<cdot>b1 \<union> sbDom\<cdot>b2)"
by (simp add: sbConc_def)

lemma sbconc_sbdom[simp]: "sbDom\<cdot>(b1 \<bullet> b2) = sbDom\<cdot>b2 \<union> sbDom\<cdot>b1"
apply(simp add:  sbconc_insert sbrestrict_sbdom)
apply(simp add: sbdom_insert)
by blast

(* helper lemma, used in the lemma below *)
lemma sbup_restrict_id [simp]: assumes "c\<in>sbDom\<cdot>b2"
  shows "(((\<lambda>c. Some (\<up>b2 . c))\<Omega>)\<bar>sbDom\<cdot>b2) . c = b2 . c"
by (smt Abs_cfun_inverse2 UNIV_I assms rep_abs restrict_in sbDom_def sbdom_cont sbgetchE sbgetch_insert sbrestrict_insert sbrestrict_well sbup_insert sbup_sbdom sbup_well sb_well_def)

lemma [simp]: assumes "c\<in>sbDom\<cdot>b2"
  shows "((\<lambda>c. Some (\<up>b2 . c))\<Omega>) . c = b2 . c"
using assms sbup_restrict_id by fastforce

(* the empty 'm SB (with a subset of channels) concatinated to the left is the identity *)
lemma sbconc_idL[simp]: assumes "cs\<subseteq> sbDom\<cdot>b2"
  shows "(sbLeast cs) \<bullet> b2 = b2" (is "?L = ?R")
proof (rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" using assms sbconc_sbdom by auto
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence c_def: "c\<in>sbDom\<cdot>?R" using assms sbconc_sbdom by auto
  have "\<forall>c. \<up>(sbLeast cs) . c = \<epsilon>" by simp
  thus "?L . c = b2 . c" using c_def by(simp add: sbconc_insert)
qed

(* the empty 'm SB (with a subset of channels) concatinated to the right is the identity *)
lemma sbconc_idR[simp]: assumes "cs\<subseteq> sbDom\<cdot>b1"
  shows "b1 \<bullet> (sbLeast cs) = b1" (is "?L = ?R")
proof (rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" using assms sbconc_sbdom by auto
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence c_def: "c\<in>sbDom\<cdot>?R" using assms sbconc_sbdom by auto
  have "\<forall>c. \<up>(sbLeast cs) . c = \<epsilon>" by simp
  thus "?L . c = b1 . c" using c_def by(simp add: sbconc_insert)
qed

lemma sbconc_idLempty [simp]: "(empty \<Omega>) \<bullet> b2 = b2"
using sbconc_idL sbleast_empty by (metis empty_subsetI)

lemma sbconc_idRempty [simp]: "b1 \<bullet> (empty \<Omega>) = b1"
using sbconc_idR sbleast_empty by (metis empty_subsetI)

lemma sbconc_sbgetch: assumes "c\<in>(sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2)"
  shows "(b1 \<bullet> b2) .c = (b1 .c)\<bullet>(b2. c)"
using assms sbconc_insert sbconc_well sbgetch_insert sbrestrict2sbgetch sbup_sbgetch 
  by (smt Int_ac(3) Int_lower2 UnCI option.sel rep_abs subsetCE)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbConcCommon\<close>
(* ----------------------------------------------------------------------- *)

lemma sbconccommon_cont[simp]: "cont (\<lambda> b2. (b1 \<bullet> b2)\<bar>sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2)"
by (metis (no_types) cont_restrict_sbdom)

lemma sbconccommon_insert: "sbConcCommon b1\<cdot>b2 =  (b1 \<bullet> b2)\<bar>sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2"
by(simp add: sbConcCommon_def)

(* sbConcCommon, which concatenates two SBs b1 and b2 and filters the intersection is equivalent to
   filtering one SB by the other and then concatenating *)
lemma sbconccommon_insert2: "sbConcCommon b1\<cdot>b2 =  (b1\<bar>sbDom\<cdot>b2) \<bullet> (b2\<bar>sbDom\<cdot>b1)" (is "?L = ?R")
proof (rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" by (simp add: Int_commute inf_assoc sbconccommon_insert) 
  fix c
  assume "c \<in> sbDom\<cdot>?L" 
  hence c_def: "c\<in>(sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2)" by (simp add: sbconccommon_insert)
  hence l_c: "?L . c = (b1 .c)\<bullet>(b2. c)" by(simp add: sbconccommon_insert sbconc_sbgetch)
  have "?R . c = (b1 .c)\<bullet>(b2. c)" by (metis (mono_tags) Int_iff c_def sbconc_sbgetch sbrestrict2sbgetch sbrestrict_sbdom) 
  thus "?L . c = ?R . c" by (simp add: l_c)
qed



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbMapStream\<close>
(* ----------------------------------------------------------------------- *)

lemma [simp]: assumes "\<forall>s. sdom\<cdot>(f s) \<subseteq> sdom\<cdot>s"
  shows "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
using assms by blast

lemma sbmapstream_well[simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "sb_well (\<lambda>c. (c \<in> sbDom\<cdot>b)\<leadsto>f (b. c))"
by (smt Abs_cfun_inverse2 assms domIff option.sel rep_well sbDom_def sb_well_def sbdom_cont sbgetch_insert)

lemma sbmapstream_dom [simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))" 
  shows "sbDom\<cdot>(sbMapStream f b) = sbDom\<cdot>b"
by (smt Abs_cfun_inverse2 Collect_cong assms domI domIff dom_def option.sel rep_abs rep_well sbDom_def sbMapStream_def sb_well_def sbdom_cont sbgetch_insert)

lemma sbmapstream_sbgetch [simp]: assumes"\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))" and "c\<in>sbDom\<cdot>b"
  shows "(sbMapStream f b) . c = f (b .c)"
by (simp add: assms(1) assms(2) sbMapStream_def sbgetch_insert)

(* for any continuous function f from stream to stream which preserves the well-typed property,
   (sbMapStream f) is also continuous *)
lemma sbmapstream_cont [simp]: assumes "cont f" and "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "cont (sbMapStream f)"
proof (rule contI2)
  show "monofun (sbMapStream f)" 
  proof  (rule monofunI)
    fix x y:: "('a ::message) SB"
    assume "x \<sqsubseteq> y"
    thus "sbMapStream f x \<sqsubseteq> sbMapStream f y "
      by (smt Abs_cfun_inverse2 assms(1) assms(2) below_SB_def below_option_def eq_imp_below fun_below_iff monofun_cfun_arg sbdom_eq sbgetch_insert sbmapstream_dom sbmapstream_sbgetch sb_below)
  qed
  thus "\<forall>Y. chain Y \<longrightarrow> sbMapStream f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. sbMapStream f (Y i))"
    by (smt  assms(1) assms(2) ch2ch_monofun cont2contlubE eq_imp_below l1 theRep_chain less_SBI lub_eq lub_eval option.sel rep_abs sbGetCh_def sbMapStream_def sbdom_insert sbgetch_insert sbmapstream_dom sbmapstream_well) 
qed

lemma sbmapstream_cont2[simp]:  assumes "cont f" and "\<forall>s. sdom\<cdot>(f s)\<subseteq>sdom\<cdot>s"
  shows "cont (sbMapStream f)"
by (meson assms(1) assms(2) sbmapstream_cont subset_eq)



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbTake\<close>
(* ----------------------------------------------------------------------- *)
lemma sbtake_cont [simp]:"cont (\<lambda>b. sbMapStream (\<lambda>s. stake n\<cdot>s) b)"
by (simp add: f1)

lemma sbtake_insert: "sbTake n\<cdot>b \<equiv>  sbMapStream (\<lambda>s. stake n\<cdot>s) b"
by(simp add: sbTake_def)

lemma sbtake_zero: "sbTake 0\<cdot>In = sbLeast (sbDom\<cdot>In)"
by(simp add: sbtake_insert sbMapStream_def sbLeast_def)

lemma sbtake_sbdom[simp]: "sbDom\<cdot>(sbTake n\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbtake_insert f1)

lemma sbtake_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "sbTake n\<cdot>b . c = stake n\<cdot>(b .c)"
using assms by(simp add: sbtake_insert f1)

lemma sbtake_below [simp]: "sbTake n\<cdot>b \<sqsubseteq> sbTake (Suc n)\<cdot>b"
by (metis eq_imp_le le_Suc_eq sbtake_sbdom sbtake_sbgetch stake_mono sb_below)

lemma sbtake_chain [simp]: "chain (\<lambda>n. sbTake n\<cdot>b)"
by (simp add: po_class.chainI)

lemma sbtake_lub_sbgetch: assumes "c\<in>sbDom\<cdot>b"
  shows "(\<Squnion>n. sbTake n\<cdot>b) . c = (\<Squnion>n. stake n\<cdot>(b . c))"
by (metis (mono_tags, lifting) assms lub_eq lub_eval po_class.chainI sbgetch_insert sbtake_below sbtake_sbgetch)

lemma sbtake_lub [simp]: "(\<Squnion>n. sbTake n\<cdot>b) = b" (is "?L = b")
proof(rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>b" by (metis po_class.chainI sbChain_dom_eq2 sbtake_below sbtake_sbdom)
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c\<in>sbDom\<cdot>b" by (simp add: \<open>sbDom\<cdot>(\<Squnion>n. sbTake n\<cdot>b) = sbDom\<cdot>b\<close>)
  hence "?L . c = (\<Squnion>n. stake n\<cdot>(b . c))" using sbtake_lub_sbgetch by auto
  thus "?L .c = b .c"  by (simp add: reach_stream)
qed


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbHd\<close>
(* ----------------------------------------------------------------------- *)
lemma sbhd_sbdom[simp]: "sbDom\<cdot>(sbHd\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbHd_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbDrop\<close>
(* ----------------------------------------------------------------------- *)
lemma sbdrop_cont [simp]:"cont (\<lambda>b. sbMapStream (\<lambda>s. sdrop n\<cdot>s) b)"
by simp

lemma sbdrop_insert: "sbDrop n\<cdot>b = sbMapStream (\<lambda>s. sdrop n\<cdot>s) b"
by(simp add: sbDrop_def)

lemma sbdrop_zero[simp]: "sbDrop 0\<cdot>b = b"
by(simp add: sbdrop_insert sbMapStream_def)


lemma sbdrop_sbdom[simp]: "sbDom\<cdot>(sbDrop n\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbdrop_insert f1)

lemma sbdrop_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "sbDrop n\<cdot>b . c = sdrop n\<cdot>(b .c)"
using assms by(simp add: sbdrop_insert f1)


lemma sbtake_sbdrop [simp]: "sbTake n\<cdot>b \<bullet> sbDrop n\<cdot>b = b" (is "?L = b")
proof(rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>b" by(simp)
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c\<in>sbDom\<cdot>b" by simp
  hence "c\<in>(sbDom\<cdot>(sbTake n\<cdot>b) \<inter> sbDom\<cdot>(sbDrop n\<cdot>b))" by simp
  hence "?L . c = (((sbTake n\<cdot>b) .c) \<bullet>  (sbDrop n\<cdot>b) . c)" using sbconc_sbgetch by blast
  hence "?L . c = (stake n\<cdot>(b . c)) \<bullet>  (sdrop n\<cdot>(b . c))" by (simp add: \<open>c \<in> sbDom\<cdot>b\<close>)
  thus "?L . c = b . c" by simp
qed


lemma sbdrop_plus [simp]: "sbDrop n\<cdot>(sbDrop k\<cdot>sb) = sbDrop (n+k)\<cdot>sb"
  apply(rule sb_eq)
   apply simp
  apply(simp add: sbDrop_def)
  by (simp add: sdrop_plus)






(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRt\<close>
(* ----------------------------------------------------------------------- *)
lemma sbrt_sbdom[simp]: "sbDom\<cdot>(sbRt\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbRt_def)


lemma sbhd_sbrt [simp]: "(sbHd\<cdot>b \<bullet> sbRt\<cdot>b) = b"
by (simp add: sbHd_def sbRt_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>snNtimes\<close>
(* ----------------------------------------------------------------------- *)

lemma sbntimes_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "(n\<star>b) . c = sntimes n (b . c)"
using assms by(simp add: sbNTimes_def)

lemma sbntimes_zero [simp]: "0\<star>b = sbLeast (sbDom\<cdot>b)" 
by(simp add: sbNTimes_def sbMapStream_def sntimes_def sbLeast_def)

lemma sbntimes_one [simp]: fixes b:: "'m SB" shows "1\<star>b = b" 
by(simp add: sbNTimes_def sbMapStream_def sntimes_def sbLeast_def)

lemma sbntimes_sbdom [simp]: "sbDom\<cdot>(i\<star>b) = sbDom\<cdot>b"
by(simp add: sbNTimes_def)

lemma sbntimes_below [simp]: fixes b:: "'m SB"
  shows "(i\<star>b) \<sqsubseteq> (Suc i)\<star>b" (is "?L \<sqsubseteq> ?R")
proof(rule sb_below)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" by simp
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c\<in>sbDom\<cdot>b" by simp
  thus "?L . c \<sqsubseteq> ?R . c" using sntimes_leq by auto 
qed

lemma sbntimes_chain[simp]: fixes b:: "'m SB"
  shows "chain (\<lambda>i. i\<star>b)"
by (simp add: po_class.chainI)

lemma sbntimes2sinftimes: assumes "chain Y" and "c\<in>sbDom\<cdot>b"
  shows "(\<Squnion>i. i\<star>b) . c = sinftimes (b . c)"
proof -
  have "(\<Squnion>i. i\<star>b) . c = (\<Squnion>i. (i\<star>b) . c)" by (simp add: contlub_cfun_arg contlub_cfun_fun)
  hence "(\<Squnion>i. i\<star>b) . c = (\<Squnion> i. sntimes i (b . c))" using assms(2) by auto
  thus ?thesis by (simp add: sntimesLub) 
qed



(* ----------------------------------------------------------------------- *)
  subsection \<open>snInfTimes\<close>
(* ----------------------------------------------------------------------- *)

lemma sbinftimes_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "(sbInfTimes b) . c = sinftimes (b . c)"
using assms by(simp add: sbInfTimes_def)

lemma sbinftimes_sbdom [simp]: "sbDom\<cdot>(b\<infinity>) = sbDom\<cdot>b"
by(simp add: sbInfTimes_def)

lemma sntimes_lub: fixes b:: "'m SB"
  shows "(\<Squnion>i. i\<star>b) = b\<infinity>" (is "?L = ?R")
proof (rule sb_eq)
  have "sbDom\<cdot>?L = sbDom\<cdot>b" by (metis po_class.chainI sbChain_dom_eq2 sbntimes_below sbntimes_sbdom)
  thus "sbDom\<cdot>?L = sbDom\<cdot>?R" by simp

  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c\<in>sbDom\<cdot>b" using sbChain_dom_eq2 sbntimes_chain sbntimes_sbdom by blast 
  hence "\<And>c. c \<in> sbDom\<cdot>b \<Longrightarrow> (\<Squnion>i. i\<star>b) . c = b\<infinity> . c" by (metis (full_types) sbinftimes_sbgetch sbntimes2sinftimes sbntimes_chain)
  hence "(\<Squnion>i. i\<star>b) . c = (\<Squnion>i. i\<star>(b . c))" by (simp add: \<open>c \<in> sbDom\<cdot>(\<Squnion>i. i\<star>b)\<close> \<open>c \<in> sbDom\<cdot>b\<close> sntimesLub)
  thus "?L . c = ?R . c" using \<open>c \<in> sbDom\<cdot>b\<close> sntimesLub by force 
qed



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbMap\<close>
(* ----------------------------------------------------------------------- *)
lemma assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>((\<lambda>s. smap f\<cdot>s) s)\<subseteq>(ctype c))"
  shows "sbDom\<cdot>(sbMap f\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbMap_def assms)



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbFilter\<close>
(* ----------------------------------------------------------------------- *)
lemma sbfilter_sbdom [simp]: "sbDom\<cdot>(sbFilter A\<cdot>b) = sbDom\<cdot>b"
by (smt Abs_cfun_inverse2 cont_Rep_cfun2 sbFilter_def sbfilter_sbdom sbmapstream_cont sbmapstream_dom subsetCE subsetI)

lemma sbfilter_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows  "(sbFilter A\<cdot>b) . c = sfilter A\<cdot>(b .c)"
apply(simp add: sbFilter_def assms)
by (meson StreamTheorie.sbfilter_sbdom assms sbmapstream_sbgetch subsetCE subsetI)


(* ----------------------------------------------------------------------- *)
  (* Lemma *)
(* ----------------------------------------------------------------------- *)


lemma if_then_dom[simp]: "dom (\<lambda>c. (c \<in> cs)\<leadsto>b .c) = cs"
using dom_def by fastforce

lemma if_then_well[simp]: assumes "cs\<subseteq>sbDom\<cdot>b" shows "sb_well (\<lambda>c. (c\<in>cs) \<leadsto> (b .c))"
using assms apply(simp add: sb_well_def sbgetch_insert sbdom_insert)
using rep_well sb_well_def by blast








lemma if_then_chain[simp]: assumes "chain Y" and "monofun g"
  shows "chain (\<lambda>i. (sbDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
proof(cases "sbDom\<cdot>(Y 0) = In")
  case True 
  hence "\<forall>i. (sbDom\<cdot>(Y i) = In)" using assms(1) sbchain_dom_eq by blast
  thus ?thesis
    by (smt assms(1) assms(2) below_option_def monofunE option.sel option.simps(3) po_class.chain_def)
next
  case False
  hence "\<forall>i. (sbDom\<cdot>(Y i) \<noteq> In)" using assms(1) sbchain_dom_eq by blast
  thus ?thesis by (auto) 
qed

lemma if_then_mono [simp]:  assumes "monofun g"
  shows "monofun (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)"
proof(rule monofunI)
  fix x y :: "'a SB"
  assume "x\<sqsubseteq>y"
  hence "sbDom\<cdot>x = sbDom\<cdot>y" using sbdom_eq by blast 
  thus "(sbDom\<cdot>x = In)\<leadsto>g x \<sqsubseteq> (sbDom\<cdot>y = In)\<leadsto>g y" by (smt \<open>(x::'a SB) \<sqsubseteq> (y::'a SB)\<close> assms monofunE po_eq_conv some_below) 
qed

lemma if_then_cont [simp]:  assumes "cont g"
  shows "cont (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)"
proof(rule contI2)
  show "monofun (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>g b)" using assms cont2mono if_then_mono by blast 
  thus " \<forall>Y. chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = In)\<leadsto>g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. (sbDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
    by (smt Abs_cfun_inverse2 assms if_then_lub lub_chain_maxelem lub_eq po_eq_conv sbChain_dom_eq2)
qed

lemma if_then_sbDom: assumes "d \<in> dom (\<lambda>b. (sbDom\<cdot>b = In)\<leadsto>(F b))"
  shows "sbDom\<cdot>d = In"
by (smt assms domIff)



end

