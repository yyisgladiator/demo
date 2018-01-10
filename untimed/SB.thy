(*  Title:        SBTheorie
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Stream Bundles" 
*)

theory SB
imports "../inc/OptionCpo" "../UnivClasses" "../UBundle" "../UBundle_Pcpo" "../Channel" Streams

begin

default_sort message


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)


instantiation stream :: (message) uscl
begin

definition usOkay_stream_def: "usOkay c m \<equiv> sdom\<cdot>m \<subseteq> ctype c"

definition usLen_stream_def: "usLen \<equiv> slen"

instance
  apply intro_classes
  apply (rule admI)
  by (simp add: usOkay_stream_def l44)

end

(* ----------------------------------------------------------------------- *)
  section \<open>Function Definition\<close>
(* ----------------------------------------------------------------------- *)

(*
definition sbConc:: "'m stream ubundle \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbConc b1 \<equiv> \<Lambda> b2. ((\<lambda>c. Some (((\<up>b1). c) \<bullet> (\<up>b2). c))\<Omega>) \<bar> ubDom\<cdot>b1 \<union> ubDom\<cdot>b2"

abbreviation sbConc_abbr :: " 'm SB \<Rightarrow> 'm SB \<Rightarrow> 'm SB" ("(_ \<bullet> _)" [66,65] 65)
where "b1 \<bullet> b2 \<equiv> sbConc b1\<cdot>b2"
*)
    

  (* Concatination on common Channels in the 'm SB. *)
(* definition sbConcCommon:: " 'm stream ubundle \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbConcCommon b1 \<equiv> \<Lambda> b2. (b1 \<bullet> b2) \<bar>  sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2"*)

  (* Applies a (Stream-)function to all streams. *)
definition sbMapStream:: "('m stream \<Rightarrow> 'm stream) \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" where
"sbMapStream f b = Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>b) \<leadsto> f (b . c))"

  (* Retrieves the first n Elements of each Stream. *)
definition sbTake:: "nat \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbTake n \<equiv> \<Lambda> b . sbMapStream (\<lambda>s. stake n\<cdot>s) b"

  (* Retrieves the first Element of each Stream. *)
definition sbHd:: " 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbHd \<equiv> sbTake 1"

  (* Deletes the first n Elements of each Stream *)
definition sbDrop:: "nat \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbDrop n \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. sdrop n\<cdot>s) b"

  (* Deletes the first Elements of each stream *)
definition sbRt:: " 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbRt \<equiv> sbDrop 1"

  (* Retrieves the n-th element of each Stream *)
definition sbNth:: "nat \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbNth n \<equiv> \<Lambda> sb.  sbHd\<cdot>(sbDrop n\<cdot>sb)"

(* I tried to make this function cont, look at SBCase_Study *)
  (* Length of the selected stream. *)
definition sbLen:: " 'm stream ubundle \<rightarrow> lnat " (* ("#_") *)where
"sbLen \<equiv> \<Lambda> b. if ubDom\<cdot>b \<noteq> {} then LEAST ln. ln \<in> { #(b. c) | c. c \<in> ubDom\<cdot>b} else \<infinity>"  

  (* Iterates the streams n-times. *)
definition sbNTimes:: "nat \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" ("_\<star>_" [60,80] 90) where
"sbNTimes n b \<equiv> sbMapStream (sntimes n) b"

  (* Iterates the streams \<infinity>-times. *)
definition sbInfTimes:: " 'm stream ubundle \<Rightarrow> 'm stream ubundle" ("_\<infinity>") where
"sbInfTimes sb = sbMapStream sinftimes sb"

  (* Applies a (Element-)function to each stream. *)
definition sbMap:: "('m \<Rightarrow> 'm) \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbMap f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. smap f\<cdot>s) b"

  (* Applies a filter to all Elements in each stream. *)
definition sbFilter:: "'m set \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbFilter f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. sfilter f\<cdot>s) b "

abbreviation sbfilter_abbr :: "'m set \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" ("(_ \<ominus> _)" [66,65] 65)
where "F \<ominus> s \<equiv> sbFilter F\<cdot>s"

  (* Applies a filter to each stream. If the stream is not in the filter it is replaces by "None"  *)
definition sbFilterStreams:: "'m stream set \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" where
"sbFilterStreams f b \<equiv> Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>b \<and> (b. c)\<in>f) \<leadsto> (b .c) )"

  (* Applies the function to the first Element in each Streams and returns only the first Element *)
definition sbLookahd:: "('m \<Rightarrow> 'm) \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbLookahd f \<equiv> \<Lambda> sb. sbMap f\<cdot>(sbHd\<cdot>sb)"

  (* Prefix while predicate holds. *)
definition sbTakeWhile:: "('m \<Rightarrow> bool) \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbTakeWhile f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. stakewhile f\<cdot>s) b"

  (* Drop prefix while predicate holds. *)
definition sbDropWhile:: "('m \<Rightarrow> bool) \<Rightarrow> 'm stream ubundle \<rightarrow> 'm stream ubundle" where
"sbDropWhile f \<equiv> \<Lambda> b. sbMapStream (\<lambda>s. sdropwhile f\<cdot>s) b"

  (* Remove successive duplicate values from each stream. *)
definition sbRcdups:: "'m stream ubundle \<rightarrow> 'm stream ubundle" where
"sbRcdups \<equiv> \<Lambda> sb. sbMapStream (\<lambda>s. srcdups\<cdot>s) sb"

(* Ugly AF, schöner machen\<And>! *)
(* Ich kann nicht "fix" verwendne da 'm SB kein pcpo ist. 
  Statdessen verwende ich "(sbTake 0\<cdot>b)" als künstliches kleinstes element *)

(* primrec myiterate :: "nat \<Rightarrow> 'm stream ubundle set \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" where
    "myiterate 0 bs b = sbLeast (ubDom\<cdot>b)"
  | "myiterate (Suc n) bs b = (let rest = (myiterate n bs (sbRt\<cdot>b)) in
          if (sbHd\<cdot>b\<in>bs) then sbHd\<cdot>b \<bullet> rest else rest )"

  (* (if (sbHd\<cdot>b\<in>bs) then sbHd\<cdot>b \<bullet>(myiterate n bs (sbRt\<cdot>b)) else (myiterate n bs (sbRt\<cdot>b))) *)

definition sbFilterTupel:: " 'm stream ubundle set \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" where
"sbFilterTupel bs b \<equiv> \<Squnion>i. myiterate i bs b"

thm fix_def
definition sbFilterTupel2:: " 'm stream ubundle set \<Rightarrow> 'm stream ubundle \<Rightarrow> 'm stream ubundle" where
"sbFilterTupel2 A \<equiv> (\<Lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>(\<lambda>s. sbTake 0\<cdot>s))\<cdot>
      (\<Lambda> h. (\<lambda> b. if (sbHd\<cdot>b\<in>A) then sbHd\<cdot>b \<bullet> h (sbRt\<cdot>b) else h (sbRt\<cdot>b)))"*)
(* \<Squnion>i. iterate i\<cdot>(\<Lambda> f. (\<lambda>b. 
  if (b=sbLeast (sbDom\<cdot>b)) then sbLeast (sbDom\<cdot>b) else
    if (sbHd\<cdot>b\<in>bs) then (sbHd\<cdot>b) \<bullet> f (sbRt\<cdot>b) else f (sbRt\<cdot>b) ))\<cdot>(\<lambda>x. empty \<Omega>)"  *)

subsection \<open>Automaton\<close>

definition sbHdElem :: "'m stream ubundle \<rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"sbHdElem \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))" 

definition convDiscrUp :: "(channel \<rightharpoonup> 'm) \<Rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"convDiscrUp sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (Iup (Discr (sb \<rightharpoonup> c))))"

definition convSB :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm stream ubundle" where
"convSB sb \<equiv> Abs_ubundle (\<lambda>c. (c \<in> dom sb) \<leadsto> (lscons\<cdot>(sb \<rightharpoonup> c)\<cdot>\<epsilon>))"

(* ----------------------------------------------------------------------- *)
section \<open>Lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
(* ----------------------------------------------------------------------- *)
subsection \<open>General Lemmas\<close>
(* ----------------------------------------------------------------------- *)

(* Zwischenteil, wird später gebraucht *)
(* verwendet sbDom && sbGetCh *)

lemma [simp]: "Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto>b . c) = b"
  apply(rule ub_eq)
  using Collect_cong dom_def mem_Collect_eq apply auto[1]
  by auto

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbSetCh\<close>
(* ----------------------------------------------------------------------- *)

(* Welltyped is preserved after setting new sb_well channels.*)
lemma sbset_well [simp]: assumes "sdom\<cdot>s \<subseteq> ctype c"
  shows "ubWell ((Rep_ubundle b) (c \<mapsto> s) )"
  by (simp add: assms usOkay_stream_def)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRestrict\<close>
(* ----------------------------------------------------------------------- *)

lemma sbrestrict2sbgetch[simp]: assumes "c\<in>cs"
  shows "(b\<bar>cs) . c = b. c"
  by(simp add: assms ubgetch_insert ubrestrict_insert)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRemCh\<close>
(* ----------------------------------------------------------------------- *)

(* lemma sbremch_monofun[simp]: "monofun (\<lambda> b. \<Lambda> c.  b \<bar> -{c})"
  by (simp add: below_cfun_def monofun_cfun_arg fun_belowI monofunI)*)

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
(*lemma sbremch_cont1[simp]: assumes "chain Y"
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
by(rule contI2, auto)*)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbConc\<close>
(* ----------------------------------------------------------------------- *)
(*lemma sbconc_well[simp]: "sb_well (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>b2. c))) "
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
    using SB.cont_Abs_SB sbconc_well sbconct_cont1 by blast
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
*)
(* ----------------------------------------------------------------------- *)
  subsection \<open>sbConcCommon\<close>
(* ----------------------------------------------------------------------- *)
(*
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
*)
(* ----------------------------------------------------------------------- *)
  subsection \<open>sbMapStream\<close>
(* ----------------------------------------------------------------------- *)

lemma [simp]: assumes "\<forall>s. sdom\<cdot>(f s) \<subseteq> sdom\<cdot>s"
  shows "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
using assms by blast

lemma sbmapstream_cont2[simp]:  assumes "cont f" and "\<forall>s. sdom\<cdot>(f s)\<subseteq>sdom\<cdot>s"
  shows "cont (sbMapStream f)"
  sorry


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbTake\<close>
(* ----------------------------------------------------------------------- *)
lemma sbtake_cont [simp]:"cont (\<lambda>b. sbMapStream (\<lambda>s. stake n\<cdot>s) b)"
by (simp)

lemma sbtake_insert: "sbTake n\<cdot>b \<equiv>  sbMapStream (\<lambda>s. stake n\<cdot>s) b"
by(simp add: sbTake_def)

lemma sbtake_zero: "sbTake 0\<cdot>In = ubLeast (ubDom\<cdot>In)"
  by (simp add: sbtake_insert sbMapStream_def sbLeast_def)

lemma sbtake_sbdom[simp]: "ubDom\<cdot>(sbTake n\<cdot>b) = ubDom\<cdot>b"
  by (simp add: sbtake_insert)

lemma sbtake_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "sbTake n\<cdot>b . c = stake n\<cdot>(b .c)"
using assms by (simp add: sbtake_insert)

lemma sbtake_below [simp]: "sbTake n\<cdot>b \<sqsubseteq> sbTake (Suc n)\<cdot>b"
  by (metis eq_imp_le le_Suc_eq sbtake_sbdom sbtake_sbgetch stake_mono ub_below)

lemma sbtake_chain [simp]: "chain (\<lambda>n. sbTake n\<cdot>b)"
by (simp add: po_class.chainI)

lemma sbtake_lub_sbgetch: assumes "c\<in>ubDom\<cdot>b"
  shows "(\<Squnion>n. sbTake n\<cdot>b) . c = (\<Squnion>n. stake n\<cdot>(b . c))"
  by (metis (mono_tags, lifting)
      assms lub_eq ubrep_lub_eval po_class.chainI ubgetch_insert sbtake_below sbtake_sbgetch)

lemma sbtake_lub [simp]: "(\<Squnion>n. sbTake n\<cdot>b) = b" (is "?L = b")
proof(rule ub_eq)
  show "ubDom\<cdot>?L = ubDom\<cdot>b"
    by (metis po_class.chainI ubdom_chain_eq2 sbtake_below sbtake_sbdom)
  fix c
  assume "c\<in>ubDom\<cdot>?L"
  hence "c\<in>ubDom\<cdot>b" by (simp add: \<open>ubDom\<cdot>(\<Squnion>n. sbTake n\<cdot>b) = ubDom\<cdot>b\<close>)
  hence "?L . c = (\<Squnion>n. stake n\<cdot>(b . c))" using sbtake_lub_sbgetch by auto
  thus "?L .c = b .c"  by (simp add: reach_stream)
qed

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbHd\<close>
(* ----------------------------------------------------------------------- *)
lemma sbhd_sbdom[simp]: "ubDom\<cdot>(sbHd\<cdot>b) = ubDom\<cdot>b"
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

lemma sbdrop_sbdom[simp]: "ubDom\<cdot>(sbDrop n\<cdot>b) = ubDom\<cdot>b"
  sorry
  (*apply (simp add: sbdrop_insert)*)

lemma sbdrop_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "sbDrop n\<cdot>b . c = sdrop n\<cdot>(b .c)"
using assms by (simp add: sbdrop_insert)

(*lemma sbtake_sbdrop [simp]: "sbTake n\<cdot>b \<bullet> sbDrop n\<cdot>b = b" (is "?L = b")
proof(rule sb_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>b" by(simp)
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c\<in>sbDom\<cdot>b" by simp
  hence "c\<in>(sbDom\<cdot>(sbTake n\<cdot>b) \<inter> sbDom\<cdot>(sbDrop n\<cdot>b))" by simp
  hence "?L . c = (((sbTake n\<cdot>b) .c) \<bullet>  (sbDrop n\<cdot>b) . c)" using sbconc_sbgetch by blast
  hence "?L . c = (stake n\<cdot>(b . c)) \<bullet>  (sdrop n\<cdot>(b . c))" by (simp add: \<open>c \<in> sbDom\<cdot>b\<close>)
  thus "?L . c = b . c" by simp
qed*)


lemma sbdrop_plus [simp]: "sbDrop n\<cdot>(sbDrop k\<cdot>sb) = sbDrop (n+k)\<cdot>sb"
  apply(rule ub_eq)
  apply simp
  apply(simp add: sbDrop_def)
  by (metis iterate_iterate sbdrop_insert sbdrop_sbdom sbdrop_sbgetch sdrop_def)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRt\<close>
(* ----------------------------------------------------------------------- *)
lemma sbrt_sbdom[simp]: "ubDom\<cdot>(sbRt\<cdot>b) = ubDom\<cdot>b"
  by(simp add: sbRt_def)

(*lemma sbhd_sbrt [simp]: "(sbHd\<cdot>b \<bullet> sbRt\<cdot>b) = b"
 by (simp add: sbHd_def sbRt_def)
*)

(* ----------------------------------------------------------------------- *)
  subsection \<open>snNtimes\<close>
(* ----------------------------------------------------------------------- *)

lemma sbntimes_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "(n\<star>b) . c = sntimes n (b . c)"
  using assms by (smt
    domIff option.sel sbMapStream_def sbNTimes_def sntimes_sdom1 subset_trans ubWell_def
    ubdom_channel_usokay ubgetch_insert ubgetch_ubrep_eq usOkay_stream_def)

lemma sbntimes_zero [simp]: "0\<star>b = ubLeast (ubDom\<cdot>b)" 
  by (simp add: sbNTimes_def sbMapStream_def sntimes_def sbLeast_def)

lemma sbntimes_one [simp]: fixes b:: "'m stream ubundle" shows "1\<star>b = b" 
  by (simp add: sbNTimes_def sbMapStream_def sntimes_def ubLeast_def)

lemma sbntimes_sbdom [simp]: "ubDom\<cdot>(i\<star>b) = ubDom\<cdot>b"
  by(simp add: sbNTimes_def)

lemma sbntimes_below [simp]: fixes b:: "'m stream ubundle"
  shows "(i\<star>b) \<sqsubseteq> (Suc i)\<star>b" (is "?L \<sqsubseteq> ?R")
proof(rule ub_below)
  show "ubDom\<cdot>?L = ubDom\<cdot>?R" by simp
  fix c
  assume "c\<in>ubDom\<cdot>?L"
  hence "c\<in>ubDom\<cdot>b" by simp
  thus "?L . c \<sqsubseteq> ?R . c" using sntimes_leq by auto 
qed

lemma sbntimes_chain[simp]: fixes b:: "'m stream ubundle"
  shows "chain (\<lambda>i. i\<star>b)"
by (simp add: po_class.chainI)

lemma sbntimes2sinftimes: assumes "chain Y" and "c\<in>ubDom\<cdot>b"
  shows "(\<Squnion>i. i\<star>b) . c = sinftimes (b . c)"
proof -
  have "(\<Squnion>i. i\<star>b) . c = (\<Squnion>i. (i\<star>b) . c)" by (simp add: contlub_cfun_arg contlub_cfun_fun)
  hence "(\<Squnion>i. i\<star>b) . c = (\<Squnion> i. sntimes i (b . c))" using assms(2) by auto
  thus ?thesis by (simp add: sntimesLub) 
qed

(* ----------------------------------------------------------------------- *)
  subsection \<open>snInfTimes\<close>
(* ----------------------------------------------------------------------- *)

lemma sbinftimes_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "(sbInfTimes b) . c = sinftimes (b . c)"
using assms by (simp add: sbInfTimes_def)

lemma sbinftimes_sbdom [simp]: "ubDom\<cdot>(b\<infinity>) = ubDom\<cdot>b"
  by (simp add: sbInfTimes_def)

lemma sntimes_lub: fixes b:: "'m stream ubundle"
  shows "(\<Squnion>i. i\<star>b) = b\<infinity>" (is "?L = ?R")
proof (rule ub_eq)
  have "ubDom\<cdot>?L = ubDom\<cdot>b" by (metis po_class.chainI ubdom_chain_eq2 sbntimes_below sbntimes_sbdom)
  thus "ubDom\<cdot>?L = ubDom\<cdot>?R" by simp

  fix c
  assume "c\<in>ubDom\<cdot>?L"
  hence "c\<in>ubDom\<cdot>b" using ubdom_chain_eq2 sbntimes_chain sbntimes_sbdom by blast 
  hence "\<And>c. c \<in> ubDom\<cdot>b \<Longrightarrow> (\<Squnion>i. i\<star>b) . c = b\<infinity> . c" by (metis (full_types) sbinftimes_sbgetch sbntimes2sinftimes sbntimes_chain)
  hence "(\<Squnion>i. i\<star>b) . c = (\<Squnion>i. i\<star>(b . c))" by (simp add: \<open>c \<in> ubDom\<cdot>(\<Squnion>i. i\<star>b)\<close> \<open>c \<in> ubDom\<cdot>b\<close> sntimesLub)
  thus "?L . c = ?R . c" using \<open>c \<in> ubDom\<cdot>b\<close> sntimesLub by force 
qed

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbMap\<close>
(* ----------------------------------------------------------------------- *)
lemma assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>((\<lambda>s. smap f\<cdot>s) s)\<subseteq>(ctype c))"
  shows "ubDom\<cdot>(sbMap f\<cdot>b) = ubDom\<cdot>b"
  by (simp add: sbMap_def assms)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbFilter\<close>
(* ----------------------------------------------------------------------- *)
lemma sbfilter_sbdom [simp]: "ubDom\<cdot>(sbFilter A\<cdot>b) = ubDom\<cdot>b"
by (smt Abs_cfun_inverse2 cont_Rep_cfun2 sbFilter_def sbfilter_sbdom ubmapstream_cont sbmapstream_dom subsetCE subsetI)

lemma sbfilter_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows  "(sbFilter A\<cdot>b) . c = sfilter A\<cdot>(b .c)"
  apply(simp add: sbFilter_def assms)
by (meson Streams.sbfilter_sbdom assms ubmapstream_ubgetch subsetCE subsetI)

(* ----------------------------------------------------------------------- *)
  (* Lemma *)
(* ----------------------------------------------------------------------- *)

lemma if_then_dom[simp]: "dom (\<lambda>c. (c \<in> cs)\<leadsto>b .c) = cs"
using dom_def by fastforce

lemma if_then_well[simp]: assumes "cs\<subseteq>ubDom\<cdot>b" shows "ubWell (\<lambda>c. (c\<in>cs) \<leadsto> (b .c))"
using assms apply(simp add: ubWell_def ubgetch_insert ubdom_insert)
using ubrep_well ubWell_def by blast

lemma if_then_chain[simp]: assumes "chain Y" and "monofun g"
  shows "chain (\<lambda>i. (sbDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
proof(cases "sbDom\<cdot>(Y 0) = In")
  case True 
  hence "\<forall>i. (sbDom\<cdot>(Y i) = In)" using assms(1) ubdom_chain_eq3 by blast
  thus ?thesis
    by (smt assms(1) assms(2) below_option_def monofunE option.sel option.simps(3) po_class.chain_def)
next
  case False
  hence "\<forall>i. (sbDom\<cdot>(Y i) \<noteq> In)" using assms(1) ubdom_chain_eq3 by blast
  thus ?thesis by (auto) 
qed

lemma if_then_mono [simp]:  assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
proof(rule monofunI)
  fix x y :: "'a stream ubundle"
  assume "x\<sqsubseteq>y"
  hence "ubDom\<cdot>x = ubDom\<cdot>y" using ubdom_eq by blast 
  thus "(sbDom\<cdot>x = In)\<leadsto>g x \<sqsubseteq> (sbDom\<cdot>y = In)\<leadsto>g y" by (smt \<open>(x::'a SB) \<sqsubseteq> (y::'a SB)\<close> assms monofunE po_eq_conv some_below) 
qed

lemma if_then_cont [simp]: assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
proof(rule contI2)
  show "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)" using assms cont2mono if_then_mono by blast 
  thus " \<forall>Y. chain Y \<longrightarrow> (ubDom\<cdot>(\<Squnion>i. Y i) = In)\<leadsto>g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
    by (smt Abs_cfun_inverse2 assms if_then_lub lub_chain_maxelem lub_eq po_eq_conv ubdom_chain_eq2)
qed

lemma if_then_sbDom: assumes "d \<in> dom (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>(F b))"
  shows "ubDom\<cdot>d = In"
by (smt assms domIff)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbLen\<close>
(* ----------------------------------------------------------------------- *)  

lemma sbLen_set_below: assumes "\<forall>b\<in>{(y . c) |c. c \<in> ubDom\<cdot>y}. \<exists>a\<in>{(x . c) |c. c \<in> ubDom\<cdot>x}. (#a) \<sqsubseteq> (#b)"
  shows "\<forall>b\<in>{#(y . c) |c. c \<in> ubDom\<cdot>y}. \<exists>a\<in>{#(x . c) |c. c \<in> ubDom\<cdot>x}. a \<sqsubseteq> b"
    using assms by fastforce

lemma sbLen_below: assumes "a \<sqsubseteq> b" shows "\<forall>c\<in>ubDom\<cdot>a. #(a. c) \<le> #(b . c)"   
by (simp add: assms mono_slen monofun_cfun_arg monofun_cfun_fun)

lemma lnat_set_least_below_sb: assumes "(A :: lnat set) \<noteq> {}" and "(B :: lnat set) \<noteq> {}"
  and "\<forall> a \<in> A . \<exists> b \<in> B.  a \<sqsubseteq> b" and "\<forall> b \<in> B. \<exists> a \<in> A. a \<sqsubseteq> b"
shows "(LEAST ln. ln \<in> A) \<sqsubseteq> (LEAST ln. ln \<in> B)"
  by (metis (no_types, lifting) LeastI Least_le all_not_in_conv assms(2) assms(4) lnle_conv rev_below_trans)  
  
lemma sbLen_mono_pre: assumes "x \<sqsubseteq> y" shows 
  "(if ubDom\<cdot>x \<noteq> {} then LEAST ln. ln \<in> { #(x. c) | c. c \<in> ubDom\<cdot>x} else \<infinity>) \<sqsubseteq>
   (if ubDom\<cdot>y \<noteq> {} then LEAST ln. ln \<in> { #(y. c) | c. c \<in> ubDom\<cdot>y} else \<infinity>)" 
proof(cases "ubDom\<cdot>x \<noteq> {}")
  case True
  have f1: "ubDom\<cdot>y = ubDom\<cdot>x"
    using assms ubdom_below by blast
  have f2: "\<forall>b\<in>{(y . c) |c. c \<in> ubDom\<cdot>y}. \<exists>a\<in>{(x . c) |c. c \<in> ubDom\<cdot>x}. (a) \<sqsubseteq> (b) 
          \<Longrightarrow> \<forall>b\<in>{(y . c) |c. c \<in> ubDom\<cdot>y}. \<exists>a\<in>{(x . c) |c. c \<in> ubDom\<cdot>x}. (#a) \<sqsubseteq> (#b)"
    by (meson monofun_cfun_arg)
  have f3: "(LEAST ln. ln \<in> {#(x . c) |c. c \<in> ubDom\<cdot>x}) \<sqsubseteq> (LEAST ln. ln \<in> {#(y . c) |c. c \<in> ubDom\<cdot>y})"
    apply (rule lnat_set_least_below_sb)
    apply (simp add: True)
    apply (simp add: True f1)
    using assms f1 sbLen_below apply fastforce
    using assms f1 sbLen_below by fastforce
  show ?thesis
    using f1 f3 by auto
next
  case False
  have f1: "ubDom\<cdot>y = ubDom\<cdot>x"
    using assms ubdom_below by blast
  then show ?thesis 
    by(simp add: False)
qed
 
lemma sbLen_mono[simp]: "monofun (\<lambda> b. if ubDom\<cdot>b \<noteq> {} then LEAST ln. ln \<in> { #(b. c) | c. c \<in> ubDom\<cdot>b} else \<infinity>)"
  using monofun_def sbLen_mono_pre by blast  

lemma sbLen_chain: assumes "chain Y" and "\<And> i. ubDom\<cdot>(Y i) \<noteq> {}" shows 
  "chain (\<lambda> i. if ubDom\<cdot>(Y i) \<noteq> {} then LEAST ln. ln \<in> { #((Y i). c) | c. c \<in> ubDom\<cdot>(Y i)} else \<infinity>)"
  apply(simp only: chain_def)
  apply(subst sbLen_mono_pre)
  using assms(1) po_class.chainE apply auto[1]
  by auto

lemma sbLen_conv: "(LEAST ln. \<exists>c. ln = #(sb . c) \<and> c \<in> ubDom\<cdot>sb) = (LEAST ln. ln \<in> { #(sb . c) | c. c \<in> ubDom\<cdot>sb})"
  by auto
    
lemma sbLen_chain2: assumes "chain Y" and "\<And> i. ubDom\<cdot>(Y i) \<noteq> {}" shows
  "chain (\<lambda> i. (LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i)))"
proof - 
  fix i
  have f1: "\<forall>i. (LEAST ln. ln \<in> {#(Y i . c) |c. c \<in> ubDom\<cdot>(Y i)}) \<sqsubseteq> (LEAST ln. ln \<in> {#(Y (Suc i) . c) |c. c \<in> ubDom\<cdot>(Y (Suc i))})"
  proof
    fix i
    show "(LEAST ln. ln \<in> {#(Y i . c) |c. c \<in> ubDom\<cdot>(Y i)}) \<sqsubseteq> (LEAST ln. ln \<in> {#(Y (Suc i) . c) |c. c \<in> ubDom\<cdot>(Y (Suc i))})"
      apply (rule lnat_set_least_below_sb)  
      using assms(2) apply auto[1]
      using assms(2) apply auto[1]
      using assms(1) po_class.chainE sbLen_below ubdom_eq apply fastforce
      using assms(1) po_class.chainE sbLen_below ubdom_eq by fastforce
  qed
  show ?thesis
    apply(subst sbLen_conv)
    apply(simp only: chain_def)
    using f1 by auto
qed

lemma chains_lub_eq_sb: assumes "chain (Y::nat \<Rightarrow> lnat)" and "chain (X::nat \<Rightarrow> lnat)" and "\<exists> i. \<forall> j\<ge>i. Y j = X j" shows "(\<Squnion>i. Y i) = (\<Squnion>i. X i)"
proof - 
  have "(\<Squnion>i. Y i) \<le> (\<Squnion>i. X i)"
  proof - 
    obtain i where f1: "\<forall> j\<ge>i. Y j = X j"
      using assms by blast
    have "\<And> j. (X j) \<le> (\<Squnion>i. X i)" 
      using assms(2) is_ub_thelub lnle_def by blast
    then have "\<forall> j\<ge>i. (Y j) \<le> (\<Squnion>i. X i)"
      by (simp add: f1)
    then show ?thesis
    proof -
      have f1: "\<forall>n na f l. (\<not> (n::nat) \<le> na \<or> \<not> f na \<le> (l::lnat) \<or> (\<exists>n na. n \<le> na \<and> \<not> f n \<le> f na)) \<or> f n \<le> l"
        by (meson order_subst2)
      obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" and nna :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
        f2: "\<forall>x1. (\<exists>v4 v5. v4 \<le> v5 \<and> \<not> x1 v4 \<le> x1 v5) = (nn x1 \<le> nna x1 \<and> \<not> x1 (nn x1) \<le> x1 (nna x1))"
        by moura
      have f3: "\<forall>n. \<not> i \<le> n \<or> Y n \<le> Lub X"
        by (metis \<open>\<forall>j\<ge>i. Y j \<le> (\<Squnion>i. X i)\<close>)
      then have f4: "Y i \<le> Lub X"
        by (metis nat_le_linear)
      obtain nnb :: "lnat \<Rightarrow> (nat \<Rightarrow> lnat) \<Rightarrow> nat" where
        f5: "\<forall>f l. (\<not> chain f \<or> f (nnb l f) \<notsqsubseteq> l) \<or> Lub f \<sqsubseteq> l"
        by (meson lub_below)
      have "\<not> nn Y \<le> nna Y \<or> Y (nn Y) \<le> Y (nna Y)"
        by (meson assms(1) lnle_conv po_class.chain_mono)
      then show ?thesis
        using f5 f4 f3 f2 f1 by (metis (full_types) assms(1) lnle_conv nat_le_linear)
    qed
  qed  
  moreover have "(\<Squnion>i. X i) \<le> (\<Squnion>i. Y i)"
  proof -   
    obtain i where f1: "\<forall> j\<ge>i. X j = Y j"
      using assms(3) by fastforce
    have "\<And> j. (Y j) \<le> (\<Squnion>i. Y i)" 
      using assms(1) is_ub_thelub lnle_def by blast
    then have "\<forall> j\<ge>i. (X j) \<le> (\<Squnion>i. Y i)"
      by (simp add: f1)
    then show ?thesis
    proof -
      have f1: "\<forall>n na f l. (\<not> (n::nat) \<le> na \<or> \<not> f na \<le> (l::lnat) \<or> (\<exists>n na. n \<le> na \<and> \<not> f n \<le> f na)) \<or> f n \<le> l"
        by (meson order_subst2)
      obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" and nna :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
        f2: "\<forall>x1. (\<exists>v4 v5. v4 \<le> v5 \<and> \<not> x1 v4 \<le> x1 v5) = (nn x1 \<le> nna x1 \<and> \<not> x1 (nn x1) \<le> x1 (nna x1))"
        by moura
      have f3: "\<forall>n. \<not> i \<le> n \<or> X n \<le> Lub Y"
        by (meson \<open>\<forall>j\<ge>i. X j \<le> (\<Squnion>i. Y i)\<close>)
      then have f4: "X i \<le> Lub Y"
        by (meson nat_le_linear)
      obtain nnb :: "lnat \<Rightarrow> (nat \<Rightarrow> lnat) \<Rightarrow> nat" where
          f5: "\<forall>f l. (\<not> chain f \<or> f (nnb l f) \<notsqsubseteq> l) \<or> Lub f \<sqsubseteq> l"
        by (meson lub_below)
      have "\<not> nn X \<le> nna X \<or> X (nn X) \<le> X (nna X)"
        by (metis assms(2) lnle_conv po_class.chain_mono)
      then show ?thesis
        using f5 f4 f3 f2 f1 by (metis (full_types) assms(2) lnle_conv nat_le_linear)
    qed
  qed    
  ultimately show ?thesis
    using order_trans by auto
qed   

lemma chain_mono_sb: assumes "chain (Y::nat \<Rightarrow> lnat)" and "\<exists> i. \<forall> j\<ge>i. (Y i \<ge> Y j)" shows "\<exists> i. \<forall> j\<ge>i. (Y i = Y j)"
  by (meson assms(1) assms(2) dual_order.antisym lnle_def po_class.chain_mono)  
  
lemma sbLen_cont_pre: assumes "chain Y" and "finite (ubDom\<cdot>(Lub Y))" shows 
  "(if ubDom\<cdot>(\<Squnion>i. Y i) \<noteq> {} then LEAST ln. ln \<in> { #((\<Squnion>i. Y i). c) | c. c \<in> ubDom\<cdot>(\<Squnion>i. Y i)} else \<infinity>) \<sqsubseteq>
   (\<Squnion>i. if ubDom\<cdot>(Y i) \<noteq> {} then LEAST ln. ln \<in> { #((Y i). c) | c. c \<in> ubDom\<cdot>(Y i)} else \<infinity>)"
proof (cases "ubDom\<cdot>(\<Squnion>i. Y i) \<noteq> {}")
  case True
  hence f1: "\<forall> i. ubDom\<cdot>(Y i) = ubDom\<cdot>(\<Squnion>i. Y i)"
    using assms(1) ubdom_chain_eq2 by auto
  hence f10: "\<forall> i. ubDom\<cdot>(\<Squnion>i. Y i) =  ubDom\<cdot>(Y i)"
    by simp
  hence f11: "\<forall> i. ubDom\<cdot>(Y i) \<noteq> {}"
    using True by auto
  show ?thesis 
    apply(simp only: True f11)
    apply(auto)
    proof (cases "finite_chain Y")
      case True
      obtain maxI where f21: "max_in_chain maxI Y"
        using True finite_chain_def by auto
      have f22: "\<forall>j. maxI \<le> j \<longrightarrow> (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI)) = (LEAST ln. \<exists>c. ln = #(Y j . c) \<and> c \<in> ubDom\<cdot>(Y j))"
      proof -
        { fix nn :: nat
          { assume "Y nn \<noteq> Y maxI"
            then have "\<not> maxI \<le> nn \<or> (LEAST l. \<exists>c. l = #(Y nn . c) \<and> c \<in> ubDom\<cdot>(Y nn)) = (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI))"
              by (metis f21 max_in_chain_def) }
          then have "\<not> maxI \<le> nn \<or> (LEAST l. \<exists>c. l = #(Y nn . c) \<and> c \<in> ubDom\<cdot>(Y nn)) = (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI))"
            by fastforce }
        then show ?thesis
          by presburger
      qed
      have f221: "max_in_chain maxI (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i))"
        by (simp add: f22 max_in_chainI)
      have f23: "(\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i)) = (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI))"
        using maxinch_is_thelub assms(1) sbLen_chain2 f221 f11 by fastforce
      show "(LEAST ln. \<exists>c. ln = #(Lub Y . c) \<and> c \<in> ubDom\<cdot>(Lub Y)) \<le> (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i))" 
        using assms(1) f21 f23 maxinch_is_thelub sorry (*by fastforce*)
    next
      case False 
      then show"(LEAST ln. \<exists>c. ln = #(Lub Y . c) \<and> c \<in> ubDom\<cdot>(Lub Y)) \<le> (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i))"
      proof(cases "finite_chain (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i))")
        case True
        then have f31: "\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i))"
          using finite_chain_def by auto    
        then obtain maxI where f32: "\<forall>j. maxI \<le> j \<longrightarrow> (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI)) = (LEAST ln. \<exists>c. ln = #(Y j . c) \<and> c \<in> ubDom\<cdot>(Y j))"
          by (meson max_in_chain_def)
        then obtain maxCount where f33: "maxCount = (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI))"
          by blast
        then have f34: "maxCount = (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> ubDom\<cdot>(Y i))"
          by (metis (mono_tags, lifting) True f32 finite_chainE l42 le_cases max_in_chainI3 max_in_chain_def)
        have f35: "finite (ubDom\<cdot>(Lub Y))"  
          using assms by blast    
        have f36: "\<exists> maxCh \<in> ubDom\<cdot>(Lub Y). \<forall>j\<ge>maxI. maxCount = #(Y j . maxCh)"
        proof(rule ccontr)
          assume "\<not>?thesis"
          then have f361: "\<forall> ch1 \<in> ubDom\<cdot>(Lub Y). \<exists>j\<ge>maxI. maxCount < #(Y j . ch1)"
          proof -
            obtain nn :: "channel \<Rightarrow> nat" where
              f1: "\<forall>c. c \<notin> ubDom\<cdot>(Lub Y) \<or> maxI \<le> nn c \<and> maxCount \<noteq> #(Y (nn c) . c)"
              using \<open>\<not> (\<exists>maxCh\<in>ubDom\<cdot>(Lub Y). \<forall>j\<ge>maxI. maxCount = #(Y j . maxCh))\<close> by moura
            obtain cc :: channel where
              "(\<exists>v0. v0 \<in> ubDom\<cdot>(Lub Y) \<and> (\<forall>v1. \<not> maxI \<le> v1 \<or> \<not> maxCount < #(Y v1 . v0))) = (cc \<in> ubDom\<cdot>(Lub Y) \<and> (\<forall>v1. \<not> maxI \<le> v1 \<or> \<not> maxCount < #(Y v1 . cc)))"
              by blast
            moreover
            { assume "cc \<in> ubDom\<cdot>(Y (nn cc))"
              then have "\<not> #(Y (nn cc) . cc) < (LEAST l. \<exists>c. l = #(Y (nn cc) . c) \<and> c \<in> ubDom\<cdot>(Y (nn cc)))"
                using not_less_Least by blast
              moreover
              { assume "\<not> #(Y (nn cc) . cc) < (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI))"
                moreover
                { assume "\<not> #(Y (nn cc) . cc) < (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI)) \<and> \<not> (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> ubDom\<cdot>(Y maxI)) < #(Y (nn cc) . cc)"
                  then have "cc \<notin> ubDom\<cdot>(Lub Y)"
                    using f1 f33 neq_iff by blast }
                ultimately have "cc \<in> ubDom\<cdot>(Lub Y) \<longrightarrow> (cc \<notin> ubDom\<cdot>(Lub Y) \<or> (\<exists>n\<ge>maxI. maxCount < #(Y n . cc))) \<or> \<not> maxI \<le> nn cc \<or> maxCount = #(Y (nn cc) . cc)"
                  using f33 by blast }
              ultimately have "cc \<in> ubDom\<cdot>(Lub Y) \<longrightarrow> (cc \<notin> ubDom\<cdot>(Lub Y) \<or> (\<exists>n\<ge>maxI. maxCount < #(Y n . cc))) \<or> \<not> maxI \<le> nn cc \<or> maxCount = #(Y (nn cc) . cc)"
                using f32 by presburger
              then have "cc \<in> ubDom\<cdot>(Lub Y) \<longrightarrow> cc \<notin> ubDom\<cdot>(Lub Y) \<or> (\<exists>n\<ge>maxI. maxCount < #(Y n . cc))"
                using f1 by blast }
            ultimately show ?thesis
              using assms(1) ubdom_chain_eq2 by blast
          qed
          show "False" 
          proof(cases "card (ubDom\<cdot>(Lub Y))")
            case 0
            then show ?thesis 
              using f10 f11 f35 by auto
          next
            case (Suc nat)
            then have i1: "card (ubDom\<cdot>(Lub Y)) = Suc nat"
              by blast
            show ?thesis
            proof - 
              obtain n where i2: "card (ubDom\<cdot>(Lub Y)) = n"
                by blast
              then have i3: "n > 0"    
                by (simp add: i1) 
                 
              obtain f where i4: "ubDom\<cdot>(Lub Y) = f ` {i::nat. i < n}"
                by (metis card_Collect_less_nat card_image f35 finite_imp_nat_seg_image_inj_on i2)   
              then have i5: "\<forall>i<n. \<exists>j\<ge>maxI. maxCount < #(Y j . (f i))"
                using f361 by blast

              then obtain x where i6: "x = Max {(LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) | i::nat. i < n}"
                by blast
              have i7: "\<forall>i<n. \<exists>m. (m = (LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) \<and> m\<ge>maxI \<and> (maxCount < #(Y m . (f i))))"    
                by (metis (no_types, lifting) LeastI i5)
              have i0: "ubDom\<cdot>(Lub Y) = ubDom\<cdot>(Y x)"    
                by (simp add: assms(1) ubdom_chain_eq2)  
              have i01: "\<forall>i<n. maxCount < #(Y x . f i)"
              proof -
                have i010: "\<forall>i<n. maxCount < #(Y (LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) . f i)"
                  using i7 by blast
                moreover have i011: "\<forall>i<n. (LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) \<le> x"
                proof - 
                  obtain g where "g = (\<lambda>i. (LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))))"
                    by blast
                  then have "g ` {i::nat. i < n} = {(LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) | i::nat. i < n}"
                    by blast
                  then have "finite {(LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) | i::nat. i < n}"
                    using nat_seg_image_imp_finite by auto
                  then show ?thesis
                    using Max_ge i6 by blast
                qed
                ultimately show ?thesis
                proof - 
                  have "\<forall>i<n. #(Y (LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) . f i) \<le> #(Y x . (f i))"
                    by (simp add: assms(1) i011 mono_slen monofun_cfun_arg monofun_cfun_fun po_class.chain_mono)
                  then show ?thesis
                    using i010 less_le_trans by blast
                qed
              qed
              then have i02: "\<forall>ch1\<in>ubDom\<cdot>(Lub Y). maxCount < #(Y x . ch1)"
                by (simp add: i4)
              then have i8: "maxCount < (LEAST ln. \<exists>c. ln = #(Y x  .  c) \<and> c \<in> ubDom\<cdot>(Y x))"
              proof - 
                have "ubDom\<cdot>(Y x) \<noteq> {}"
                  using f11 by auto
                then have "\<exists>ch1\<in>ubDom\<cdot>(Y x). (LEAST ln. \<exists>c. ln = #(Y x  .  c) \<and> c \<in> ubDom\<cdot>(Y x)) = #(Y x . ch1)"
                  by (smt Collect_empty_eq LeastI all_not_in_conv assms(1) f11 f33 ubchain_dom_eq)
                then show ?thesis
                  using i0 i02 by auto
              qed
              then have i9: "maxCount < (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i))"
              proof -
                have "\<exists>l. l \<sqsubseteq> (\<Squnion>n. LEAST l. \<exists>c. l = #(Y n . c) \<and> c \<in> ubDom\<cdot>(Y n)) \<and> maxCount < l"
                  using True finite_chain_def i8 is_ub_thelub by blast
                then show ?thesis
                  using less_le_trans lnle_def by blast
              qed
              then show ?thesis
                using f34 by auto
            qed  
          qed
        qed
        then obtain maxCh where f37: "maxCh \<in> ubDom\<cdot>(Lub Y) \<and> (\<forall>j\<ge>maxI. maxCount = #(Y j . maxCh))"
          by blast
        then have f38: "\<forall>j\<ge>maxI. #(Y j . maxCh) = (LEAST ln. \<exists>c. ln = # (Y j . c) \<and> c \<in> ubDom\<cdot>(Y j))"
          by (simp add: f32 f33)
        have f39: "maxCh \<in> ubDom\<cdot>(Lub Y) \<and> (\<forall> j. \<forall> ch2 \<in> ubDom\<cdot>(Lub Y). (maxI \<le> j) \<longrightarrow> ((#(Y j . maxCh)) \<sqsubseteq> (#(Y j .  ch2))))"    
          by (smt Least_le assms(1) f37 f38 lnle_conv ubdom_chain_eq2)     
        have f40: "(\<Squnion>i. LEAST ln. \<exists>c. ln = # (Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i)) = (\<Squnion>i.  (# (Y i  .  maxCh)))"
          apply(subst chains_lub_eq_sb, simp_all)
          using True finite_chain_def apply auto[1]
           apply (simp add: assms(1))
            using f38 by fastforce
        show ?thesis 
          apply(subst f40)
        proof -
          have f1: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'a stream)::lnat) = (\<Squnion>n. c\<cdot>(f n))"
            using contlub_cfun_arg by blast
          have f2: "ubGetCh\<cdot>(Lub Y) = (\<Squnion>n. ubGetCh\<cdot>(Y n))"
            using assms(1) contlub_cfun_arg by blast
          have "\<forall>f c. \<not> chain f \<or> (Lub f\<cdot>(c::channel)::'a stream) = (\<Squnion>n. f n\<cdot>c)"
            using contlub_cfun_fun by blast
          then have "(\<Squnion>n. #(Y n . maxCh)) = #(Lub Y . maxCh)"
            using f2 f1 by (simp add: assms(1))
          then have "\<exists>c. (\<Squnion>n. #(Y n . maxCh)) = #(Lub Y . c) \<and> c \<in> ubDom\<cdot>(Lub Y)"
            by (meson f37)
          then show "(LEAST l. \<exists>c. l = #(Lub Y . c) \<and> c \<in> ubDom\<cdot>(Lub Y)) \<le> (\<Squnion>n. #(Y n . maxCh))"
            by (simp add: Least_le)
        qed
      next
        case False
        then have f41: "\<not>(\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i)))"
          using assms(1) f11 finite_chain_def sbLen_chain2 by auto
        have f42: "\<forall>i. \<exists>j\<ge>i. (LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i)) < (LEAST ln. \<exists>c. ln = #(Y j  .  c) \<and> c \<in> ubDom\<cdot>(Y j))"
        proof(rule ccontr)
          assume a0: "\<not>?thesis"
          then have "\<exists>i. \<forall>j\<ge>i. (LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i)) = ( LEAST ln. \<exists>c. ln = #(Y j  .  c) \<and> c \<in> ubDom\<cdot>(Y j))"
          proof - 
            have "chain (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i))"
              by (simp add: assms(1) f11 sbLen_chain2)
            thus ?thesis
              using  a0 chain_mono_sb by fastforce
          qed
          then have "\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i))" 
            by (meson max_in_chainI)
          then show "False" 
            using f41 by blast
        qed      
        then have "(\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> ubDom\<cdot>(Y i)) = \<infinity>"
          using False assms(1) f11 sbLen_chain2 unique_inf_lub by blast
        then show ?thesis 
          by simp
      qed  
    qed 
next
  case False
  have f0: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> ubDom\<cdot>y = ubDom\<cdot>x"
    using ubdom_below by blast
  show ?thesis 
    using False assms(1) ubdom_chain_eq2 by fastforce
qed

lemma sbLen_cont[simp]: "cont (\<lambda> b. if ubDom\<cdot>b \<noteq> {} then LEAST ln. ln \<in> { #(b. c) | c. c \<in> ubDom\<cdot>b} else \<infinity>)"  
proof - 
  have f1: "\<forall>sb. finite (ubDom\<cdot>sb)"
    sorry
  show ?thesis
    apply (rule contI2)
    apply simp
    using f1 sbLen_cont_pre by blast
qed

  
(* ----------------------------------------------------------------------- *)
  subsection \<open>sbHdElem\<close>
(* ----------------------------------------------------------------------- *)    

lemma sbHdElem_mono: "monofun (\<lambda> sb::'a stream ubundle. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
proof(rule monofunI) 
  fix x y ::"'a stream ubundle"
  assume "x \<sqsubseteq> y"
  then show "(\<lambda> sb::'a stream ubundle. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) x \<sqsubseteq> (\<lambda> sb::'a stream ubundle. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) y"
    by (smt below_refl fun_below_iff monofun_cfun_arg some_below ubdom_below)
qed  
  
lemma sbHdElem_cont_pre: assumes "chain Y" shows "(\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> ubDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)))"
proof - 
  fix c
  have "(\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) c \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> ubDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)) c)"
  proof(cases "c \<in> ubDom\<cdot>(\<Squnion>i. Y i)")
    case True
    have f1: "\<And>i. ubDom\<cdot>(\<Squnion>i. Y i) =  ubDom\<cdot>(Y i)"
      by (simp add: assms ubdom_chain_eq2)
    then show ?thesis 
      apply(simp add: True)
    proof -
      have "Some (lshd\<cdot>(\<Squnion>n. Y n . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (metis assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR if_then_lub)
      then show "Some (lshd\<cdot>(Lub Y . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        using True assms ubgetch_lub by fastforce
    qed
  next
    case False
    then show ?thesis 
      using assms ubdom_chain_eq2 by fastforce
  qed  
  then show ?thesis
    by (smt assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun fun_below_iff if_then_lub is_ub_thelub lub_eq lub_fun monofun_cfun_arg monofun_cfun_fun po_class.chain_def po_eq_conv ubdom_chain_eq2 some_below)
qed  
 
lemma sbHdElem_cont: "cont (\<lambda> sb::'a stream ubundle. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
  apply(rule contI2)
  apply (simp add: sbHdElem_mono)
  using sbHdElem_cont_pre by blast

end


