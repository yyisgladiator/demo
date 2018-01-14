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
   apply(simp add: usOkay_stream_def)
  apply (metis IntE sdom_sfilter subsetI)
  apply (rule admI)
  by (simp add: usOkay_stream_def l44)

end

instantiation stream :: (message) uscl_pcpo
begin
instance
  apply intro_classes
  sorry
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
  subsection \<open>sbMapStream\<close>
(* ----------------------------------------------------------------------- *)

lemma [simp]: assumes "\<forall>s. sdom\<cdot>(f s) \<subseteq> sdom\<cdot>s"
  shows "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
using assms by blast

lemma sbmapstream_well[simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto>f (b. c))"
  by (smt assms domIff option.sel ubWell_def ubdom_channel_usokay ubgetch_insert usOkay_stream_def)

lemma sbmapstream_dom [simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "ubDom\<cdot>(sbMapStream f b) = ubDom\<cdot>b"
proof -
  have "\<forall>f u. (\<exists>c s. usOkay c (s::'a stream) \<and> \<not> usOkay c (f s)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    using ubMapStream_ubDom by blast
  then obtain cc :: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> channel" and ss :: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> 'a stream" where
    f1: "\<forall>f u. usOkay (cc f) (ss f) \<and> \<not> usOkay (cc f) (f (ss f)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    by moura
  have "ubMapStream f b = sbMapStream f b"
    by (simp add: sbMapStream_def ubMapStream_def)
  then show ?thesis
    using f1 by (metis (no_types) assms usOkay_stream_def)
qed

lemma sbmapstream_sbgetch [simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  and "c\<in>ubDom\<cdot>b"
shows "(sbMapStream f b) . c = f (b . c)"
  by (simp add: assms(1) assms(2) sbMapStream_def ubgetch_insert)

(* for any continuous function f from stream to stream which preserves the well-typed property,
   (sbMapStream f) is also continuous *)
lemma sbmapstream_cont [simp]: assumes "cont f" and "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "cont (sbMapStream f)"
proof (rule contI2)
  show "monofun (sbMapStream f)"
  proof  (rule monofunI)
    fix x y:: "('a ::message) stream ubundle"
    assume "x \<sqsubseteq> y"
    thus "sbMapStream f x \<sqsubseteq> sbMapStream f y "
      by (smt
          Abs_cfun_inverse2 assms(1) assms(2) below_ubundle_def below_option_def eq_imp_below
          fun_below_iff monofun_cfun_arg ubdom_below ubgetch_insert sbmapstream_dom sbmapstream_sbgetch
          ub_below)
  qed
  thus "\<forall>Y. chain Y \<longrightarrow> sbMapStream f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. sbMapStream f (Y i))"
    by (smt 
        assms(1) assms(2) ch2ch_monofun cont2contlubE eq_imp_below ubrep_chain_lub_dom_eq ubrep_chain_the
        less_UBI lub_eq ubrep_lub_eval option.sel ubrep_ubabs ubGetCh_def sbMapStream_def ubdom_insert
        ubgetch_insert sbmapstream_dom sbmapstream_well)
qed

lemma sbmapstream_cont2[simp]: assumes "cont f" and "\<forall>s. sdom\<cdot>(f s)\<subseteq>sdom\<cdot>s"
  shows "cont (sbMapStream f)"
  apply (rule contI)
  using sbmapstream_cont assms(1) assms(2) contE by blast

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbTake\<close>
(* ----------------------------------------------------------------------- *)
lemma sbtake_cont [simp]:"cont (\<lambda>b. sbMapStream (\<lambda>s. stake n\<cdot>s) b)"
by (simp)

lemma sbtake_insert: "sbTake n\<cdot>b = sbMapStream (\<lambda>s. stake n\<cdot>s) b"
by(simp add: sbTake_def)

lemma sbtake_zero: "sbTake 0\<cdot>In = ubLeast (ubDom\<cdot>In)"
  by (simp add: sbtake_insert sbMapStream_def ubLeast_def)

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
  by (simp add: sbdrop_insert)

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
  by (simp add: sbNTimes_def sbMapStream_def sntimes_def ubLeast_def)

lemma sbntimes_one [simp]: fixes b:: "'m stream ubundle" shows "1\<star>b = b" 
  by (simp add: sbNTimes_def sbMapStream_def sntimes_def ubLeast_def)

lemma sbntimes_sbdom [simp]: "ubDom\<cdot>(i\<star>b) = ubDom\<cdot>b"
  by (simp add: sbNTimes_def)

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
  by (smt
      Abs_cfun_inverse2 cont_Rep_cfun2 sbFilter_def sbfilter_sbdom sbmapstream_cont sbmapstream_dom
      subsetCE subsetI)

lemma sbfilter_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows  "(sbFilter A\<cdot>b) . c = sfilter A\<cdot>(b .c)"
  apply(simp add: sbFilter_def assms)
by (meson Streams.sbfilter_sbdom assms sbmapstream_sbgetch subsetCE subsetI)

(* ----------------------------------------------------------------------- *)
  (* Lemma *)
(* ----------------------------------------------------------------------- *)

lemma if_then_dom[simp]: "dom (\<lambda>c. (c \<in> cs)\<leadsto>b .c) = cs"
using dom_def by fastforce

lemma if_then_well[simp]: assumes "cs\<subseteq>ubDom\<cdot>b" shows "ubWell (\<lambda>c. (c\<in>cs) \<leadsto> (b .c))"
using assms apply(simp add: ubWell_def ubgetch_insert ubdom_insert)
using ubrep_well ubWell_def by blast

lemma if_then_chain[simp]: assumes "chain Y" and "monofun g"
  shows "chain (\<lambda>i. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
proof(cases "ubDom\<cdot>(Y 0) = In")
  case True 
  hence "\<forall>i. (ubDom\<cdot>(Y i) = In)" using assms(1) ubdom_chain_eq3 by blast
  thus ?thesis
    by (smt assms(1) assms(2) below_option_def monofunE option.sel option.simps(3) po_class.chain_def)
next
  case False
  hence "\<forall>i. (ubDom\<cdot>(Y i) \<noteq> In)" using assms(1) ubdom_chain_eq3 by blast
  thus ?thesis by (auto) 
qed

lemma if_then_mono [simp]:  assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
proof -
  obtain uu :: "('a\<^sup>\<Omega> \<Rightarrow> 'b option) \<Rightarrow> 'a\<^sup>\<Omega>" and uua :: "('a\<^sup>\<Omega> \<Rightarrow> 'b option) \<Rightarrow> 'a\<^sup>\<Omega>" where
    "\<forall>f. (\<not> monofun f \<or> (\<forall>u ua. u \<notsqsubseteq> ua \<or> f u \<sqsubseteq> f ua)) \<and> (monofun f \<or> uu f \<sqsubseteq> uua f \<and> f (uu f) \<notsqsubseteq> f (uua f))"
    using monofun_def by moura
  moreover
  { assume "(UBundle.ubDom\<cdot> (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) \<notsqsubseteq> (UBundle.ubDom\<cdot> (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))"
    { assume "((UBundle.ubDom\<cdot> (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) \<sqsubseteq> (UBundle.ubDom\<cdot> (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))) \<noteq> (Some (g (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))) \<sqsubseteq> Some (g (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))))"
      then have "UBundle.ubDom\<cdot> (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = UBundle.ubDom\<cdot> (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) \<longrightarrow> uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u) \<notsqsubseteq> uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u) \<or> (UBundle.ubDom\<cdot> (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) \<sqsubseteq> (UBundle.ubDom\<cdot> (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))"
        by auto
      then have "uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u) \<notsqsubseteq> uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u) \<or> (UBundle.ubDom\<cdot> (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) \<sqsubseteq> (UBundle.ubDom\<cdot> (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))"
        using ubdom_below by blast }
    then have "uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u) \<notsqsubseteq> uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u) \<or> (UBundle.ubDom\<cdot> (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uu (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) \<sqsubseteq> (UBundle.ubDom\<cdot> (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u)) = In)\<leadsto>g (uua (\<lambda>u. (UBundle.ubDom\<cdot>u = In)\<leadsto>g u))"
      using assms monofun_def some_below by blast }
  ultimately show ?thesis
    by meson
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
    by (smt
        assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun fun_below_iff
        if_then_lub is_ub_thelub lub_eq lub_fun monofun_cfun_arg monofun_cfun_fun po_class.chain_def
        po_eq_conv ubdom_chain_eq2 some_below)
qed  
 
lemma sbHdElem_cont: "cont (\<lambda> sb::'a stream ubundle. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
  apply(rule contI2)
  apply (simp add: sbHdElem_mono)
  using sbHdElem_cont_pre by blast

end