theory SB
  imports UBundle_Conc stream.Streams
begin

default_sort message

type_synonym 'm SB = "'m stream ubundle"


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

(* Converter function. *)
  (* definition should be right, but needs to be nicer *)
definition sbElemWell::"(channel \<rightharpoonup> 'm::message) \<Rightarrow> bool" where
"sbElemWell f \<equiv> \<forall>c\<in> dom f. f\<rightharpoonup>c \<in> ctype c"

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
  by (simp add: assms usclOkay_stream_def)

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
  subsection \<open>convDiscrUp\<close>
(* ----------------------------------------------------------------------- *)

(* convDiscrUp only modifies the range, not the domain *)
lemma convDiscrUp_dom[simp]: "dom (convDiscrUp f) = dom f"
  by(simp add: convDiscrUp_def)

(* Pseudo-Inverse function of convDiscrUp: Only inverts, if "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>" holds *)
definition invConvDiscrUp :: "(channel \<rightharpoonup> 'a discr\<^sub>\<bottom>) \<Rightarrow> (channel \<rightharpoonup> 'a)" where
"invConvDiscrUp f \<equiv> \<lambda>c. (c\<in>dom f) \<leadsto> (inv Discr (inv Iup (f \<rightharpoonup> c)))"

(* Domain of invConvDiscrUp depends entirely on f *)
lemma invConvDiscrUp_dom: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                            shows "dom (invConvDiscrUp f) = dom f"
  proof -
    have "dom (invConvDiscrUp f) \<subseteq> dom f"
      by (meson invConvDiscrUp_def domIff subsetI)
    moreover have "c \<in> dom f \<Longrightarrow> c \<in> dom (invConvDiscrUp f)"
      by (simp add: invConvDiscrUp_def)
    ultimately show ?thesis
      by (simp add: Collect_mono_iff invConvDiscrUp_def)
  qed

(* A substitution rule for invConvDiscrUp *)
lemma invConvDiscrUp_subst: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                                and "c \<in> dom f"
                              shows "(invConvDiscrUp f) \<rightharpoonup> c = inv Discr (inv Iup (f \<rightharpoonup> c))"
  by (simp add: assms(2) invConvDiscrUp_def)

(* TODO: Wrong theory *)
lemma iup_inv_iup: assumes "(x::('a::cpo)\<^sub>\<bottom>) \<noteq> \<bottom>"
                     shows "Iup (inv Iup x) = x"
  proof -
    have h0: "x \<noteq> Ibottom"
      using assms inst_up_pcpo by force
    then have h1: "\<exists>a. x = Iup a"
      using h0 u.exhaust by auto
    then obtain a where a_def: "x = Iup a"
      using h1 by blast
    then have h2: "inv Iup x = a"
      apply(subst a_def)
      by(simp add: inv_def)
    then have h3: "Iup (inv Iup x) = Iup a"
      by (simp add: h2)        
    then have h4: "Iup (inv Iup x) = x"
      using a_def h3 by auto
    then show ?thesis
      by simp
  qed

(* TODO: Wrong theory (+Naming?) *)
lemma iup_discr_and_back: assumes "(x::'a discr\<^sub>\<bottom>) \<noteq> \<bottom>"
                            shows "Iup (Discr (inv Discr (inv Iup x))) = x"
  proof -
    have "Iup (Discr (inv Discr (inv Iup x))) = Iup (inv Iup x)"
      by (metis discr.exhaust surj_def surj_f_inv_f)
    moreover have "Iup (inv Iup x) = x"
      by (simp add: assms iup_inv_iup)
    ultimately show ?thesis
      by simp
  qed

(* Given the assumption, invConvDiscrUp is the pseudo-inverse of convDiscrUp *)
lemma convDiscrUp_invConvDiscrUp_eq: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                                       shows "convDiscrUp (invConvDiscrUp f) = f"
                                         (is "?L = ?R")
  proof -
    have eq_dom: "dom ?L = dom ?R"
      by (simp add: assms invConvDiscrUp_dom)
    moreover have eq_on_dom: "\<And>c. c\<in>dom ?L \<Longrightarrow> ?L\<rightharpoonup>c = ?R\<rightharpoonup>c"
      proof -
        fix c::channel
        assume "c\<in>dom ?L"
        then show "?L\<rightharpoonup>c = ?R\<rightharpoonup>c"
          apply(simp add: invConvDiscrUp_def convDiscrUp_def)
          by(simp add: assms iup_discr_and_back)
      qed
    ultimately show ?thesis
      by (meson part_eq)
  qed

(* Given the assumption, the inverse of convDiscrUp exists (convDiscrUp is pseudo-invertible) *)
lemma convdiscrup_inv_ex: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                            shows "\<exists>x. convDiscrUp x = f"
  apply(rule_tac x="invConvDiscrUp f" in exI)
  by (simp add: assms convDiscrUp_invConvDiscrUp_eq)

(* Given the assumption, convDiscrUp is pseudo-bijective *)
lemma convdiscrup_inv_eq[simp]: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                                  shows "convDiscrUp (inv convDiscrUp f) = f"
  by (metis assms convdiscrup_inv_ex f_inv_into_f rangeI)

(* Given the assumption (convDiscrUp is pseudo-bijective), the domain of the inverse stays the same *)
lemma convdiscrup_inv_dom_eq[simp]: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                                      shows "dom (inv convDiscrUp f) = dom f"
  by (metis assms convdiscrup_inv_eq convDiscrUp_dom)
   
(* convDiscrUp is an injective function *) 
lemma convDiscrUp_inj: "inj convDiscrUp"
  proof (rule injI)
    fix x::"channel \<Rightarrow> 'b option" and y::"channel \<Rightarrow> 'b option"
    assume a1: "convDiscrUp x = convDiscrUp y"
    have f1: "dom x = dom y"
      by (metis a1 convDiscrUp_dom)
    have f2: "\<forall> xa \<in> dom x. (Iup (Discr (x \<rightharpoonup> xa))) = (Iup (Discr (y \<rightharpoonup> xa)))"
      by (metis (full_types) a1 convDiscrUp_def convDiscrUp_dom option.sel)
    show "x = y"     
      apply (subst fun_eq_iff)
      apply rule
      apply (case_tac "xa \<in> dom x") defer
       apply (metis a1 convDiscrUp_dom domIff)
      by (metis discr.inject domD f1 f2 option.sel u.inject)
  qed

lemma convDiscrUp_eqI: "convDiscrUp x = convDiscrUp y \<Longrightarrow> x = y"
  by (simp add: convDiscrUp_inj inj_eq)

(* Substitution rule for the inverse of convDiscrUp *)
lemma convDiscrUp_inv_subst: assumes "\<forall>c\<in>dom f. (f \<rightharpoonup> c) \<noteq> \<bottom>"
                                 and "c \<in> dom f"
                               shows "((inv convDiscrUp) f) \<rightharpoonup> c = inv Discr (inv Iup (f \<rightharpoonup> c))"
  proof -
    have "((inv convDiscrUp) f) = (invConvDiscrUp f)"
      proof -
        have "convDiscrUp ((inv convDiscrUp) f) = f"
          by (simp add: assms(1))
        moreover have "convDiscrUp (invConvDiscrUp f) = f"
          by (simp add: assms(1) convDiscrUp_invConvDiscrUp_eq)
        ultimately show ?thesis
          by (simp add: convDiscrUp_eqI)
      qed
    moreover have "(invConvDiscrUp f) \<rightharpoonup> c = inv Discr (inv Iup (f \<rightharpoonup> c))"
      by (simp add: assms invConvDiscrUp_subst)
    ultimately show ?thesis
      by simp
  qed
(* ----------------------------------------------------------------------- *)
  subsection \<open>sbElemWell\<close>
(* ----------------------------------------------------------------------- *)

lemma sbElemWellI: assumes "sbElemWell f"
                       and "c \<in> dom f"
                     shows "(f \<rightharpoonup> c) \<in> ctype c"
  using assms(1) assms(2) sbElemWell_def by auto

lemma sbElemWellI2: assumes "sbElemWell f"
                        and "c \<in> dom f"
                        and "(f \<rightharpoonup> c) = a"
                      shows "a \<in> ctype c"
  using assms(1) assms(2) assms(3) sbElemWellI by auto
    
lemma sbElemWellEx:"\<exists>x::channel \<Rightarrow> 'm option. sbElemWell x"
  apply(simp add: sbElemWell_def)
  by fastforce

(* ----------------------------------------------------------------------- *)
  subsection \<open>convSB\<close>
(* ----------------------------------------------------------------------- *)

lemma convsb_ubwell: assumes "sbElemWell (sb)" 
  shows "ubWell (\<lambda>c. (c \<in> dom sb) \<leadsto> (lscons\<cdot>((convDiscrUp sb) \<rightharpoonup> c)\<cdot>\<epsilon>))"
  apply (rule ubwellI) 
  apply (simp add: domIff2)
  unfolding usclOkay_stream_def
proof - 
  fix c
  assume c_in_dom: "c \<in> dom sb"
  have f0: "sb\<rightharpoonup>c \<in> ctype c"
    by (simp add: assms c_in_dom sbElemWellI)
  have f1: "updis(sb\<rightharpoonup>c) && \<epsilon> = convDiscrUp sb\<rightharpoonup>c && \<epsilon>"
    by (simp add: c_in_dom convDiscrUp_def up_def)
  have f2: "updis(sb\<rightharpoonup>c) && \<epsilon> = \<up>(sb\<rightharpoonup>c)"
    by (simp add: sup'_def)
  have f3: "sdom\<cdot>(convDiscrUp sb\<rightharpoonup>c && \<epsilon>) = sdom\<cdot>(\<up>sb\<rightharpoonup>c)"
    using f1 f2 by auto
  have f4: "sdom\<cdot>(\<up>sb\<rightharpoonup>c) = {sb\<rightharpoonup>c}"
    by simp
  show "sdom\<cdot>(convDiscrUp sb\<rightharpoonup>c && \<epsilon>) \<subseteq> ctype c"
    by (simp add: f0 f3)
qed

lemma convsb_dom: assumes "sbElemWell (sb)" shows "ubDom\<cdot>(convSB (convDiscrUp sb)) = dom sb"
  apply (simp add: convSB_def)
  apply (subst ubdom_ubrep_eq)
   apply (simp add: assms convsb_ubwell)
  by simp

lemma convsb_apply: assumes "sbElemWell (sb)" and "c \<in> dom sb" 
  shows " (convSB (convDiscrUp sb)) . c = \<up>(sb \<rightharpoonup>c)"
  apply (simp add: convSB_def)
  apply (simp add: ubgetch_ubrep_eq assms convsb_ubwell)
  by (simp add: assms(2) convDiscrUp_def sup'_def up_def)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbMapStream\<close>
(* ----------------------------------------------------------------------- *)

lemma [simp]: assumes "\<forall>s. sdom\<cdot>(f s) \<subseteq> sdom\<cdot>s"
  shows "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
using assms by blast

lemma sbmapstream_well[simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto>f (b. c))"
  by (smt assms domIff option.sel ubWell_def ubdom_channel_usokay ubgetch_insert usclOkay_stream_def)

lemma sbmapstream_dom [simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "ubDom\<cdot>(sbMapStream f b) = ubDom\<cdot>b"
proof -
  have "\<forall>f u. (\<exists>c s. usclOkay c (s::'a stream) \<and> \<not> usclOkay c (f s)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    using ubMapStream_ubDom by blast
  then obtain cc :: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> channel" and ss :: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> 'a stream" where
    f1: "\<forall>f u. usclOkay (cc f) (ss f) \<and> \<not> usclOkay (cc f) (f (ss f)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    by moura
  have "ubMapStream f b = sbMapStream f b"
    by (simp add: sbMapStream_def ubMapStream_def)
  then show ?thesis
    using f1 by (metis (no_types) assms usclOkay_stream_def)
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

lemma sbhd_getch [simp]: assumes "c\<in>ubDom\<cdot>sb"
  shows "(sbHd\<cdot>sb) . c = stake 1\<cdot>(sb . c)"
  by(simp add: sbHd_def assms)
  

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

lemma sbRt2srt[simp]: assumes "ubWell [c \<mapsto> x]"
                        shows "sbRt\<cdot>(Abs_ubundle [c \<mapsto> x]) = (Abs_ubundle [c \<mapsto> srt\<cdot>x])"
                          (is "?L = ?R")
  proof -
    have srt_sdom: "sdom\<cdot>(srt\<cdot>x) \<subseteq> sdom\<cdot>x"
      by (metis (full_types) Un_upper2 sdom2un stream.sel_rews(2) subsetI surj_scons)
    have sdom_ctype: "sdom\<cdot>x \<subseteq> ctype c"
      apply(fold usclOkay_stream_def)
      by (metis (full_types) assms dom_eq_singleton_conv fun_upd_same insertI1 option.sel ubWell_def)
    have srt_ctype: "sdom\<cdot>(srt\<cdot>x) \<subseteq> ctype c"
      using srt_sdom sdom_ctype by auto
    have well_r: "ubWell [c \<mapsto> srt\<cdot>x]"
      by (metis srt_ctype sbset_well ubWell_empty ubrep_ubabs)
    have dom_r: "ubDom\<cdot>?R = {c}"
      by (simp add: well_r ubdom_ubrep_eq)
    have dom_l: "ubDom\<cdot>?L = {c}"
      by (simp add: assms ubdom_ubrep_eq)
    moreover have "?L .c = ?R .c"
      apply(simp add: sbRt_def sbDrop_def assms ubdom_ubrep_eq )
      by (simp add: assms well_r sdrop_forw_rt ubgetch_ubrep_eq)
    ultimately show ?thesis
      by (metis dom_r dom_l singletonD ubgetchI)
  qed

lemma sbrt_getch [simp]: assumes "c\<in>ubDom\<cdot>sb"
  shows "(sbRt\<cdot>sb) . c = srt\<cdot>(sb . c)"
  apply(simp add: sbRt_def assms)
  by (simp add: sdrop_forw_rt)

lemma sbrt_conc_hd[simp]: "sbRt\<cdot>(ubConc (sbHd\<cdot>sb)\<cdot>sb) = sb"
  apply(rule ub_eq)
   apply simp
  apply (simp add: usclConc_stream_def)
  using stake_srt_conc by auto

lemma sbRt_surj: "surj (Rep_cfun sbRt)"
  by (metis sbrt_conc_hd surj_def)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbLen\<close>
(* ----------------------------------------------------------------------- *)

lemma sbLen_empty_bundle [simp]: assumes "ubclLen sb = 0"
  shows "\<exists>c\<in>ubclDom\<cdot>sb. (sb . c) = \<epsilon>"
  apply (simp add: ubclDom_ubundle_def ubclLen_ubundle_def)
  proof -
    have dom_not_empty: "ubDom\<cdot>sb \<noteq> {}"
      using assms
      apply (simp add: ubclDom_ubundle_def ubclLen_ubundle_def)
      apply (simp add: ubLen_def)
      by auto
    have empty_sb_equal_zero: "\<exists>c::channel\<in>ubDom\<cdot>sb. (usclLen\<cdot>(sb . c) = 0)"
      by (metis (no_types, lifting) assms dom_not_empty ubLen_def ubclLen_ubundle_def ublen_min_on_channel)
    show "\<exists>c::channel\<in>ubDom\<cdot>sb. (sb  .  c) = \<epsilon>"
      using assms
      apply (simp add: ubclDom_ubundle_def ubclLen_ubundle_def)
      by (metis empty_sb_equal_zero slen_empty_eq usclLen_stream_def)
  qed

lemma sbConcEq_Len1 [simp]: assumes "ubDom\<cdot>b1 = ubDom\<cdot>b2"
  shows "ubLen(b1 :: 'a stream ubundle) \<le> ubLen(ubConcEq b1\<cdot>b2)"
  proof - 
    have dom_empty: "ubDom\<cdot>b2 = {} \<Longrightarrow> ubLen b1 \<le> ubLen(ubConcEq b1\<cdot>b2)"
      by (simp add: ubLen_geI)
    have dom_not_empty: "ubDom\<cdot>b2 \<noteq> {} \<Longrightarrow> ubLen b1 \<le> ubLen(ubConcEq b1\<cdot>b2)"
      proof -
        assume a1: "ubDom\<cdot>b2 \<noteq> {}"
        have h1: "ubDom\<cdot>b1 \<noteq> {}"
          by (simp add: a1 assms)
        have h2: "\<And>c::channel. c \<in> ubDom\<cdot>b2 \<Longrightarrow> c \<in> ubDom\<cdot>b1 \<Longrightarrow> #(b1  .  c) \<le> #((ubUp\<cdot>b1  .  c) \<bullet> ubUp\<cdot>b2  .  c)"
          apply (case_tac "#(b2  .  c) = \<infinity>")
          apply (simp add: slen_sconc_snd_inf)
          apply (case_tac "#(b1  .  c) = \<infinity>")
          apply simp
          apply(simp add: ubup_insert ubconc_insert ubgetch_insert)
          proof - 
            fix c
            assume a1: "c \<in> ubDom\<cdot>b2"
            assume a2: "c \<in> ubDom\<cdot>b1"
            assume a3: "#Rep_ubundle b2\<rightharpoonup>c \<noteq> \<infinity>"
            assume a4: "#Rep_ubundle b1\<rightharpoonup>c \<noteq> \<infinity>"
            obtain k1 where k1_def: "#Rep_ubundle b1\<rightharpoonup>c = Fin k1"
              by (metis a4 lncases)
            obtain k2 where k2_def: "#Rep_ubundle b2\<rightharpoonup>c = Fin k2"
              by (metis a3 lncases)
            show "#Rep_ubundle b1\<rightharpoonup>c \<le> #(Rep_ubundle b1\<rightharpoonup>c \<bullet> Rep_ubundle b2\<rightharpoonup>c)"
              using k1_def k2_def
              by (simp add: slen_sconc_all_finite)
          qed
        have h3: "\<forall>c\<in>ubDom\<cdot>b1. ubLen b1 \<le> usclLen\<cdot>(usclConc(ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c)) "
          apply (simp add: ubLen_def)
          by (metis (mono_tags, lifting) Least_le h1 assms dual_order.trans h2 ubup_ubgetch usclConc_stream_def usclLen_stream_def)
        have h4: "\<exists>c\<in>ubDom\<cdot>b1. usclLen\<cdot>(usclConc(ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c)) = ubLen(ubConcEq b1\<cdot>b2)"
          by (metis (no_types, lifting) Un_absorb Un_upper2 a1 assms ubLen_def ubconc_dom ubconc_getch ubconceq_dom ubconceq_insert ublen_min_on_channel ubrestrict_id)
        show ?thesis
          using h3 h4 by auto          
      qed
    then show ?thesis
      using dom_empty by blast
  qed

lemma sbConcEq_Len2 [simp]: "ubLen(b2 :: 'a stream ubundle) \<le> ubLen(ubConcEq b1\<cdot>b2)"
  proof -
    have dom_empty: "ubDom\<cdot>b2 = {} \<Longrightarrow> ubLen b2 \<le> ubLen(ubConcEq b1\<cdot>b2)"
      by (simp add: ubLen_def)
    have dom_not_empty1: "ubDom\<cdot>b2 \<noteq> {} \<Longrightarrow> ubDom\<cdot>b1 = {} \<Longrightarrow> ubLen b2 \<le> ubLen(ubConcEq b1\<cdot>b2)"
      proof -
        assume a1: "ubDom\<cdot>b2 \<noteq> {}"
        assume a2: "ubDom\<cdot>b1 = {}"
        have h1: "(ubDom\<cdot>b1 \<union> ubDom\<cdot>b2) = ubDom\<cdot>b2"
          using a2 by auto
        have h21: "\<forall>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)) = Some (ubUp\<cdot>b2 . c)"
          by (simp add: a2 usclConc_stream_def)
        have h2: "b2 = ubConc b1\<cdot>b2"
          by (metis (no_types, lifting) h1 h21 option.inject ubconc_dom ubconc_getch ubgetchI ubup_ubgetch)
        have h3: "b2 = ubConcEq b1\<cdot>b2"
          using h2 by (auto simp add: ubconceq_insert)
        show ?thesis
          using h3 by auto
      qed
    have dom_not_empty2: "ubDom\<cdot>b2 \<noteq> {} \<Longrightarrow> ubDom\<cdot>b1 \<noteq> {} \<Longrightarrow> ubLen b2 \<le> ubLen(ubConcEq b1\<cdot>b2)"
      proof -
        assume a1: "ubDom\<cdot>b2 \<noteq> {}"
        assume a2: "ubDom\<cdot>b1 \<noteq> {}"
        have h1: "(ubDom\<cdot>b1 \<union> ubDom\<cdot>b2) \<inter> ubDom\<cdot>b2 = ubDom\<cdot>b2"
          using a1 by blast
        have h21: "\<And>c::channel. c \<in> ubDom\<cdot>b2 \<Longrightarrow> c \<in> ubDom\<cdot>b1 \<Longrightarrow> #(b2  .  c) \<le> #((ubUp\<cdot>b1  .  c) \<bullet> ubUp\<cdot>b2  .  c)"
          apply (case_tac "#(b2  .  c) = \<infinity>")
          apply (simp add: slen_sconc_snd_inf)
          apply (case_tac "#(b1  .  c) = \<infinity>")
          apply simp
          apply(simp add: ubup_insert ubconc_insert ubgetch_insert)
          proof - 
            fix c
            assume a1: "c \<in> ubDom\<cdot>b2"
            assume a2: "c \<in> ubDom\<cdot>b1"
            assume a3: "#Rep_ubundle b2\<rightharpoonup>c \<noteq> \<infinity>"
            assume a4: "#Rep_ubundle b1\<rightharpoonup>c \<noteq> \<infinity>"
            obtain k1 where k1_def: "#Rep_ubundle b1\<rightharpoonup>c = Fin k1"
              by (metis a4 lncases)
            obtain k2 where k2_def: "#Rep_ubundle b2\<rightharpoonup>c = Fin k2"
              by (metis a3 lncases)
            show "#Rep_ubundle b2\<rightharpoonup>c \<le> #(Rep_ubundle b1\<rightharpoonup>c \<bullet> Rep_ubundle b2\<rightharpoonup>c)"
              using k1_def k2_def
              by (simp add: slen_sconc_all_finite)
          qed
        have h2: "\<forall>c\<in>ubDom\<cdot>b2. usclLen\<cdot>(b2 . c) \<le> usclLen\<cdot>(usclConc(ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c))"
          apply (simp only: usclConc_stream_def usclLen_stream_def)
          apply rule
          apply (case_tac "c\<in>ubDom\<cdot>b1")
          using h21 apply blast
          by simp
        have h3: "\<forall>c\<in>ubDom\<cdot>b2. (LEAST ln. ln\<in>{(usclLen\<cdot>(b2. c)) | c. c \<in> ubDom\<cdot>b2}) \<le> usclLen\<cdot>(usclConc(ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c))"
          by (metis (mono_tags, lifting) Least_le dual_order.trans h2 mem_Collect_eq)         
        have h4: "\<forall>c\<in>ubDom\<cdot>b2. ubLen b2 \<le> usclLen\<cdot>(usclConc(ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c)) "
          apply (simp add: ubLen_def)
          using h3 by auto          
        have h5: "\<exists>c\<in>ubDom\<cdot>b2. usclLen\<cdot>(usclConc(ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c)) = ubLen(ubConcEq b1\<cdot>b2)"
          by (metis (no_types, lifting) IntE a1 h1 ubLen_def ubconc_getch ubconceq_dom ubconceq_insert ubgetch_ubrestrict ublen_min_on_channel)
        show ?thesis
          using h4 h5 by auto
      qed
    then show ?thesis
      using dom_empty dom_not_empty1 by blast
  qed

(* ----------------------------------------------------------------------- *)
  subsection \<open>snNtimes\<close>
(* ----------------------------------------------------------------------- *)

lemma sbntimes_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "(n\<star>b) . c = sntimes n (b . c)"
  using assms by (smt
    domIff option.sel sbMapStream_def sbNTimes_def sntimes_sdom1 subset_trans ubWell_def
    ubdom_channel_usokay ubgetch_insert ubgetch_ubrep_eq usclOkay_stream_def)

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

lemma sbHdElem_mono: "monofun (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"
proof(rule monofunI)
  fix x y ::"'a stream ubundle"
  assume "x \<sqsubseteq> y"
  then show "(\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) x \<sqsubseteq> (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) y"
    by (smt below_option_def fun_below_iff monofun_cfun_arg option.discI option.sel ubdom_below)
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

lemma sbhdelem_insert: "sbHdElem\<cdot>sb = (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))"
  by(simp add: sbHdElem_def sbHdElem_cont)

lemma sbHdElem_bottom_exI: assumes "(\<exists>c\<in>ubDom\<cdot>sb. sb  .  c = \<epsilon>)"
  shows "(\<exists>c::channel\<in>ubDom\<cdot>sb. sbHdElem\<cdot>sb\<rightharpoonup>c = \<bottom>)"
proof -
  obtain my_c where my_c_def1: "sb . my_c = \<epsilon>" and my_c_def2: "my_c \<in> ubDom\<cdot>sb"
    using assms by auto
  have f0: " sbHdElem\<cdot>sb\<rightharpoonup>my_c = \<bottom>"
    apply (simp add: sbHdElem_def sbHdElem_cont)
    by (simp add: my_c_def1 my_c_def2)
  then show "(\<exists>c::channel\<in>ubDom\<cdot>sb. sbHdElem\<cdot>sb\<rightharpoonup>c = \<bottom>)"
    using my_c_def2 by auto
qed

lemma sbHdElem_dom[simp]:"dom (sbHdElem\<cdot>sb) = ubDom\<cdot>sb"
  by(simp add: sbHdElem_def sbHdElem_cont)

lemma sbHdElem_channel: assumes "ubDom\<cdot>sb = In"  and "c \<in> In" and "sb . c \<noteq> \<bottom>" shows "sbHdElem\<cdot>sb\<rightharpoonup>c \<noteq> \<bottom>"
    by(simp add: sbHdElem_def sbHdElem_cont assms) 

(* Substituting sbHdElem with shd *)
lemma sbHdElem_2_shd: assumes "\<forall>c\<in>(ubDom\<cdot>sb). sb .c \<noteq> \<epsilon>"
                          and "c \<in> ubDom\<cdot>sb"
                        shows "(inv convDiscrUp (sbHdElem\<cdot>sb))\<rightharpoonup>c = shd(sb .c)"
  proof -
    have h1:"sbHdElem\<cdot>sb\<rightharpoonup>c = lshd\<cdot>(sb .c)"
      by(simp add: assms sbHdElem_def sbHdElem_cont)
    then have h2: "(inv convDiscrUp (sbHdElem\<cdot>sb))\<rightharpoonup>c = inv Discr (inv Iup (lshd\<cdot>(sb .c)))" 
      by (simp add: assms(1) assms(2) convDiscrUp_inv_subst sbHdElem_channel)
    moreover have h4: "\<exists>a. lshd\<cdot>(sb .c) = Iup (Discr a)"
      by (metis (no_types, lifting) assms convDiscrUp_def convdiscrup_inv_dom_eq convdiscrup_inv_eq h1 option.sel sbHdElem_channel sbHdElem_dom)
    then have h5: "lshd\<cdot>(sb .c) = Iup (Discr (shd(sb .c)))"
      apply(simp add: shd_def up_def)
      using assms by auto
    then have "inv Discr (inv Iup (lshd\<cdot>(sb .c))) = shd (sb .c)"
      by (metis (no_types, lifting) h1 assms convDiscrUp_def convdiscrup_inv_dom_eq convdiscrup_inv_eq discr.inject h2 option.sel sbHdElem_dom sbHdElem_channel u.inject)
    ultimately show ?thesis
      by simp
  qed

(* Substituting sbHdElem with shd over a simple bundle *)
lemma sbHdElem_2_shd2: assumes "x\<noteq>\<epsilon>" 
                           and "ubWell [c \<mapsto> x]" 
                         shows "inv convDiscrUp (sbHdElem\<cdot>(Abs_ubundle [c\<mapsto>x])) = [c\<mapsto>shd(x)]"
                           (is "?L = ?R")
  proof -
    have convDiscrUp_assms: "\<forall>c\<in>dom(sbHdElem\<cdot>(Abs_ubundle[c\<mapsto>x])). (sbHdElem\<cdot>(Abs_ubundle[c\<mapsto>x]))\<rightharpoonup>c \<noteq> \<bottom>"
      by (metis assms dom_fun_upd fun_upd_same option.sel option.simps(3) sbHdElem_channel 
                sbHdElem_dom singletonD ubWell_empty ubdom_empty ubdom_ubrep_eq ubgetch_ubrep_eq)
    have l_dom: "dom ?L = {c}"
      by (simp add: convDiscrUp_assms assms(2) ubdom_ubrep_eq)
    moreover have r_dom: "dom ?R = {c}"
      by simp
    moreover have eq_on_dom: "?R \<rightharpoonup> c = ?L \<rightharpoonup> c"
      by (simp add: assms(1) assms(2) sbHdElem_2_shd ubdom_ubrep_eq ubgetch_ubrep_eq)
    ultimately show ?thesis
      by (metis part_eq singletonD)
  qed

lemma sbHdElem_sbElemWell: assumes "\<forall>c\<in>(ubDom\<cdot>sb). sb .c \<noteq> \<epsilon>"
                             shows "sbElemWell (inv convDiscrUp (sbHdElem\<cdot>sb))"
  proof -
    (* Assumptions of convDiscrUp-lemmas *)
    have convDiscrUp_assms: "\<forall>c\<in>dom (sbHdElem\<cdot>sb). (sbHdElem\<cdot>sb \<rightharpoonup> c) \<noteq> \<bottom>"
      by (simp add: assms sbHdElem_channel)
    (* Reformulation of the thesis to better match proving technique *)
    have "\<And>c::channel. c\<in>ubDom\<cdot>sb \<Longrightarrow> inv convDiscrUp (sbHdElem\<cdot>sb)\<rightharpoonup>c \<in> ctype c"
      proof -
        fix c::channel
        assume a1: "c\<in>ubDom\<cdot>sb"
        moreover have "inv convDiscrUp (sbHdElem\<cdot>sb)\<rightharpoonup>c = shd(sb .c)"
          by(simp add: assms a1 sbHdElem_2_shd)
        moreover have "usclOkay c (sb .c)"
          by (simp add: a1 ubgetch_insert)
        then have "sdom\<cdot>(sb .c) \<subseteq> ctype c"
          using  usclOkay_stream_def by blast
        then have "shd (sb .c) \<in> ctype c" 
          by (metis a1 assms sfilter_ne_resup sfilter_sdoml3)
        ultimately show "inv convDiscrUp (sbHdElem\<cdot>sb)\<rightharpoonup>c \<in> ctype c" 
          by simp
      qed
    then show ?thesis
      by(simp add: sbElemWell_def convDiscrUp_assms)
  qed



(* ----------------------------------------------------------------------- *)
  subsection \<open>ubConc on Streams\<close>
(* ----------------------------------------------------------------------- *)


lemma sbconc_inj_h: assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  and "ubConcEq sb\<cdot>x . c = ubConcEq sb\<cdot>y . c" 
  and "c \<in> ubDom\<cdot>x" and "c \<in> ubDom\<cdot>y"
shows "x  .  c = y  .  c"
  apply(cases "c \<in> ubDom\<cdot>sb")
  using assms apply (simp add: usclConc_stream_def ubconceq_insert)
  using sconc_neq apply blast
  using assms apply (simp add: usclConc_stream_def ubconc_getch ubconceq_insert)
  done

lemma sbconc_inj: assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows "inj (Rep_cfun (ubConcEq sb))"
  apply rule
  apply(rule ub_eq)
   apply (metis ubconceq_dom ubconceq_insert)
  apply simp
  by (metis assms sbconc_inj_h ubconceq_dom ubconceq_insert)
  
  
lemma sbconc_inf: fixes sb::"'m::message SB"
    assumes "ubDom\<cdot>sb=ubDom\<cdot>ub_inf" and "ubLen ub_inf = \<infinity>"
  shows "ubConc ub_inf\<cdot>sb = ub_inf"
proof(rule ub_eq)
  show "ubDom\<cdot>(ubConc ub_inf\<cdot>sb) = ubDom\<cdot>ub_inf" by (simp add: assms(1))
next
  fix c
  assume "c \<in> ubDom\<cdot>(ubConc ub_inf\<cdot>sb)"
  hence c_dom: "c\<in>(ubDom\<cdot>ub_inf)"
    by (simp add: assms(1))
  hence "usclLen\<cdot>(ub_inf . c) = \<infinity>"
    using assms(2) ublen_channel by fastforce
  thus "(ubConc ub_inf\<cdot>sb)  .  c = ub_inf  .  c"
    by (simp add: c_dom assms(1) usclConc_stream_def usclLen_stream_def)
qed







lemma sblen_up_restrict[simp]: fixes ub ::"'a::message SB"
  assumes "ubLen (ubRestrict cs\<cdot>(ubUp\<cdot>ub)) \<noteq> 0"
  shows "cs \<subseteq> ubDom\<cdot>ub"
proof - 
  have "\<And>c. c\<in>cs \<Longrightarrow>  usclLen\<cdot>((ubRestrict cs \<cdot>(ubUp\<cdot>ub)) . c) \<noteq> 0" 
    by(subst ublen_not_0, auto simp add: assms)
  hence "\<And>c. c\<in>cs \<Longrightarrow>  usclLen\<cdot>((ubUp\<cdot>ub) . c) \<noteq> 0" by simp
  thus ?thesis
    by (metis strict_slen subsetI ubup_ubgetch2 usclLen_stream_def)
qed


lemma sblen_up_restrict2[simp]: fixes ub ::"'a::message SB"
  shows "ubLen (ubRestrict cs\<cdot>(ubUp\<cdot>ub)) \<noteq> 0 \<Longrightarrow> (ubRestrict cs\<cdot>(ubUp\<cdot>ub)) = ubRestrict cs\<cdot>ub"
  apply(rule ub_eq)
  apply (simp add: inf_absorb2)
  apply simp
  by (simp add: rev_subsetD)




(* ----------------------------------------------------------------------- *)
  subsection \<open>Automaton\<close>
(* ----------------------------------------------------------------------- *)

(* Create a simple bundle. Used to shorten parts of automaton transitions, e.g. in EvenAutomaton *)
lift_definition createBundle :: "'a \<Rightarrow> channel \<Rightarrow> 'a SB" is
  "\<lambda>a c. if (a \<in> ctype c) then ([c \<mapsto> \<up>a]) else ([c \<mapsto> \<epsilon>]) "
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  by auto

lemma createBundle_dom[simp]: "ubDom\<cdot>(createBundle a c) = {c}"
  by (simp add: ubdom_insert createBundle.rep_eq)  

lemma createBundle_apply[simp]: assumes "a \<in> ctype c"
                                  shows "createBundle a c = Abs_ubundle [c \<mapsto> \<up>a]"
  by (simp add: assms createBundle.abs_eq)

lemma createbundle_ubgetch:
  assumes " m \<in> ctype c"
  shows   "(createBundle m c) . c  = \<up>m"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by (simp add: assms)

end
