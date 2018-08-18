(*  Title:        SBTheorie
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Stream Bundles" 
*)

theory SB
imports "../Channel" "../inc/OptionCpo" "../UnivClasses" Streams

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
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)


  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition sb_well :: "(channel \<rightharpoonup> 'm stream) => bool" where
"sb_well f \<equiv> \<forall>c \<in> dom f. sdom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c"

(* sb_well is admissible, used to define 'm SB with cpodef *)
lemma sb_well_adm[simp]: "adm sb_well"
by (simp add: adm_def sb_well_def part_dom_lub lub_fun the_subset_cont)

(* There is at least one element, that satisfies sb_well *)
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


(* Returns the domain of the stream bundle *)
definition sbDom :: "'m SB \<rightarrow> channel set" where
"sbDom \<equiv> \<Lambda> b. dom (Rep_SB b)"



(* Returns the stream flowing on a channel of a stream bundle *)
definition sbGetCh :: "'m SB \<rightarrow> channel \<rightarrow> 'm stream"  where
"sbGetCh \<equiv> \<Lambda> b c. ((Rep_SB b) \<rightharpoonup> c)"

abbreviation sbGetch_abbr :: "'m SB \<Rightarrow> channel \<Rightarrow> 'm stream" (infix "." 65) where 
"b . c \<equiv> sbGetCh\<cdot>b\<cdot>c"


(* For a given channel set, "sbLeast" is the smallest stream bundle with empty streams. *)
definition sbLeast :: "channel set \<Rightarrow> 'm SB" ("_^\<bottom>" [1000] 999) where
"sbLeast cs \<equiv> (\<lambda>c. (c \<in> cs) \<leadsto> \<epsilon> )\<Omega>"

(* The channel-domains are merged, the second argument has priority *)
definition sbUnion:: " 'm SB \<rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbUnion \<equiv> \<Lambda> b1 b2.  (Rep_SB b1 ++ Rep_SB b2)\<Omega>"

abbreviation sbUnion_abbr :: " 'm SB \<Rightarrow> 'm SB \<Rightarrow> 'm SB" (infixl "\<uplus>" 100) where 
"b1 \<uplus> b2 \<equiv> sbUnion\<cdot>b1\<cdot>b2"


(* Adds a channel or replaces its content *)
definition sbSetCh:: " 'm SB \<rightarrow> channel \<Rightarrow> 'm stream \<Rightarrow> 'm SB" where
"sbSetCh \<equiv> \<Lambda> b. (\<lambda> c s. b \<uplus> ([c \<mapsto> s]\<Omega>))"




(* Channels not in the channel set are set to "None". *)
definition sbRestrict:: "channel set \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbRestrict cs  \<equiv> \<Lambda> b. (Rep_SB b |` cs)\<Omega>"

abbreviation sbRestrict_abbr :: " 'm SB \<Rightarrow> channel set \<Rightarrow> 'm SB" ("(_\<bar>_)" [66,65] 65)
where "b\<bar>cs \<equiv> sbRestrict cs\<cdot>b"


(* Removes a channel from a stream bundle *)
definition sbRemCh:: " 'm SB \<rightarrow> channel \<rightarrow> 'm SB" where
"sbRemCh \<equiv> \<Lambda> b c.  b \<bar> -{c}" 


(* Renaming channels *)
definition sbRenameCh :: " 'm SB => channel => channel => 'm SB" where
"sbRenameCh b ch1 ch2 \<equiv> (sbSetCh\<cdot>(sbRemCh\<cdot>b\<cdot>ch1)) ch2 (b .ch1)"



(* Replaces all "None" channels with \<epsilon>. *)
definition sbUp:: " 'm SB \<rightarrow> 'm SB"  where
"sbUp \<equiv> \<Lambda> b . (\<lambda>c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b) c else Some \<epsilon>)\<Omega>"

abbreviation sbUp_abbr:: " 'm SB \<Rightarrow> 'm SB"  ("\<up>_" 70) where
"\<up>b \<equiv> sbUp\<cdot>b"


(* Equality on specific channels *)
definition sbEqSelected:: " channel set \<Rightarrow> 'm SB => 'm SB => bool" where
"sbEqSelected cs b1 b2 \<equiv>  (b1\<bar>cs) = (b2\<bar>cs)"

(* Equality on common channels *)
definition sbEqCommon:: " 'm SB => 'm SB => bool" where
"sbEqCommon b1 b2\<equiv> sbEqSelected (sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2) b1 b2"


(* The function 'm SB creates the set of all bundles b with a fixed set of channels C.*)
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
definition sbLen:: " 'm SB \<rightarrow> lnat " (* ("#_") *)where
"sbLen \<equiv> \<Lambda> b. if sbDom\<cdot>b \<noteq> {} then LEAST ln. ln \<in> { #(b. c) | c. c \<in> sbDom\<cdot>b} else \<infinity>"  

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
(* Custom iterate bc. "fix" requires a PCPO, which 'm SB isn't. Uses "(sbTake 0\<cdot>b)" as artificial \<bottom> *)
primrec myiterate :: "nat \<Rightarrow> 'm SB set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
    "myiterate 0 bs b = sbLeast (sbDom\<cdot>b)"
  | "myiterate (Suc n) bs b = (let rest = (myiterate n bs (sbRt\<cdot>b)) in
          if (sbHd\<cdot>b\<in>bs) then sbHd\<cdot>b \<bullet> rest else rest )"

  (* (if (sbHd\<cdot>b\<in>bs) then sbHd\<cdot>b \<bullet>(myiterate n bs (sbRt\<cdot>b)) else (myiterate n bs (sbRt\<cdot>b))) *)

(* Filter SB b by SB set bs of "tuples": delete the parts from b that cannot be constructed with bs *)
definition sbFilterTupel:: " 'm SB set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbFilterTupel bs b \<equiv> \<Squnion>i. myiterate i bs b"

definition sbFilterTupel2:: " 'm SB set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbFilterTupel2 A \<equiv> (\<Lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>(\<lambda>s. sbTake 0\<cdot>s))\<cdot>
      (\<Lambda> h. (\<lambda> b. if (sbHd\<cdot>b\<in>A) then sbHd\<cdot>b \<bullet> h (sbRt\<cdot>b) else h (sbRt\<cdot>b)))"
(* \<Squnion>i. iterate i\<cdot>(\<Lambda> f. (\<lambda>b. 
  if (b=sbLeast (sbDom\<cdot>b)) then sbLeast (sbDom\<cdot>b) else
    if (sbHd\<cdot>b\<in>bs) then (sbHd\<cdot>b) \<bullet> f (sbRt\<cdot>b) else f (sbRt\<cdot>b) ))\<cdot>(\<lambda>x. empty \<Omega>)"  *)

subsection \<open>Automaton\<close>

definition sbHdElem :: "'m SB \<rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"sbHdElem \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))" 

definition convDiscrUp :: "(channel \<rightharpoonup> 'm) \<Rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"convDiscrUp sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (Iup (Discr (sb \<rightharpoonup> c))))"

definition convSB :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm SB" where
"convSB sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (lscons\<cdot>(sb \<rightharpoonup> c)\<cdot>\<epsilon>))\<Omega>"



(* ----------------------------------------------------------------------- *)
section \<open>Lemmas\<close>
(* ----------------------------------------------------------------------- *)



subsection \<open>General Lemmas\<close>
(* ----------------------------------------------------------------------- *)
(* Lemmas about Rep_SB, Abs_SB or 'm SBLub *)

(*Streambundles are sb_well by definition*)
theorem rep_well[simp]: "sb_well (Rep_SB x)"
using Rep_SB by auto

(* Rep und Abs - Theorems *)
theorem rep_abs[simp]: assumes "sb_well f" shows "Rep_SB (Abs_SB f) = f"
by (simp add: Abs_SB_inverse assms)

(* A chain of 'm SBs is also a chain after applying Rep_SB *)
lemma rep_chain[simp]: assumes "chain S"
  shows "chain (\<lambda>n. Rep_SB (S n))"
by (meson assms below_SB_def po_class.chain_def)

(* A chain of 'm SBs is also a chain after applying Rep_SB and fixing a channel*)
lemma theRep_chain[simp]: assumes "chain S" 
  shows "chain (\<lambda>n. the (Rep_SB (S n) c))"
using assms part_the_chain rep_chain by fastforce

(* The LUB of the chain after applying Rep_SB is also sb_well *)
lemma lub_well[simp]: assumes "chain S"
  shows "sb_well (\<Squnion>n. Rep_SB (S n))"
by (metis rep_chain adm_def sb_well_adm assms rep_well)

(* LUB and Rep_SB are commutative *)
lemma rep_lub:assumes "chain Y"
  shows "(\<Squnion>i. Rep_SB (Y i)) = Rep_SB (\<Squnion>i.  Y i)"
using assms lub_SB by fastforce

(* Rep_SB is a continuous function *)
lemma rep_cont [simp]: "cont Rep_SB"
by (metis rep_chain contI cpo_lubI rep_lub)

(* "the" and LUB are commutative *)
lemma rep_SB_up_lub[simp]: assumes "chain Y"
  shows "range (\<lambda>n. the (Rep_SB (Y n) c)) <<| the (\<Squnion>n. Rep_SB (Y n) c)"
by (metis rep_chain assms cpo_lubI part_the_cont2 theRep_chain)

(* an easy to use introduction rule for "sb_well" *)
lemma sb_wellI[simp]: assumes "\<And>c. c \<in> dom f \<Longrightarrow> sdom\<cdot>(the(f c)) \<subseteq> ctype c"
  shows "sb_well f"
by (simp add: assms sb_well_def)

(* Abs_SB is a continuous function *)
lemma cont_Abs_SB[simp]: assumes "cont g" and "\<forall>x. sb_well (g x)"
  shows "cont (\<lambda>x. (g x)\<Omega>)"
by (simp add: assms(1) assms(2) cont_Abs_SB)

(* Applying Abs_SB to Rep_SB is the identity *)
lemma [simp]: "(Rep_SB b2)\<Omega> = b2"
by (simp add: Rep_SB_inverse)

(* If c is in the domain a SB, then this channel is well typed *)
lemma wt2[simp]: assumes "c \<in> dom (Rep_SB (S k))" 
  shows "sdom\<cdot>(the (Rep_SB (S k) c)) \<subseteq> ctype c"
using assms rep_well sb_well_def by blast

(* A chain of SBs consists only of SBs with the same domain *)
lemma l400[simp]: assumes "chain S" and "c \<in> dom (Rep_SB (S k))"
  shows "c\<in>dom (Rep_SB (S j))"
by (metis assms(1) assms(2) below_SB_def is_ub_thelub part_dom_eq)

(* For all SBs in a chain, all channels within the domain are well typed *)
lemma l460: assumes "chain S" and "c \<in> dom (Rep_SB (S k))"
  shows "sdom\<cdot>(the (Rep_SB (S i) c)) \<subseteq> ctype c"
using assms(1) assms(2) l400 rep_well sb_well_def by blast

(* For all SBs in a chain, the LUB of all channels within the domain is well typed *)
lemma l500: assumes "chain S" and "c \<in> dom (Rep_SB (S k))"
       shows "sdom\<cdot>(\<Squnion>j. the (Rep_SB (S j) c)) \<subseteq> ctype c"
by (smt assms(1) assms(2) l44 theRep_chain l460 lub_eq)

(* LUB and getting the value from an optional ("the" operator) are commutative. *)
lemma lub_eval: assumes "chain S" 
  shows "the (Rep_SB (\<Squnion>i. S i) c) = (\<Squnion>j. the (Rep_SB (S j) c))"
using assms part_the_lub rep_chain rep_lub by fastforce

(* The domain of any SB in a chain is the same as the domain of the LUB. *)
lemma l1: assumes "chain S" 
  shows "dom (Rep_SB (S i)) = dom (Rep_SB (\<Squnion>i. S i))"
by (meson assms below_SB_def is_ub_thelub part_dom_eq)

(* If SB's b1 and b2 have the same domain and for every channel c b1.c \<sqsubseteq> b2.c holds, b1 \<sqsubseteq> b2. *)
lemma less_SBI: assumes "dom (Rep_SB b1) = dom (Rep_SB b2)" 
    and "\<And>c. c\<in>dom (Rep_SB b1) \<Longrightarrow>  the ((Rep_SB b1) c) \<sqsubseteq> the ((Rep_SB b2) c)"
  shows "b1 \<sqsubseteq> b2"
by (metis assms(1) assms(2) below_SB_def below_option_def domIff fun_belowI)

(* For any channel c and sb a SB from the chain, sb.c \<sqsubseteq> LUB.c (LUB is an upper bound) *)
lemma less_sbLub1: assumes "chain S" 
  shows "the (Rep_SB (S i) c) \<sqsubseteq> the (Rep_SB (\<Squnion>i. S i) c)"
by (metis assms(1) is_ub_thelub theRep_chain lub_eval)

(* For any channel c and any upper bound u of the chain of SBs, LUB.c \<sqsubseteq> u.c (LUB is the smallest) *)
lemma less_sbLub2: assumes "chain S"  and "range S <| u"
  shows "the (Rep_SB (\<Squnion>i. S i) c) \<sqsubseteq> the (Rep_SB u c)"
by (metis assms below_SB_def below_option_def eq_imp_below fun_below_iff is_lub_thelub)




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbDom\<close>
(* ----------------------------------------------------------------------- *)


(* sbDom is continuous *)
lemma sbdom_cont [simp]: "cont (\<lambda> b. dom (Rep_SB b))"
by (simp add: cont_compose)

(* sbDom insert rule *)
lemma sbdom_insert: "sbDom\<cdot>b = dom (Rep_SB b)"
by (simp add: sbDom_def)

(* sbDom works as expected compared to its Map-counterpart "dom" if the bundle b is well-defined *)
lemma sbdom_rep_eq: "sb_well b \<Longrightarrow> sbDom\<cdot>(Abs_SB b) = dom b"
by (simp add: sbDom_def)

(* If one SB a is below (\<sqsubseteq>) another SB b, then their domains are equal *)
lemma sbdom_eq: assumes "a\<sqsubseteq>b"
  shows "sbDom\<cdot>a = sbDom\<cdot>b"
by (metis assms below_SB_def part_dom_eq sbdom_insert)

(* The domain of the empty SB is empty *)
lemma sbdom_empty [simp]: "sbDom\<cdot>(empty \<Omega>) = {}"
by (simp add: sbdom_insert sb_well_def)




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbGetCh\<close>
(* ----------------------------------------------------------------------- *)

(* Helper lemma for the continuous proof *)
lemma sbgetch_cont2[simp]: "cont (\<lambda> b c. the ((Rep_SB b) c))"
by (smt cont2cont_lambda contI cpo_lubI image_cong lub_eval theRep_chain) 

(* sbGetCh is continuous *)
lemma sbgetch_cont [simp]: "cont (\<lambda> b. \<Lambda> c. the ((Rep_SB b) c))"
using cont2cont_LAM cont2cont_fun sbgetch_cont2 channel_cont by force

(* Insert rule for sbGetCh *)
lemma sbgetch_insert: "b. c = the (Rep_SB b c)"
by (simp add: sbGetCh_def)

(* sbGetCh works as expected if the SB b is well-defined *)
lemma sbgetch_rep_eq: "sb_well b \<Longrightarrow> (Abs_SB b . c) = (b \<rightharpoonup> c)"
by (simp add: sbGetCh_def)

(* If the channel c is in the domain of the SB b, then the result of sbGetCh exists/is not None *)
lemma sbgetchE: assumes "(c\<in>sbDom\<cdot>b)"
  shows "Some (b .c) =  (Rep_SB b) c"
apply (simp add: domIff sbdom_insert sbgetch_insert)
using assms domIff sbdom_insert by force

(* If Y is a chain of SB, then applying the LUB and sbGetCh is commutative *)
lemma sbgetch_lub: "chain Y \<Longrightarrow> ((\<Squnion>i. Y i) . c) =  (\<Squnion>i. (Y i) . c)"
  by (metis (mono_tags, lifting) lub_eq lub_eval sbgetch_insert)





(* Zwischenteil, wird später gebraucht *)
(* The domains of SBs in a chain S are all equal *)
lemma sbchain_dom_eq: assumes "chain S"
  shows "sbDom\<cdot>(S i) = sbDom\<cdot>(S j)"
  by (simp add: assms l1 sbdom_insert)

(* The domains of SBs in a chain S are equal to the domain of the LUB *)
lemma sbChain_dom_eq2: assumes "chain S"
  shows "sbDom\<cdot>(S i) = sbDom\<cdot>(\<Squnion>j. S j)"
  by (simp add: assms l1 sbdom_insert)

(* If two SBs have the same domain and are equal for every channel, then the SBs are equal *)
lemma sb_eq: assumes "sbDom\<cdot>x = sbDom\<cdot>y" and "\<And>c. c\<in>(sbDom\<cdot>x) \<Longrightarrow> (x .c) = (y .c)"
  shows "x = y"
by (metis assms(1) assms(2) less_SBI po_eq_conv sbdom_insert sbgetch_insert)

(* Alternative definition of the LUB for a chain of SBs *)
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

(* If two SBs x,y have the same domain and for every channel c: x.c \<sqsubseteq> y.c, then x \<sqsubseteq> y *)
lemma sb_below[simp]: assumes "sbDom\<cdot>x = sbDom\<cdot>y" and "\<And>c. c\<in>sbDom\<cdot>x \<Longrightarrow> (x .c) \<sqsubseteq> (y .c)"
  shows "x \<sqsubseteq> y"
by (metis assms(1) assms(2) less_SBI sbdom_insert sbgetch_insert)

(* Alternative definition of the identity on SBs *)
lemma [simp]: "(\<lambda>c. (c \<in> sbDom\<cdot>b)\<leadsto>b . c)\<Omega> = b"
  apply(rule sb_eq)
   apply(subst sbdom_rep_eq)
    apply (smt domIff rep_well sb_well_def sbgetchE)
   apply simp
  by (smt domIff option.distinct(1) option.sel rep_abs rep_well sbgetchE sb_well_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbLeast\<close>
(* ----------------------------------------------------------------------- *)

(* sbLeast produces a partial function that is sb_well *)
lemma sbleast_well[simp]: "sb_well (\<lambda>c. (c \<in> cs)\<leadsto>\<epsilon>)"
by(auto simp add: sb_well_def)

(* The parameter to sbLeast defines the domain *)
lemma sbleast_sbdom [simp]: "sbDom\<cdot>(sbLeast cs) = cs"
by(simp add: sbDom_def sbLeast_def)

(* sbLeast for a channel set cs results in empty streams (\<epsilon>) on all channels c \<in> cs *)
lemma sbleast_getch [simp]: assumes "c \<in> cs" shows "sbLeast cs . c = \<epsilon>"
by (simp add: assms sbLeast_def sbgetch_insert)

(* sbLeast returns the smalles SB with the given domain *)
lemma sbleast_least [simp]: assumes "cs = sbDom\<cdot>b"
  shows "sbLeast cs \<sqsubseteq> b"
by (metis (full_types) assms minimal sbleast_getch sbleast_sbdom sb_below)

(* sbLeast for the empty domain results in an empty mapping/SB *)
lemma sbleast_empty: "sbLeast {} = Map.empty \<Omega>"
by (simp add: sbLeast_def)

(* If sbLeast {} (= empty\<Omega>) is in an chain, all elements are (by having the same domain) empty *)
lemma stbundle_allempty: assumes "chain Y" and "sbLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = sbLeast {}"
by (smt Rep_SB_inject assms(1) assms(2) dom_eq_empty_conv image_iff sbchain_dom_eq sbdom_insert sbleast_sbdom)



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbUnion\<close>
(* ----------------------------------------------------------------------- *)


(* sbUnion produces a partial function that is sb_well *)
lemma sbunion_well[simp]: assumes "sb_well b1" and "sb_well b2"
  shows "sb_well (b1 ++ b2)"
by (metis assms(1) assms(2) domIff mapadd2if_then sb_well_def)

(* Helper function for continuity proof *)
lemma sbunion_contL[simp]: "cont (\<lambda>b1. (Rep_SB b1) ++ (Rep_SB b2))"
using cont_compose part_add_contL rep_cont by blast

(* Helper function for continuity proof *)
lemma sbunion_contR[simp]: "cont (\<lambda>b2. (Rep_SB b1) ++ (Rep_SB b2))"
using cont_compose part_add_contR rep_cont by blast

(* sbUnion is a continuous function *)
lemma sbunion_cont[simp]: "cont (\<lambda> b1. \<Lambda> b2.((Rep_SB b1 ++ Rep_SB b2)\<Omega>))"
by(simp add: cont2cont_LAM)

(* Insert rule for sbUnion *)
lemma sbunion_insert: "(b1 \<uplus> b2) = (Rep_SB b1 ++ Rep_SB b2)\<Omega>"
by(simp add: sbUnion_def)


(* If all channels of SB b1 are also in SB b2, the union produces b2 *)
lemma sbunion_idL [simp]: assumes "sbDom\<cdot>b1\<subseteq>sbDom\<cdot>b2" shows "b1 \<uplus> b2 = b2"
using assms apply(simp add: sbunion_insert)
by(simp add: sbdom_insert)

(* The union with sbLeast{} (= empty\<Omega>) is the identity *)
lemma sbunion_idR [simp]: "b \<uplus> (sbLeast {}) = b"
by(simp add: sbunion_insert sbLeast_def)

(* If b1 and b2 have no common channels, sbUnion is commutative *)
lemma sbunion_commutative: assumes "sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2 = {}"
  shows "b1\<uplus>b2 = b2\<uplus>b1"
using assms apply(simp add: sbunion_insert)
  by (metis map_add_comm sbdom_insert)

(* sbUnion is associative *)
lemma sbunion_associative: "sb1 \<uplus> (sb2 \<uplus> sb3) = (sb1 \<uplus> sb2) \<uplus> sb3"
  by(simp add: sbunion_insert)
  
(* sbUnion prioritizes the second argument *)
lemma sbunion_getchR [simp]: assumes "c\<in>sbDom\<cdot>b2"
  shows "b1\<uplus>b2 . c = b2 . c"
apply(simp add: sbunion_insert sbgetch_insert)
by (metis (full_types) assms map_add_find_right sbgetchE)

(* sbUnion takes the definition of the 1st arg., iff channel c is not in the domain of the 2nd arg. *)
lemma sbunion_getchL [simp]: assumes "c\<notin>sbDom\<cdot>b2"
  shows "b1\<uplus>b2 . c = b1 . c"
apply(simp add: sbunion_insert sbgetch_insert)
by (metis assms map_add_dom_app_simps(3) sbdom_insert)

(* The domain of the union is the union of the domains *)
lemma sbunionDom [simp] : "sbDom\<cdot>(b1 \<uplus> b2) = sbDom\<cdot>b1 \<union> sbDom\<cdot>b2"
by(auto simp add: sbdom_insert sbunion_insert)

(* sbUnion keeps the \<sqsubseteq>-relation if the respective args. (1st-1st and 2nd-2nd) are in a \<sqsubseteq>-relation *)
lemma sbunion_pref_eq: assumes "(a \<sqsubseteq> b)" and "(c \<sqsubseteq> d)"
  shows "(a \<uplus> c \<sqsubseteq> b \<uplus> d)"
  by (simp add: assms(1) assms(2) monofun_cfun)

(* If only one argument differs, sbUnion's ordering (\<sqsubseteq>) depends entirely on that argument *)
lemma sbunion_pref_eq2: assumes "(a \<sqsubseteq> b)"
  shows "(x \<uplus> a \<sqsubseteq> x \<uplus> b)"
     by (metis assms monofun_cfun_arg)

(* sbUnion is associative (other direction) *)
lemma sbunion_assoc2: "(sb1 \<uplus> sb2) \<uplus> sb3 = sb1 \<uplus> (sb2 \<uplus> sb3)"
  by (simp add: sbunion_associative)

(* sbUnion keeps the equality if the respective args. (1st-1st and 2nd-2nd) are equal *)
lemma sbunion_eqI:  assumes "(a = b)" and "(c = d)"
  shows "(a \<uplus> c = b \<uplus> d)"
  by (simp add: assms(1) assms(2))

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbSetCh\<close>
(* ----------------------------------------------------------------------- *)

(* Welltyped is preserved after setting new sb_well channels. *)
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

(* Restricting b's domain to a channel set cs doesn't change well typedness *)
lemma sbrestrict_well [simp]: "sb_well (Rep_SB b |` cs)"
by (metis (no_types, lifting) domIff rep_well restrict_map_def sb_well_def)

(* Restricting the domain to a channel set cs is a monotonic function *)
lemma sbrestrict_monofun[simp]: "monofun  (\<lambda>b. Rep_SB b |` cs)"
by (smt below_SB_def fun_below_iff monofunI not_below2not_eq restrict_map_def )

(* sbRestrict is continuous on the second argument *)
lemma sbrestrict_cont1[simp]: "cont  (\<lambda>b. ((Rep_SB b) |` cs))"
apply(rule contI2)
apply(auto)
by (smt below_option_def fun_below_iff is_ub_thelub lub_eq lub_fun po_class.chain_def rep_chain rep_lub restrict_in restrict_out)

(* sbRestrict is continuous on the second argument *)
lemma sbrestrict_cont[simp]: "cont  (\<lambda>b. ((Rep_SB b) |` cs)\<Omega>)"
by (simp)

(* Insert Rule for sbRestrict *)
lemma sbrestrict_insert: "b \<bar> cs = (Rep_SB b) |` cs \<Omega>"
by(simp add: sbRestrict_def)

(* The domain of SB b restricted to channel set cs is the intersection of the old domain with cs *)
lemma sbrestrict_sbdom[simp]: "sbDom\<cdot>(b \<bar> cs) = sbDom\<cdot>b \<inter> cs"
by (simp add: sbDom_def sbrestrict_insert)

(* Restricting the SB b with a superset of it`s domain is the identity *)
lemma sbrestrict_id [simp]: assumes "sbDom\<cdot>b \<subseteq> cs" shows "b \<bar> cs = b"
using assms apply(simp add: sbrestrict_insert sbdom_insert)
by (metis (no_types, lifting) IntD2 dom_restrict inf.orderE rep_abs restrict_in sbdom_insert sbgetch_insert sbrestrict_well sb_eq)

(* Restricting to the empty channel set yields the smallest SB *)
lemma sbrestrict_least[simp]: "b \<bar> {} = sbLeast {}"
by(simp add: sbrestrict_insert sbLeast_def)

lemma sbrestrict_least2[simp]: assumes "cs \<inter>sbDom\<cdot>b = {}" shows "b \<bar> cs = sbLeast {}"
by (metis assms ex_in_conv inf_commute sbleast_sbdom sbrestrict_sbdom sb_eq)

(* sbGetch works as expected on a SB b rerstricted to a  channel set cs if c is in the cs *)
lemma sbrestrict2sbgetch[simp]: assumes "c\<in>cs"
  shows "(b\<bar>cs) . c = b. c"
by(simp add: assms sbgetch_insert sbrestrict_insert)

(* If h is continuous, then so is the composition of h with a restriction *)
lemma sbrestrict_below [simp]:  assumes "chain Y" and "cont h"
      shows "(h (\<Squnion>i. Y i) \<bar> g (sbDom\<cdot>(\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. (h (Y i) \<bar> g (sbDom\<cdot>(Y i)) ))"
by (smt assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_arg lub_eq po_eq_conv sbChain_dom_eq2)

(* sbUnion favors the second argument, restriction of a union therefore depends on this attribute *)
lemma sbunion_restrict [simp]: assumes "sbDom\<cdot>b2 = cs"
  shows "(b1 \<uplus> b2) \<bar> cs = b2"
apply(simp add: sbunion_insert sbrestrict_insert )
by (metis (no_types) Rep_SB_inverse assms map_union_restrict2 sbdom_insert)

lemma sbunion_restrict2 [simp]: assumes "sbDom\<cdot>b2 \<inter> cs = {}"
  shows "(b1 \<uplus> b2) \<bar> cs = b1 \<bar> cs" 
  apply(rule sb_eq)
   apply (simp add: Int_Un_distrib2 assms)
  using assms sbunion_getchL by fastforce

(* sbUnion and sbRestrict are distributive *)
lemma sbunion_restrict3: "(b1 \<uplus> b2) \<bar> cs = (b1 \<bar> cs) \<uplus> (b2 \<bar> cs)"
apply(simp add: sbrestrict_insert sbunion_insert)
by (metis (full_types) mapadd2if_then restrict_map_def)  
  

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRemCh\<close>
(* ----------------------------------------------------------------------- *)

(* sbRemCh is monotonic *)
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

(* sbRemCh and LUB are commutative *)
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

(* sbRemCh is continuous *)
lemma sbremch_cont[simp]: "cont (\<lambda> b. \<Lambda> c.  b \<bar> -{c})"
by(rule contI2, auto)

(* Insert rule for sbRemCh *)
lemma sbremch_insert: "sbRemCh\<cdot>b\<cdot>c =  b \<bar> -{c}"
by (simp add: sbRemCh_def)

(* The domain of an SB b where channel c was removed is the old domain minus c *)
lemma sbremch_sbdom[simp]: "sbDom\<cdot>(sbRemCh\<cdot>b\<cdot>c) = sbDom\<cdot>b - {c}"
by(simp add: sbremch_insert diff_eq)

(* From sbRemCh to sbRestrict *)
lemma sbrem2sbrestrict: "sbRemCh\<cdot>b\<cdot>c = b \<bar> (sbDom\<cdot>b - {c})"
by (smt Int_absorb1 Int_commute Int_lower2 Set.basic_monos(7) sbremch_insert sbremch_sbdom sbrestrict2sbgetch sbrestrict_sbdom sb_eq)

(* Restricting to the same channel set cs preserves below-relation *)
lemma sbres_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "(a \<bar> cs) \<sqsubseteq> (b \<bar> cs)"
  by (metis assms monofun_cfun_arg)

lemma sbres_sbdom_supset: assumes "sbDom\<cdot>sb \<subseteq> cs"
  shows "sb \<bar> cs = sb \<bar> (sbDom\<cdot>sb)"
  by (simp add: assms)
    
lemma sbres_sbdom_supset_inter: 
  shows "sb \<bar> cs = sb \<bar> (cs \<inter> (sbDom\<cdot>sb))"
  by (smt inf.right_idem inf_commute inf_sup_ord(1) sb_eq 
          sbrestrict2sbgetch sbrestrict_sbdom set_mp)
        


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRenameCh\<close>
(* ----------------------------------------------------------------------- *)

(* Renaming a channel to the same name is the identity *)
lemma sbrenamech_id: assumes "c\<in>sbDom\<cdot>b"
  shows "sbRenameCh b c c = b"
apply(simp add: sbRenameCh_def sbgetch_insert sbSetCh_def sbremch_insert sbrestrict_insert)
by (smt Rep_SB_inverse assms dom_empty dom_fun_upd fun_upd_same fun_upd_triv fun_upd_upd map_add_empty map_add_upd option.distinct(1) option.sel rep_abs rep_well restrict_complement_singleton_eq sbdom_insert sbgetchE sbrestrict_well sbunion_insert singletonD sb_well_def)





(* ----------------------------------------------------------------------- *)
  subsection \<open>sbUp\<close>
(* ----------------------------------------------------------------------- *)

(* Upping (always returning a stream, potentially empty) is a well-defined SB *)
lemma sbup_well[simp]: "sb_well (\<lambda>c. if c \<in> sbDom\<cdot>b then (Rep_SB b)c else Some \<epsilon>)"
by (smt domIff rep_well sbleast_well sb_well_def)

(* Upping is continuous *)
lemma sbup_cont1[simp]: "cont (\<lambda>b. (\<lambda> c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b)c else Some \<epsilon>))"
by (smt Prelude.contI2 below_SB_def eq_imp_below fun_below_iff is_ub_thelub lub_eq lub_fun monofunI po_class.chainE po_class.chainI rep_lub sbdom_eq sbgetchE)

lemma sbup_cont[simp]: "cont (\<lambda>b. (\<lambda> c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b)c else Some \<epsilon>)\<Omega>)"
by simp

(* Insert rule for upping *)
lemma sbup_insert: "\<up>b = (\<lambda>c. if (c\<in>sbDom\<cdot>b) then (Rep_SB b) c else Some \<bottom>)\<Omega>"
by(simp add: sbUp_def)


(* The domain of an upped SB b is the Universe *)
lemma sbup_sbdom [simp]: "sbDom\<cdot>(\<up>b) = UNIV"
apply(simp add: sbdom_insert )
apply(simp add: sbup_insert)
by (smt CollectD Collect_cong UNIV_def dom_def optionLeast_def optionleast_dom sbdom_insert)

(* sbGetch on an upped SB works as before if the channel c was in the domain before *)
lemma sbup_sbgetch[simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "\<up>b . c = b .c"
by (simp add: assms sbgetch_insert sbup_insert)

(* sbGetch on an upped SB returns the empty stream \<epsilon> if the channel c was not in the domain before *)
lemma sbup_sbgetch2[simp]: assumes "c\<notin>sbDom\<cdot>b"
  shows "\<up>b . c = \<epsilon>"
by (simp add: assms sbgetch_insert sbup_insert)

(* Upping any sbLeast yields an SB that always returns the empty stream \<epsilon> *)
lemma [simp]: "\<up>(sbLeast cs) . c = \<epsilon>"
by (metis sbleast_getch sbleast_sbdom sbup_sbgetch sbup_sbgetch2)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbEqSelected\<close>
(* ----------------------------------------------------------------------- *)

(* Restricted to the empty channel set {}, two SBs b1 and b2 are always equal*)
lemma [simp]: "sbEqSelected {} b1 b2"
by(simp add: sbEqSelected_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbEqCommon\<close>
(* ----------------------------------------------------------------------- *)

(* Two SBs b1 and b2 that have no common channels are always equal on their common channels *)
lemma assumes "sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2 = {}"
  shows "sbEqCommon b1 b2"
by(simp add: sbEqCommon_def assms)



(* ----------------------------------------------------------------------- *)
  subsection \<open>SB\<close>
(* ----------------------------------------------------------------------- *)

(* sbLeast exists *)
lemma sb_exists[simp]: "(sbLeast cs)\<in>(cs^\<Omega>)"
by (simp add: SB_def)

(* All 'm SBs in cs^\<Omega> have the domain cs *)
lemma sb_sbdom[simp]: "sbDom\<cdot>(SOME b. b \<in> cs^\<Omega>) = cs"
by (metis (mono_tags, lifting) SB_def mem_Collect_eq sb_exists someI_ex)

(* sbLeast {} is the only  SB with empty domain *)
lemma sb_empty: "{}^\<Omega> = {sbLeast {} }"
apply(simp add: SB_def sbdom_insert sbLeast_def)
apply rule
apply (metis (mono_tags, lifting) Rep_SB_inverse mem_Collect_eq singleton_iff subsetI)
by auto





(* ----------------------------------------------------------------------- *)
  subsection \<open>sbConc\<close>
(* ----------------------------------------------------------------------- *)

(* Concatenation is a well-defined SB *)
lemma sbconc_well[simp]: "sb_well (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>b2. c))) "
apply(rule sb_wellI)
apply(simp add: sbdom_insert )
by (smt UNIV_I Un_least dual_order.trans rep_well sb_well_def sbdom_insert sbgetch_insert sbup_sbdom sconc_sdom)

(* From here: coninuity proof for sbConc *)
lemma sbconct_mono1[simp]: "monofun (\<lambda>b2. (\<lambda>c. Some ((\<up>b1. c) \<bullet> (\<up>b2. c))))"
apply(rule monofunI)
by (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun) 

(* Helper function to proof continuity *)
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

(* Concatenation is continuous *)
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

(* Insert rule for sbConc *)
lemma sbconc_insert: "b1 \<bullet> b2 = ((\<lambda>c. Some ((\<up>b1. c) \<bullet> \<up>b2. c))\<Omega>) \<bar> (sbDom\<cdot>b1 \<union> sbDom\<cdot>b2)"
by (simp add: sbConc_def)

(* Concatenation of SB b1 and b2 results in the domain being the union of the domains of b1 and b2 *)
lemma sbconc_sbdom[simp]: "sbDom\<cdot>(b1 \<bullet> b2) = sbDom\<cdot>b2 \<union> sbDom\<cdot>b1"
apply(simp add:  sbconc_insert sbrestrict_sbdom)
apply(simp add: sbdom_insert)
by blast

(* Helper lemma, used in the lemma below *)
lemma sbup_restrict_id [simp]: assumes "c\<in>sbDom\<cdot>b2"
  shows "(((\<lambda>c. Some (\<up>b2 . c))\<Omega>)\<bar>sbDom\<cdot>b2) . c = b2 . c"
by (smt Abs_cfun_inverse2 UNIV_I assms rep_abs restrict_in sbDom_def sbdom_cont sbgetchE sbgetch_insert sbrestrict_insert sbrestrict_well sbup_insert sbup_sbdom sbup_well sb_well_def)

lemma [simp]: assumes "c\<in>sbDom\<cdot>b2"
  shows "((\<lambda>c. Some (\<up>b2 . c))\<Omega>) . c = b2 . c"
using assms sbup_restrict_id by fastforce

(* The empty 'm SB (with a subset of channels) concatinated to the left is the identity *)
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

(* The empty 'm SB (with a subset of channels) concatinated to the right is the identity *)
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

(* Concatenating with the empty SB is the identity *)
lemma sbconc_idLempty [simp]: "(empty \<Omega>) \<bullet> b2 = b2"
using sbconc_idL sbleast_empty by (metis empty_subsetI)

lemma sbconc_idRempty [simp]: "b1 \<bullet> (empty \<Omega>) = b1"
using sbconc_idR sbleast_empty by (metis empty_subsetI)

(* sbGetch is distributive with sbConc if the channel c is part of both domains *)
lemma sbconc_sbgetch: assumes "c\<in>(sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2)"
  shows "(b1 \<bullet> b2) .c = (b1 .c)\<bullet>(b2. c)"
using assms sbconc_insert sbconc_well sbgetch_insert sbrestrict2sbgetch sbup_sbgetch 
  by (smt Int_ac(3) Int_lower2 UnCI option.sel rep_abs subsetCE)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbConcCommon\<close>
(* ----------------------------------------------------------------------- *)

(* sbConcCommon is a continuous function *)
lemma sbconccommon_cont[simp]: "cont (\<lambda> b2. (b1 \<bullet> b2)\<bar>sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2)"
by (metis (no_types) cont_restrict_sbdom)

(* Insert rule for sbConcCommon *)
lemma sbconccommon_insert: "sbConcCommon b1\<cdot>b2 =  (b1 \<bullet> b2)\<bar>sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2"
by(simp add: sbConcCommon_def)

(* sbConcCommon is equivalent to filtering each SB by the other and then concatenating *)
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

(* sbMapStream is well-typed, if the function f preserves the well-typed property *)
lemma sbmapstream_well[simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))"
  shows "sb_well (\<lambda>c. (c \<in> sbDom\<cdot>b)\<leadsto>f (b. c))"
by (smt Abs_cfun_inverse2 assms domIff option.sel rep_well sbDom_def sb_well_def sbdom_cont sbgetch_insert)

(* The domain is identical after sbMapStream, if the function f preserves the well-typed property *)
lemma sbmapstream_dom [simp]: assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))" 
  shows "sbDom\<cdot>(sbMapStream f b) = sbDom\<cdot>b"
by (smt Abs_cfun_inverse2 Collect_cong assms domI domIff dom_def option.sel rep_abs rep_well sbDom_def sbMapStream_def sb_well_def sbdom_cont sbgetch_insert)

(* Assuming the channel c is in the domain, sbMapStream and sbGetch are commutative *)
lemma sbmapstream_sbgetch [simp]: assumes"\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(f s)\<subseteq>(ctype c))" and "c\<in>sbDom\<cdot>b"
  shows "(sbMapStream f b) . c = f (b .c)"
by (simp add: assms(1) assms(2) sbMapStream_def sbgetch_insert)

(* sbMapStream is continuous, if the function f preserves the well-typed property *)
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

(* sbTake is continuous *)
lemma sbtake_cont [simp]:"cont (\<lambda>b. sbMapStream (\<lambda>s. stake n\<cdot>s) b)"
by (simp)

(* Insert rule for sbTake *)
lemma sbtake_insert: "sbTake n\<cdot>b \<equiv>  sbMapStream (\<lambda>s. stake n\<cdot>s) b"
by(simp add: sbTake_def)

(* Taking zero elements yields the smallest SB (sbLeast) with the same domain *)
lemma sbtake_zero: "sbTake 0\<cdot>In = sbLeast (sbDom\<cdot>In)"
by(simp add: sbtake_insert sbMapStream_def sbLeast_def)

(* The domain stays the same *)
lemma sbtake_sbdom[simp]: "sbDom\<cdot>(sbTake n\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbtake_insert)

(* Assuming the channel c is in the domain of the SB b, sbTake and sbGetCh are commutative *)
lemma sbtake_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "sbTake n\<cdot>b . c = stake n\<cdot>(b .c)"
using assms by(simp add: sbtake_insert)

(* Taking n from SB b yields a smaller (below, \<sqsubseteq>) SB than taking n+1 *)
lemma sbtake_below [simp]: "sbTake n\<cdot>b \<sqsubseteq> sbTake (Suc n)\<cdot>b"
by (metis eq_imp_le le_Suc_eq sbtake_sbdom sbtake_sbgetch stake_mono sb_below)

(* Taking increasingly more from an SB b yields a chain of SBs *)
lemma sbtake_chain [simp]: "chain (\<lambda>n. sbTake n\<cdot>b)"
by (simp add: po_class.chainI)

(* Assuming the channel c is in the domain of SB b, sbGetch/LUB and sbTake are commutative *)
lemma sbtake_lub_sbgetch: assumes "c\<in>sbDom\<cdot>b"
  shows "(\<Squnion>n. sbTake n\<cdot>b) . c = (\<Squnion>n. stake n\<cdot>(b . c))"
by (metis (mono_tags, lifting) assms lub_eq lub_eval po_class.chainI sbgetch_insert sbtake_below sbtake_sbgetch)

(* The LUB of sbTake on an SB b is b itself *)
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

(* Applying sbHd yields the same domain as before *)
lemma sbhd_sbdom[simp]: "sbDom\<cdot>(sbHd\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbHd_def)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbDrop\<close>
(* ----------------------------------------------------------------------- *)

(* sbDrop is continuous *)
lemma sbdrop_cont [simp]:"cont (\<lambda>b. sbMapStream (\<lambda>s. sdrop n\<cdot>s) b)"
by simp

(* Insert rule for sbDrop *)
lemma sbdrop_insert: "sbDrop n\<cdot>b = sbMapStream (\<lambda>s. sdrop n\<cdot>s) b"
by(simp add: sbDrop_def)

(* Dropping zero elements is the identity *)
lemma sbdrop_zero[simp]: "sbDrop 0\<cdot>b = b"
by(simp add: sbdrop_insert sbMapStream_def)

(* Dropping does not change the domain *)
lemma sbdrop_sbdom[simp]: "sbDom\<cdot>(sbDrop n\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbdrop_insert)

(* Assuming the channel c is in the domain of SB b, sbDrop and sbGetch are commutative *)
lemma sbdrop_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "sbDrop n\<cdot>b . c = sdrop n\<cdot>(b .c)"
using assms by(simp add: sbdrop_insert)

(* Taking the first n of SB b, then dropping the first n of b and concatenating both yields b *)
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

(* Applying sbDrop twice is the same as dropping the sum of the two counts *)
lemma sbdrop_plus [simp]: "sbDrop n\<cdot>(sbDrop k\<cdot>sb) = sbDrop (n+k)\<cdot>sb"
  apply(rule sb_eq)
   apply simp
  apply(simp add: sbDrop_def)
  by (simp add: sdrop_plus)






(* ----------------------------------------------------------------------- *)
  subsection \<open>sbRt\<close>
(* ----------------------------------------------------------------------- *)

(* sbRt does not change the domain *)
lemma sbrt_sbdom[simp]: "sbDom\<cdot>(sbRt\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbRt_def)

(* Concatenating sbHd and sbRt is the identity*)
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

(* Assuming the channel c is in the domain of SB b, sbInfTimes and sbGetch are commutative *)
lemma sbinftimes_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows "(sbInfTimes b) . c = sinftimes (b . c)"
using assms by(simp add: sbInfTimes_def)

(* The domain stays the same *)
lemma sbinftimes_sbdom [simp]: "sbDom\<cdot>(b\<infinity>) = sbDom\<cdot>b"
by(simp add: sbInfTimes_def)

(* The LUB of concatenating a SB b with itself n times in sbInfTimes of b *)
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

(* Applying f to the SB b does not change the domain, assuming f preserves the well-typedness  *)
lemma assumes "\<forall>c s. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>((\<lambda>s. smap f\<cdot>s) s)\<subseteq>(ctype c))"
  shows "sbDom\<cdot>(sbMap f\<cdot>b) = sbDom\<cdot>b"
by(simp add: sbMap_def assms)



(* ----------------------------------------------------------------------- *)
  subsection \<open>sbFilter\<close>
(* ----------------------------------------------------------------------- *)

(* Filtering does not change the domain *)
lemma sbfilter_sbdom [simp]: "sbDom\<cdot>(sbFilter A\<cdot>b) = sbDom\<cdot>b"
by (smt Abs_cfun_inverse2 cont_Rep_cfun2 sbFilter_def sbfilter_sbdom sbmapstream_cont sbmapstream_dom subsetCE subsetI)

(* Assuming the channel c is in the domain of SB b, sbFilter and sbGetch are commutative *)
lemma sbfilter_sbgetch [simp]: assumes "c\<in>sbDom\<cdot>b"
  shows  "(sbFilter A\<cdot>b) . c = sfilter A\<cdot>(b .c)"
apply(simp add: sbFilter_def assms)
by (meson Streams.sbfilter_sbdom assms sbmapstream_sbgetch subsetCE subsetI)


(* ----------------------------------------------------------------------- *)
  subsection \<open>if_then\<close>
(* ----------------------------------------------------------------------- *)

(* Domain of if-then construct works as expected for constructing SBs *)
lemma if_then_dom[simp]: "dom (\<lambda>c. (c \<in> cs)\<leadsto>b .c) = cs"
using dom_def by fastforce

(* The if-then construct yields well-typed SBs, if the channel in the if-condition is in the domain *)
lemma if_then_well[simp]: assumes "cs\<subseteq>sbDom\<cdot>b" shows "sb_well (\<lambda>c. (c\<in>cs) \<leadsto> (b .c))"
using assms apply(simp add: sb_well_def sbgetch_insert sbdom_insert)
  using rep_well sb_well_def by blast

(* Additionals lemmata concerning continuity, monotonicity, domain and chains *)

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

(* ----------------------------------------------------------------------- *)
  subsection \<open>sbLen\<close>
(* ----------------------------------------------------------------------- *)  

lemma sbLen_set_below: assumes "\<forall>b\<in>{(y  .  c) |c. c \<in> sbDom\<cdot>y}. \<exists>a\<in>{(x  .  c) |c. c \<in> sbDom\<cdot>x}. (#a) \<sqsubseteq> (#b)"
  shows "\<forall>b\<in>{#(y  .  c) |c. c \<in> sbDom\<cdot>y}. \<exists>a\<in>{#(x  .  c) |c. c \<in> sbDom\<cdot>x}. a \<sqsubseteq> b"
    using assms by fastforce    

lemma sbLen_below: assumes "a \<sqsubseteq> b" shows "\<forall>c\<in>sbDom\<cdot>a. #(a. c) \<le> #(b . c)"   
by (simp add: assms mono_slen monofun_cfun_arg monofun_cfun_fun)

lemma lnat_set_least_below_sb: assumes "(A :: lnat set) \<noteq> {}" and "(B :: lnat set) \<noteq> {}"
  and "\<forall> a \<in> A . \<exists> b \<in> B.  a \<sqsubseteq> b" and "\<forall> b \<in> B. \<exists> a \<in> A. a \<sqsubseteq> b"
shows "(LEAST ln. ln \<in> A) \<sqsubseteq> (LEAST ln. ln \<in> B)"
  by (metis (no_types, lifting) LeastI Least_le all_not_in_conv assms(2) assms(4) lnle_conv rev_below_trans)  
  
lemma sbLen_mono_pre: assumes "x \<sqsubseteq> y" shows 
  "(if sbDom\<cdot>x \<noteq> {} then LEAST ln. ln \<in> { #(x. c) | c. c \<in> sbDom\<cdot>x} else \<infinity>) \<sqsubseteq>
   (if sbDom\<cdot>y \<noteq> {} then LEAST ln. ln \<in> { #(y. c) | c. c \<in> sbDom\<cdot>y} else \<infinity>)" 
proof(cases "sbDom\<cdot>x \<noteq> {}")
  case True
  have f1: "sbDom\<cdot>y = sbDom\<cdot>x"
    using assms sbdom_eq by auto
  have f2: "\<forall>b\<in>{(y . c) |c. c \<in> sbDom\<cdot>y}. \<exists>a\<in>{(x . c) |c. c \<in> sbDom\<cdot>x}. (a) \<sqsubseteq> (b) 
          \<Longrightarrow> \<forall>b\<in>{(y . c) |c. c \<in> sbDom\<cdot>y}. \<exists>a\<in>{(x . c) |c. c \<in> sbDom\<cdot>x}. (#a) \<sqsubseteq> (#b)"
    by (meson monofun_cfun_arg)
  have f3: "(LEAST ln. ln \<in> {#(x . c) |c. c \<in> sbDom\<cdot>x}) \<sqsubseteq> (LEAST ln. ln \<in> {#(y . c) |c. c \<in> sbDom\<cdot>y})"
    apply (rule lnat_set_least_below_sb)  
    apply (simp add: True)
    apply (simp add: True f1)
    using assms f1 sbLen_below apply fastforce
    using assms f1 sbLen_below by fastforce
  show ?thesis 
    using f1 f3 by auto
next
  case False
  have f1: "sbDom\<cdot>y = sbDom\<cdot>x"
    using assms sbdom_eq by auto
  then show ?thesis 
    by(simp add: False)
qed  
    
lemma sbLen_mono[simp]: "monofun (\<lambda> b. if sbDom\<cdot>b \<noteq> {} then LEAST ln. ln \<in> { #(b. c) | c. c \<in> sbDom\<cdot>b} else \<infinity>)"
  using monofun_def sbLen_mono_pre by blast  

lemma sbLen_chain: assumes "chain Y" and "\<And> i. sbDom\<cdot>(Y i) \<noteq> {}" shows 
  "chain (\<lambda> i. if sbDom\<cdot>(Y i) \<noteq> {} then LEAST ln. ln \<in> { #((Y i). c) | c. c \<in> sbDom\<cdot>(Y i)} else \<infinity>)"
  apply(simp only: chain_def)
  apply(subst sbLen_mono_pre)
  using assms(1) po_class.chainE apply auto[1]
  by auto

lemma sbLen_conv: "(LEAST ln. \<exists>c. ln = #(sb . c) \<and> c \<in> sbDom\<cdot>sb) = (LEAST ln. ln \<in> { #(sb . c) | c. c \<in> sbDom\<cdot>sb})"
  by auto
    
lemma sbLen_chain2: assumes "chain Y" and "\<And> i. sbDom\<cdot>(Y i) \<noteq> {}" shows
  "chain (\<lambda> i. (LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i)))"
proof - 
  fix i
  have f1: "\<forall>i. (LEAST ln. ln \<in> {#(Y i . c) |c. c \<in> sbDom\<cdot>(Y i)}) \<sqsubseteq> (LEAST ln. ln \<in> {#(Y (Suc i) . c) |c. c \<in> sbDom\<cdot>(Y (Suc i))})"
  proof
    fix i
    show "(LEAST ln. ln \<in> {#(Y i . c) |c. c \<in> sbDom\<cdot>(Y i)}) \<sqsubseteq> (LEAST ln. ln \<in> {#(Y (Suc i) . c) |c. c \<in> sbDom\<cdot>(Y (Suc i))})"
      apply (rule lnat_set_least_below_sb)  
      using assms(2) apply auto[1]
      using assms(2) apply auto[1]
      using assms(1) po_class.chainE sbLen_below sbdom_eq apply fastforce
      using assms(1) po_class.chainE sbLen_below sbdom_eq by fastforce
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
  
lemma sbLen_cont_pre: assumes "chain Y" and "finite (sbDom\<cdot>(Lub Y))" shows 
  "(if sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {} then LEAST ln. ln \<in> { #((\<Squnion>i. Y i). c) | c. c \<in> sbDom\<cdot>(\<Squnion>i. Y i)} else \<infinity>) \<sqsubseteq>
   (\<Squnion>i. if sbDom\<cdot>(Y i) \<noteq> {} then LEAST ln. ln \<in> { #((Y i). c) | c. c \<in> sbDom\<cdot>(Y i)} else \<infinity>)"
proof (cases "sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {}")
  case True
  hence f1: "\<forall> i. sbDom\<cdot>(Y i) = sbDom\<cdot>(\<Squnion>i. Y i)"
    using assms(1) sbChain_dom_eq2 by auto
  hence f10: "\<forall> i. sbDom\<cdot>(\<Squnion>i. Y i) =  sbDom\<cdot>(Y i)"
    by simp
  hence f11: "\<forall> i. sbDom\<cdot>(Y i) \<noteq> {}"
    using True by auto
  show ?thesis 
    apply(simp only: True f11)
    apply(auto)
    proof (cases "finite_chain Y")
      case True
      obtain maxI where f21: "max_in_chain maxI Y"
        using True finite_chain_def by auto
      have f22: "\<forall>j. maxI \<le> j \<longrightarrow> (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI)) = (LEAST ln. \<exists>c. ln = #(Y j . c) \<and> c \<in> sbDom\<cdot>(Y j))"
      proof -
        { fix nn :: nat
          { assume "Y nn \<noteq> Y maxI"
            then have "\<not> maxI \<le> nn \<or> (LEAST l. \<exists>c. l = #(Y nn . c) \<and> c \<in> sbDom\<cdot>(Y nn)) = (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI))"
              by (metis f21 max_in_chain_def) }
          then have "\<not> maxI \<le> nn \<or> (LEAST l. \<exists>c. l = #(Y nn . c) \<and> c \<in> sbDom\<cdot>(Y nn)) = (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI))"
            by fastforce }
        then show ?thesis
          by presburger
      qed
      have f221: "max_in_chain maxI (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i))"
        by (simp add: f22 max_in_chainI)
      have f23: "(\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i)) = (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI))"
        using maxinch_is_thelub assms(1) sbLen_chain2 f221 f11 by fastforce
      show "(LEAST ln. \<exists>c. ln = #(Lub Y . c) \<and> c \<in> sbDom\<cdot>(Lub Y)) \<le> (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i))" 
        using assms(1) f21 f23 maxinch_is_thelub by fastforce
    next
      case False 
      then show"(LEAST ln. \<exists>c. ln = #(Lub Y . c) \<and> c \<in> sbDom\<cdot>(Lub Y)) \<le> (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i))"
      proof(cases "finite_chain (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i))")
        case True
        then have f31: "\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i))"
          using finite_chain_def by auto    
        then obtain maxI where f32: "\<forall>j. maxI \<le> j \<longrightarrow> (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI)) = (LEAST ln. \<exists>c. ln = #(Y j . c) \<and> c \<in> sbDom\<cdot>(Y j))"
          by (meson max_in_chain_def)
        then obtain maxCount where f33: "maxCount = (LEAST ln. \<exists>c. ln = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI))"
          by blast
        then have f34: "maxCount = (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i . c) \<and> c \<in> sbDom\<cdot>(Y i))"
          by (metis (mono_tags, lifting) True f32 finite_chainE l42 le_cases max_in_chainI3 max_in_chain_def)
        have f35: "finite (sbDom\<cdot>(Lub Y))"  
          using assms by blast    
        have f36: "\<exists> maxCh \<in> sbDom\<cdot>(Lub Y). \<forall>j\<ge>maxI. maxCount = #(Y j . maxCh)"
        proof(rule ccontr)
          assume "\<not>?thesis"
          then have f361: "\<forall> ch1 \<in> sbDom\<cdot>(Lub Y). \<exists>j\<ge>maxI. maxCount < #(Y j . ch1)"
          proof -
            obtain nn :: "channel \<Rightarrow> nat" where
              f1: "\<forall>c. c \<notin> sbDom\<cdot>(Lub Y) \<or> maxI \<le> nn c \<and> maxCount \<noteq> #(Y (nn c) . c)"
              using \<open>\<not> (\<exists>maxCh\<in>sbDom\<cdot>(Lub Y). \<forall>j\<ge>maxI. maxCount = #(Y j . maxCh))\<close> by moura
            obtain cc :: channel where
              "(\<exists>v0. v0 \<in> sbDom\<cdot>(Lub Y) \<and> (\<forall>v1. \<not> maxI \<le> v1 \<or> \<not> maxCount < #(Y v1 . v0))) = (cc \<in> sbDom\<cdot>(Lub Y) \<and> (\<forall>v1. \<not> maxI \<le> v1 \<or> \<not> maxCount < #(Y v1 . cc)))"
              by blast
            moreover
            { assume "cc \<in> sbDom\<cdot>(Y (nn cc))"
              then have "\<not> #(Y (nn cc) . cc) < (LEAST l. \<exists>c. l = #(Y (nn cc) . c) \<and> c \<in> sbDom\<cdot>(Y (nn cc)))"
                using not_less_Least by blast
              moreover
              { assume "\<not> #(Y (nn cc) . cc) < (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI))"
                moreover
                { assume "\<not> #(Y (nn cc) . cc) < (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI)) \<and> \<not> (LEAST l. \<exists>c. l = #(Y maxI . c) \<and> c \<in> sbDom\<cdot>(Y maxI)) < #(Y (nn cc) . cc)"
                  then have "cc \<notin> sbDom\<cdot>(Lub Y)"
                    using f1 f33 neq_iff by blast }
                ultimately have "cc \<in> sbDom\<cdot>(Lub Y) \<longrightarrow> (cc \<notin> sbDom\<cdot>(Lub Y) \<or> (\<exists>n\<ge>maxI. maxCount < #(Y n . cc))) \<or> \<not> maxI \<le> nn cc \<or> maxCount = #(Y (nn cc) . cc)"
                  using f33 by blast }
              ultimately have "cc \<in> sbDom\<cdot>(Lub Y) \<longrightarrow> (cc \<notin> sbDom\<cdot>(Lub Y) \<or> (\<exists>n\<ge>maxI. maxCount < #(Y n . cc))) \<or> \<not> maxI \<le> nn cc \<or> maxCount = #(Y (nn cc) . cc)"
                using f32 by presburger
              then have "cc \<in> sbDom\<cdot>(Lub Y) \<longrightarrow> cc \<notin> sbDom\<cdot>(Lub Y) \<or> (\<exists>n\<ge>maxI. maxCount < #(Y n . cc))"
                using f1 by blast }
            ultimately show ?thesis
              using assms(1) sbChain_dom_eq2 by blast
          qed
          show "False" 
          proof(cases "card (sbDom\<cdot>(Lub Y))")
            case 0
            then show ?thesis 
              using f10 f11 f35 by auto
          next
            case (Suc nat)
            then have i1: "card (sbDom\<cdot>(Lub Y)) = Suc nat"
              by blast
            show ?thesis
            proof - 
              obtain n where i2: "card (sbDom\<cdot>(Lub Y)) = n"
                by blast
              then have i3: "n > 0"    
                by (simp add: i1) 
                 
              obtain f where i4: "sbDom\<cdot>(Lub Y) = f ` {i::nat. i < n}"
                by (metis card_Collect_less_nat card_image f35 finite_imp_nat_seg_image_inj_on i2)   
              then have i5: "\<forall>i<n. \<exists>j\<ge>maxI. maxCount < #(Y j . (f i))"
                using f361 by blast

              then obtain x where i6: "x = Max {(LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) | i::nat. i < n}"
                by blast
              have i7: "\<forall>i<n. \<exists>m. (m = (LEAST x. x\<ge>maxI \<and> (maxCount < #(Y x . (f i)))) \<and> m\<ge>maxI \<and> (maxCount < #(Y m . (f i))))"    
                by (metis (no_types, lifting) LeastI i5)
              have i0: "sbDom\<cdot>(Lub Y) = sbDom\<cdot>(Y x)"    
                by (simp add: assms(1) sbChain_dom_eq2)  
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
              then have i02: "\<forall>ch1\<in>sbDom\<cdot>(Lub Y). maxCount < #(Y x . ch1)"
                by (simp add: i4)
              then have i8: "maxCount < (LEAST ln. \<exists>c. ln = #(Y x  .  c) \<and> c \<in> sbDom\<cdot>(Y x))"
              proof - 
                have "sbDom\<cdot>(Y x) \<noteq> {}"
                  using f11 by auto
                then have "\<exists>ch1\<in>sbDom\<cdot>(Y x). (LEAST ln. \<exists>c. ln = #(Y x  .  c) \<and> c \<in> sbDom\<cdot>(Y x)) = #(Y x . ch1)"
                  by (smt Collect_empty_eq LeastI all_not_in_conv assms(1) f11 f33 sbchain_dom_eq)
                then show ?thesis
                  using i0 i02 by auto
              qed
              then have i9: "maxCount < (\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i))"
              proof -
                have "\<exists>l. l \<sqsubseteq> (\<Squnion>n. LEAST l. \<exists>c. l = #(Y n . c) \<and> c \<in> sbDom\<cdot>(Y n)) \<and> maxCount < l"
                  using True finite_chain_def i8 is_ub_thelub by blast
                then show ?thesis
                  using less_le_trans lnle_def by blast
              qed
              then show ?thesis
                using f34 by auto
            qed  
          qed
        qed
        then obtain maxCh where f37: "maxCh \<in> sbDom\<cdot>(Lub Y) \<and> (\<forall>j\<ge>maxI. maxCount = #(Y j . maxCh))"
          by blast
        then have f38: "\<forall>j\<ge>maxI. #(Y j . maxCh) = (LEAST ln. \<exists>c. ln = # (Y j . c) \<and> c \<in> sbDom\<cdot>(Y j))"
          by (simp add: f32 f33)
        have f39: "maxCh \<in> sbDom\<cdot>(Lub Y) \<and> (\<forall> j. \<forall> ch2 \<in> sbDom\<cdot>(Lub Y). (maxI \<le> j) \<longrightarrow> ((#(Y j . maxCh)) \<sqsubseteq> (#(Y j .  ch2))))"    
          by (smt Least_le assms(1) f37 f38 lnle_conv sbChain_dom_eq2)     
        have f40: "(\<Squnion>i. LEAST ln. \<exists>c. ln = # (Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i)) = (\<Squnion>i.  (# (Y i  .  maxCh)))"
          apply(subst chains_lub_eq_sb, simp_all)
          using True finite_chain_def apply auto[1]
           apply (simp add: assms(1))
            using f38 by fastforce
        show ?thesis 
          apply(subst f40)
        proof -
          have f1: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'a stream)::lnat) = (\<Squnion>n. c\<cdot>(f n))"
            using contlub_cfun_arg by blast
          have f2: "sbGetCh\<cdot>(Lub Y) = (\<Squnion>n. sbGetCh\<cdot>(Y n))"
            using assms(1) contlub_cfun_arg by blast
          have "\<forall>f c. \<not> chain f \<or> (Lub f\<cdot>(c::channel)::'a stream) = (\<Squnion>n. f n\<cdot>c)"
            using contlub_cfun_fun by blast
          then have "(\<Squnion>n. #(Y n . maxCh)) = #(Lub Y . maxCh)"
            using f2 f1 by (simp add: assms(1))
          then have "\<exists>c. (\<Squnion>n. #(Y n . maxCh)) = #(Lub Y . c) \<and> c \<in> sbDom\<cdot>(Lub Y)"
            by (meson f37)
          then show "(LEAST l. \<exists>c. l = #(Lub Y . c) \<and> c \<in> sbDom\<cdot>(Lub Y)) \<le> (\<Squnion>n. #(Y n . maxCh))"
            by (simp add: Least_le)
        qed
      next
        case False
        then have f41: "\<not>(\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i)))"
          using assms(1) f11 finite_chain_def sbLen_chain2 by auto
        have f42: "\<forall>i. \<exists>j\<ge>i. (LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i)) < (LEAST ln. \<exists>c. ln = #(Y j  .  c) \<and> c \<in> sbDom\<cdot>(Y j))"
        proof(rule ccontr)
          assume a0: "\<not>?thesis"
          then have "\<exists>i. \<forall>j\<ge>i. (LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i)) = ( LEAST ln. \<exists>c. ln = #(Y j  .  c) \<and> c \<in> sbDom\<cdot>(Y j))"
          proof - 
            have "chain (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i))"
              by (simp add: assms(1) f11 sbLen_chain2)
            thus ?thesis
              using  a0 chain_mono_sb by fastforce
          qed
          then have "\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i))" 
            by (meson max_in_chainI)
          then show "False" 
            using f41 by blast
        qed      
        then have "(\<Squnion>i. LEAST ln. \<exists>c. ln = #(Y i  .  c) \<and> c \<in> sbDom\<cdot>(Y i)) = \<infinity>"
          using False assms(1) f11 sbLen_chain2 unique_inf_lub by blast
        then show ?thesis 
          by simp
      qed  
    qed 
next
  case False
  have f0: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> sbDom\<cdot>y = sbDom\<cdot>x"
    using assms sbdom_eq by auto
  show ?thesis 
    using False assms(1) sbChain_dom_eq2 by fastforce
qed

lemma sbLen_cont[simp]: "cont (\<lambda> b. if sbDom\<cdot>b \<noteq> {} then LEAST ln. ln \<in> { #(b. c) | c. c \<in> sbDom\<cdot>b} else \<infinity>)"  
proof - 
  have f1: "\<forall>sb. finite (sbDom\<cdot>sb)"
    sorry
  show ?thesis
    apply (rule contI2)
    apply simp
    using f1 sbLen_cont_pre by blast
qed

  
(* ----------------------------------------------------------------------- *)
  subsection \<open>sbHdElem\<close>
(* ----------------------------------------------------------------------- *)    

lemma sbHdElem_mono: "monofun (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
proof(rule monofunI) 
  fix x y ::"'a SB"
  assume "x \<sqsubseteq> y"
  then show "(\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) x \<sqsubseteq> (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) y"
    by (smt \<open>x \<sqsubseteq> y\<close> cont_pref_eq1I fun_below_iff monofun_cfun_fun po_eq_conv sbdom_eq some_below)
qed  
  
lemma sbHdElem_cont_pre: assumes "chain Y" shows "(\<lambda>c. (c \<in> sbDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> sbDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)))"
proof - 
  fix c
  have "(\<lambda>c. (c \<in> sbDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) c \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> sbDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)) c)"
  proof(cases "c \<in> sbDom\<cdot>(\<Squnion>i. Y i)")
    case True
    have f1: "\<And>i. sbDom\<cdot>(\<Squnion>i. Y i) =  sbDom\<cdot>(Y i)"
      by (simp add: assms sbChain_dom_eq2)
    then show ?thesis 
      apply(simp add: True)
    proof -
      have "Some (lshd\<cdot>(\<Squnion>n. Y n . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (metis assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR if_then_lub)
      then show "Some (lshd\<cdot>(Lub Y . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (simp add: assms sbgetch_lub)
    qed
  next
    case False
    then show ?thesis 
      using assms sbChain_dom_eq2 by fastforce
  qed  
  then show ?thesis
    by (smt assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun fun_below_iff if_then_lub is_ub_thelub lub_eq lub_fun monofun_cfun_arg monofun_cfun_fun po_class.chain_def po_eq_conv sbChain_dom_eq2 some_below)
qed  
    
lemma sbHdElem_cont: "cont (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
  apply(rule contI2)
  by(simp_all add: sbHdElem_mono sbHdElem_cont_pre)



end


