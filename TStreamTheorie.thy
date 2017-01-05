(*  Title:        TStreamTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Definition of "Timed Streams"
*)

chapter {* Timed Streams *} 

theory TStreamTheorie

imports  Streams
begin
default_sort countable


(* ----------------------------------------------------------------------- *)
section {* Type definition *}
(* ----------------------------------------------------------------------- *)


text {* Definition of  datatype  @{text "'m event"}; extends @{text "'m"} with a @{term "Tick"}. *}
datatype 'm event = Msg 'm | Tick

text {* Prove that datatype event is countable. Needed, since the domain-constructor defined
 to work for countable types.*}
instance event :: (countable) countable
by countable_datatype



text {* Introduce symbol for ticks (@{text "\<surd>"}), marks the end of each time slot. *}
syntax
  "@Tick"     :: "'a event"       ("\<surd>")

translations
  "\<surd>"  == "CONST Tick"



(* Lemmas used for PCPO-definition *)


(* Every infinite chain Y in which every element ends with "\<surd>" (and is finite)
      has a Lub with infinitly many \<surd>'s   *)
lemma tstream_well_fin_adm: assumes "chain Y" and "\<not> finite_chain Y"
    and "\<forall>i. (#(Y i)<\<infinity> \<and> (\<exists>x. (Y i) = x\<bullet>\<up>\<surd>))"
  shows " #(sfilter {\<surd>}\<cdot>(\<Squnion>i. Y i)) = \<infinity>" 
proof -
  have f1:"\<forall>i. #(Y i) < \<infinity>" using LNat.inf_chainl2 assms(1) assms(2) eq_less_and_fst_inf lnless_def by auto
  hence f2: "#(\<Squnion>i. Y i) = \<infinity>"
    by (simp add: assms(1) assms(2) inf_chainl4)
  have "\<And>i j. i\<le>j \<Longrightarrow> Y i\<noteq> Y j \<Longrightarrow> #(sfilter {\<surd>}\<cdot>(Y i)) < #(sfilter {\<surd>}\<cdot>(Y j))" 
  proof -
    fix i j
    assume "i\<le>j" and "Y i \<noteq> Y j"
    hence "Y i\<sqsubseteq> Y j" by (simp add: assms(1) po_class.chain_mono)
    obtain n where "Fin n = # (Y j)" by (metis f1 lncases lnless_def) 
    have "#(Y i) < #(Y j)"
      using \<open>Y i \<noteq> Y j\<close> \<open>Y i \<sqsubseteq> Y j\<close> eq_slen_eq_and_less lnless_def monofun_cfun_arg by blast
    obtain s where s_def: "Y j =  s \<bullet> \<up>\<surd>" by (metis \<open>Y i \<noteq> Y j\<close> \<open>Y i \<sqsubseteq> Y j\<close> assms(3) bottomI sfoot2)
    hence "Y i\<sqsubseteq>s" using \<open>Y i \<noteq> Y j\<close> \<open>Y i \<sqsubseteq> Y j\<close> below_conc by auto
    hence "#({\<surd>} \<ominus> Y i) \<le> #({\<surd>} \<ominus> s)" by (simp add: mono_slen monofun_cfun_arg)
    have f1:"#({\<surd>} \<ominus> s) \<le> #({\<surd>} \<ominus> (Y j))" by (simp add: mono_slen monofun_cfun_arg s_def) 
    thus "#({\<surd>} \<ominus> Y i) < #({\<surd>} \<ominus> Y j)"
      by (smt Fin_neq_inf \<open>#({\<surd>} \<ominus> Y i) \<le> #({\<surd>} \<ominus> s)\<close> \<open>Fin n = #(Y j)\<close> inf_ub less2eq lnle_conv lnless_def s_def sconc_fst_inf sfilter_conc singletonI trans_lnle)
  qed
  thus ?thesis
    by (smt f1 f2 assms(1) ch2ch_Rep_cfunR contlub_cfun_arg inf_chainl4 lnless_def lub_eqI lub_finch2 max_in_chainI max_in_chain_def maxinch_is_thelub) 
qed

lemma tstream_well_adm1 [simp]: "adm (\<lambda>s. #(sfilter {\<surd>}\<cdot>s) = \<infinity> \<or> ( #s<\<infinity> \<and> (\<exists>x. s = x\<bullet>\<up>\<surd>)))"
apply(rule admI)
by (metis inf2max lub_eqI lub_finch2 sfilterl4 tstream_well_fin_adm)

(* wellformed definition for timed Streams *)
definition ts_well :: "'a event stream \<Rightarrow> bool" where
"ts_well  \<equiv> \<lambda>s.     s = \<epsilon>   (* stream is the empty stream *)
                  \<or> #({\<surd>} \<ominus> s) = \<infinity> (* or has infinitly many ticks *)
                  \<or>(#s < \<infinity> \<and> (\<exists>x. s = x\<bullet>\<up>\<surd>))"  (* or is finite and ends with \<surd> *)

lemma tstream_well_adm [simp]: "adm ts_well"
proof -
  have "adm (\<lambda>s. s=\<epsilon>)" by simp
  hence "adm (\<lambda>s. (s=\<epsilon>) \<or> (#(sfilter {\<surd>}\<cdot>s) = \<infinity> \<or> (#s<\<infinity> \<and> (\<exists>x. s = x\<bullet>\<up>\<surd>))))"  
    using tstream_well_adm1 Adm.adm_disj by blast
  thus ?thesis by (simp add: ts_well_def)
qed



(* Finally, the definition of tstream *)
pcpodef 'a tstream = "{t :: 'a event stream. ts_well t}"
apply (simp add: ts_well_def)
by auto

setup_lifting type_definition_tstream





(* ----------------------------------------------------------------------- *)
  subsection \<open>Definitions on tstream\<close>
(* ----------------------------------------------------------------------- *)


(* returns the set with all Msg in t. No ticks *)
definition tsDom :: "'a tstream \<rightarrow> 'a set" where
"tsDom \<equiv> \<Lambda> ts . {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream ts)}"


(* concatenation of tstreams *)
definition tsConc :: "'a tstream \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsConc ts1 \<equiv> \<Lambda> ts2. Abs_tstream ((Rep_tstream ts1) \<bullet> (Rep_tstream ts2))"

abbreviation sbConc_abbr :: "'a tstream \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream" (infixl "\<bullet>" 65)
where "ts1 \<bullet> ts2 \<equiv> tsConc ts1\<cdot>ts2"



(* filters all ticks and returns the corrosponding 'a stream *)
definition tsAbs:: "'a tstream \<rightarrow> 'a stream" where
"tsAbs \<equiv> \<Lambda> ts.  smap (\<lambda>e. case e of Msg m \<Rightarrow> m | \<surd> \<Rightarrow> undefined)\<cdot>(sfilter {e. e \<noteq> \<surd>}\<cdot>(Rep_tstream ts))"


(* returns the first time slot *)
definition tsTakeFirst :: "'a tstream \<rightarrow> 'a tstream" where
"tsTakeFirst \<equiv> \<Lambda> ts. Abs_tstream (stwbl (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts))"

(* deletes the first time slot *)
definition tsDropFirst :: "'a tstream \<rightarrow> 'a tstream" where
"tsDropFirst \<equiv> \<Lambda> ts. Abs_tstream (srtdw(\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts))"


(* drops the first n time slots*)
primrec tsDrop :: "nat \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsDrop 0 = ID" | (* drop nothing, Identitiy function *)
"tsDrop (Suc n) = (\<Lambda> ts. tsDrop n\<cdot>(tsDropFirst\<cdot>ts))"


(* returns the n-th time slot, counting from 0 *)
definition tsNth:: "nat \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsNth n \<equiv> \<Lambda> ts. tsTakeFirst\<cdot>(tsDrop n\<cdot>ts)"


(* take the first n time slots. *)
primrec tsTake :: "nat \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsTake 0 = \<bottom>" |  (* take 0 timeslots. empty stream *)
"tsTake (Suc n) = (\<Lambda> ts. if ts=\<bottom> then \<bottom> else tsTakeFirst\<cdot>ts \<bullet> tsTake n\<cdot>(tsDropFirst\<cdot>ts))"

declare tsTake.simps [simp del]

abbreviation tsTake_abbrv:: "'m tstream \<Rightarrow> nat \<Rightarrow> 'm tstream" ("_ \<down> _ ") where
"ts \<down> n \<equiv> tsTake n\<cdot>ts"


definition tsTickCount :: "'a tstream \<rightarrow> lnat" where
"tsTickCount \<equiv> \<Lambda> ts. #( {\<surd>} \<ominus> (Rep_tstream ts))"

abbreviation tsTickCount_abbr :: "'a tstream \<Rightarrow>lnat" ( "#\<surd> _" 65)
where "#\<surd>ts \<equiv> tsTickCount\<cdot>ts"

(*@{term tsntimes}  concatenates a timed stream n times with itself *)
primrec tsntimes:: " nat \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream" where
"tsntimes 0 ts =\<bottom> " |
"tsntimes (Suc n) ts = tsConc ts\<cdot>(tsntimes n ts)"

(*@{term tsinftimes}  concatenates a timed stream infinitely often with itself *)
definition tsinftimes:: "'a tstream \<Rightarrow> 'a tstream" where
"tsinftimes \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda>ts. if ts = \<bottom> then \<bottom> else (tsConc ts \<cdot> (h ts))))"




(* Definitionen aus TStream *)

text {* Convert an event-spf to a timed-spf. Just a restriction of the function domain. *}
definition espf2tspf :: "('a event,'b event) spf \<Rightarrow> 'a tstream \<Rightarrow> 'b tstream" where
"espf2tspf f x = Abs_tstream (f\<cdot>(Rep_tstream x))"

text {* Apply a function to all messages of a stream. Ticks are mapped to ticks. *}
definition tstmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tstream \<rightarrow> 'b tstream" where
"tstmap f \<equiv> \<Lambda> s.  espf2tspf (smap (\<lambda>x. case x of Msg m \<Rightarrow> Msg (f m) | \<surd> \<Rightarrow> \<surd>)) s"


definition tsrcDups_helper :: "'m event stream \<rightarrow> 'm event stream" where
"tsrcDups_helper \<equiv> \<mu> h. (\<Lambda> s . if s = \<epsilon> then \<epsilon> else sconc (\<up>(shd s))\<cdot>( h\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)))"
  
  (* remove successive duplicates on tstreams *)
definition tsrcdups :: "'m tstream \<Rightarrow> 'm tstream" where
"tsrcdups = espf2tspf tsrcDups_helper"


text {* "Unzipping" of timed streams: project to the first element of a tuple of streams. *}
definition tstprojfst :: "('a \<times> 'b) tstream \<rightarrow> 'a tstream" where
"tstprojfst = tstmap fst"

text {* "Unzipping" of timed streams: project to the second element of tuple. *}
definition tstprojsnd :: "('a \<times> 'b) tstream \<rightarrow> 'b tstream" where
"tstprojsnd = tstmap snd"






(* ----------------------------------------------------------------------- *)
  subsection \<open>Lemmas on tstream\<close>
(* ----------------------------------------------------------------------- *)


(* Allgemeine Lemma *)


lemma rep_tstream_cont [simp]: "cont Rep_tstream"
apply(rule contI2)
apply (meson below_tstream_def monofunI)
by (metis (mono_tags, lifting) Abs_tstream_inverse Rep_tstream adm_def below_tstream_def lub_tstream mem_Collect_eq po_class.chain_def po_eq_conv tstream_well_adm)

lemma rep_tstream_chain [simp]: assumes "chain Y"
  shows "chain (\<lambda>i. Rep_tstream (Y i))"
by (meson assms below_tstream_def po_class.chain_def)

(* i want this in the simplifier *)
lemma [simp]: assumes "cont g" and "\<forall>x. ts_well (g x)"
  shows "cont (\<lambda>x. Abs_tstream (g x))"
by (simp add: assms(1) assms(2) cont_Abs_tstream)

lemma [simp]:assumes "ts_well t"
  shows "Rep_tstream (Abs_tstream t) = t"
by (simp add: Abs_tstream_inverse assms)

lemma tick_msg [simp]: "ts_well (\<up>\<surd>)"
by(simp add: ts_well_def)

lemma [simp]: "ts_well \<epsilon>"
by(simp add: ts_well_def)

lemma [simp]: "Rep_tstream \<bottom> = \<epsilon>"
by (simp add: Rep_tstream_strict)

lemma [simp]: "Abs_tstream \<bottom> = \<bottom>"
by (simp add: Abs_tstream_strict)

lemma [simp]: assumes "ts_well s" and "s\<noteq>\<bottom>"
  shows "Abs_tstream s \<noteq> \<bottom>"
using Abs_tstream_inverse assms(1) assms(2) by fastforce

lemma [simp]: assumes "Rep_tstream (Abs_tstream t) = ts"
  shows "ts_well ts"
using Rep_tstream assms by blast

lemma  assumes "Rep_tstream (Abs_tstream t) = t"
  shows "ts_well t"
using assms by auto

lemma [simp]: assumes "Rep_tstream ts \<noteq> \<bottom>"
  shows "ts \<noteq> \<bottom>"
using Rep_tstream_strict assms by blast

lemma [simp]: "Abs_tstream (Rep_tstream ts) = ts"
by (simp add: Rep_tstream_inverse)

lemma [simp]:"ts_well (Rep_tstream ts)"
using Rep_tstream by blast






(* tsDom *)
thm tsDom_def

lemma tsdom_monofun [simp]: "monofun (\<lambda>t. {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream t)})"
by (smt below_tstream_def contra_subsetD mem_Collect_eq monofunI monofun_cfun_arg set_cpo_simps(1) subsetI) 

(* for any chain Y of tstreams the domain of the lub is contained in the lub of domains of the chain *)
lemma tsdom_contlub [simp]: assumes "chain Y" 
  shows "{a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream (\<Squnion>i. Y i))} \<subseteq> (\<Squnion>i. {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream (Y i))})"
    (is "?F (\<Squnion>i. Y i) \<subseteq> _ ")
proof 
  fix a
  assume "a\<in>?F (\<Squnion>i. Y i)"
  hence "Msg a \<in> sdom\<cdot>(Rep_tstream (\<Squnion>i. Y i))" by (simp add: tsDom_def)
  hence "Msg a \<in> (\<Squnion>i. sdom\<cdot>(Rep_tstream (Y i)))"
    by (smt Abs_tstream_inverse Rep_tstream adm_def assms below_tstream_def contlub_cfun_arg lub_eq lub_tstream mem_Collect_eq po_class.chain_def tstream_well_adm) 
  hence "Msg a \<in> (\<Union>i. sdom\<cdot>(Rep_tstream (Y i)))" by (metis SUP_def set_cpo_simps(2))
  hence "(a \<in> (\<Squnion>i. {u. Msg u \<in> sdom\<cdot>(Rep_tstream (Y i))}))"
    by (metis (no_types, lifting) SUP_def UN_iff mem_Collect_eq set_cpo_simps(2))
  thus "a\<in>(\<Squnion>i. ?F (Y i))" by (metis (mono_tags, lifting) Collect_cong lub_eq tsDom_def)
qed

lemma tsdom_cont [simp]:"cont (\<lambda>t. {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream t)})"
apply(rule contI2)
using tsdom_monofun apply blast
by (metis SetPcpo.less_set_def tsdom_contlub)

lemma tsdom_insert: "tsDom\<cdot>t = {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream t)}"
by (metis (mono_tags, lifting) Abs_cfun_inverse2 tsDom_def tsdom_cont)

lemma tsdom_rep_eq: assumes "ts_well ts"
  shows "tsDom\<cdot>(Abs_tstream ts) = {a | a. (Msg a) \<in> sdom\<cdot>ts}"
by(simp add: tsdom_insert assms)


lemma [simp]: "tsDom\<cdot>\<bottom> = {}"
by(simp add: tsdom_insert)








(* tsConc *)
thm tsConc_def


(* the concatination of 2 tStreams is wellformed *)
lemma ts_well_conc1 [simp]: assumes "ts_well ts1" and "ts_well ts2"
  shows "ts_well (ts1 \<bullet> ts2)"
proof(cases "ts1=\<epsilon>\<or>ts2=\<epsilon>")
  case True thus ?thesis using assms(1) assms(2) sconc_fst_empty sconc_snd_empty by auto
next
  case False thus ?thesis
  proof (cases "#ts1=\<infinity> \<or> #ts2=\<infinity>")
    case True thus ?thesis
      by (metis False assms(1) assms(2) lnless_def sconc_fst_inf sfilter_conc2 sfilterl4 ts_well_def)
  next
    case False 
    hence "#(ts1\<bullet>ts2) < \<infinity>" by (metis fair_sdrop inf_ub lnle_def lnless_def ninf2Fin sdropl6)
    thus ?thesis
      by (metis (no_types, lifting) False assms(1) assms(2) assoc_sconc sconc_snd_empty sfilterl4 ts_well_def)
   qed
qed

lemma ts_well_conc [simp]: "ts_well ((Rep_tstream ts1) \<bullet> (Rep_tstream ts2))"
using Rep_tstream ts_well_conc1 by auto

lemma tsconc_insert: "ts1 \<bullet> ts2 = Abs_tstream ((Rep_tstream ts1) \<bullet> (Rep_tstream ts2))"
by (simp add: tsConc_def)

lemma tsconc_rep_eq: assumes "ts_well s"
  shows "Rep_tstream ((Abs_tstream s) \<bullet> ts) = s \<bullet> Rep_tstream ts"
  by(simp add: tsconc_insert assms)

lemma tsconc_rep_eq1: assumes "ts_well s" and "ts_well ts"
  shows "Rep_tstream ((Abs_tstream s) \<bullet> (Abs_tstream ts)) = s \<bullet> ts"
  by(simp add: tsconc_insert assms)


lemma [simp]: fixes ts1::"'a tstream"
  shows "ts1 \<bullet> \<bottom> = ts1"
by(simp add: tsConc_def)

lemma [simp]: fixes ts1::"'a tstream"
  shows "\<bottom> \<bullet> ts1 = ts1"
by(simp add: tsConc_def)

lemma tsconc_assoc [simp]:  fixes a:: "'a tstream"
  shows "a \<bullet> (x \<bullet> y) = (a \<bullet> x) \<bullet> y"
by(simp add: tsconc_insert)

lemma ts_tsconc_prefix [simp]: "(x::'a tstream) \<sqsubseteq> (x \<bullet> y)"
by (metis Rep_tstream_inverse Rep_tstream_strict minimal monofun_cfun_arg sconc_snd_empty tsconc_insert)

text {* By appending an event on the left side, a timed stream remains a timed stream. *}
lemma tstream_scons_eq[simp]: "((\<up>e \<bullet> rs) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}) 
                      \<longleftrightarrow> (rs \<in> {t. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>})"
apply (smt fold_inf lnat.injects mem_Collect_eq sfilter_in sfilter_nin slen_scons)
done




(* tsAbs *)
thm tsAbs_def


lemma tsabs_insert: "tsAbs\<cdot>ts = smap (\<lambda>e. case e of Msg m \<Rightarrow> m | \<surd> \<Rightarrow> undefined)\<cdot>
                                                    (sfilter {e. e \<noteq> \<surd>}\<cdot>(Rep_tstream ts))"
by (simp add: tsAbs_def)

lemma tsabs_rep_eq: assumes "ts_well ts"
  shows "tsAbs\<cdot>(Abs_tstream ts) = smap (\<lambda>e. case e of Msg m \<Rightarrow> m | \<surd> \<Rightarrow> undefined)\<cdot>
                                                    (sfilter {e. e \<noteq> \<surd>}\<cdot>ts)"
by(simp add: tsabs_insert assms)


lemma tsabs_tick [simp]: "tsAbs\<cdot>((Abs_tstream (\<up>\<surd>)) \<bullet> ts) = tsAbs\<cdot>ts"
by(simp add: tsabs_insert tsconc_rep_eq)

lemma tsabs_conc: assumes "#(Rep_tstream ts1)<\<infinity>"
  shows "tsAbs\<cdot>(ts1 \<bullet> ts2) = tsAbs\<cdot>ts1 \<bullet> tsAbs\<cdot>ts2"
apply(simp add: tsabs_insert tsconc_insert)
using add_sfilter assms infI lnless_def smap_split by fastforce

lemma tsabs_tsdom [simp]: "sdom\<cdot>(tsAbs\<cdot>ts) = tsDom\<cdot>ts"
  apply(simp add: tsdom_insert tsabs_insert smap_sdom)
  apply rule
   apply rule
   apply (smt IntE event.case(1) event.exhaust imageE mem_Collect_eq)
  apply rule
  apply (metis (mono_tags, lifting) Int_iff event.distinct(1) event.simps(4) image_iff mem_Collect_eq)
done 




(* tsRep *)

text {* Abs_Rep *}
lemma Abs_Rep: "Abs_tstream (Rep_tstream t) = t"
apply simp
done

text {* typedef tstream unfold. *}
lemma tstreaml1[simp]: "#(Rep_tstream x) \<noteq> \<infinity> \<or> #(sfilter {\<surd>}\<cdot>(Rep_tstream x)) = \<infinity>"
apply (insert Rep_tstream [of x])
apply (simp add: ts_well_def)
by auto


text {* Rep_Abs *}
lemma Rep_Abs: "ts_well t  \<Longrightarrow> Rep_tstream (Abs_tstream t) = t"
using Abs_tstream_inverse by blast

(*Rep_tstream is ts_well*)
lemma ts_well_Rep: "ts_well (Rep_tstream s)"
by simp

(*sConc of an finite eventstream and an Rep_tstream has only finitely many \<surd> \<Longrightarrow> Conc is finite*)
lemma sConc_Rep_fin_fin: "(#({\<surd>} \<ominus> \<up>e \<bullet> Rep_tstream s) \<noteq> \<infinity>) \<Longrightarrow> ((#((\<up>e \<bullet> Rep_tstream s)) < \<infinity>))"
using leI tstreaml1 by fastforce

(*If an well defined stream is not empty, then there is an stream concatenated with \<surd>
equal to the well defined stream *)
lemma ts_fin_well: "ts_well ts \<and> ts\<noteq>\<epsilon> \<Longrightarrow>\<exists> ts2. ts = ts2 \<bullet> (\<up>\<surd>)"
apply(simp add: ts_well_def)
by (metis sconc_fst_inf sfilterl4)


(*An Rep_tstream of an not empty stream is well defined if there is an event appended*)
lemma sConc_fin_well: "s\<noteq>\<bottom> \<Longrightarrow> ts_well (\<up>e \<bullet> Rep_tstream s)"
apply(simp add: ts_well_def)
apply auto
using sConc_Rep_fin_fin apply auto[1]
by (metis ts_well_Rep Rep_tstream_bottom_iff assoc_sconc ts_fin_well)

text {* Another useful variant of this identity: *}
lemma [simp]: " s\<noteq>\<bottom> \<Longrightarrow>( Rep_tstream (Abs_tstream ( \<up>e \<bullet> Rep_tstream s)) = (\<up>e \<bullet> Rep_tstream s))"
using Abs_tstream_inverse Rep_tstream tstream_scons_eq ts_well_def
using Rep_Abs sConc_fin_well by blast

text {* The following implication follows from the type definition of timed streams. *}
lemma Rep_tstreamD1: "(Rep_tstream ts = s) \<Longrightarrow> (s \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>})"
using Rep_tstream 
using tstreaml1 by auto



(* tsTakeFirst *)



(* the first tick comes after finitely many messages *)
lemma stakewhileFromTS[simp]: assumes "ts_well ts"
  shows "#(stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts) < \<infinity>"
by (metis (mono_tags, lifting) Inf'_neq_0 assms ex_snth_in_sfilter_nempty inf_ub lnle_conv lnless_def po_eq_conv singletonD slen_empty_eq stakewhile_less stakewhile_slen ts_well_def)

lemma stakewhileFromTS2[simp]: assumes "ts_well ts"
  shows "#(stwbl (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts) < \<infinity>"
by (metis assms inf_ub lnle_def lnless_def notinfI3 sconc_slen stakewhileFromTS stwbl_stakewhile ub_slen_stake)

lemma stakewhile2stake: assumes "ts_well ts"
  shows "\<exists>n. stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts = stake n\<cdot>ts"
by (metis approxl2 assms fin2stake lncases lnless_def stakewhileFromTS stakewhile_below)

lemma stakewhile2stake2: assumes "ts_well ts"
  shows "\<exists>n. stwbl (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts = stake n\<cdot>ts"
by (metis approxl2 assms fin2stake lncases lnless_def stakewhileFromTS2 stwbl_below)

(* tsTakeFirst produces a wellformed stream *)
lemma ts_well_stakewhile[simp]: assumes "ts_well ts"
  shows "ts_well (stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts\<bullet> \<up>\<surd>)"
proof -
  have "\<forall>s. \<not> ts_well s \<or> #(stakewhile (\<lambda>e. (e::'a event) \<noteq> \<surd>)\<cdot>s) < \<infinity>"
    using stakewhileFromTS by blast
  then have "#(stakewhile (\<lambda>e. e \<noteq> \<surd>)\<cdot> ts \<bullet> \<up>\<surd>) < \<infinity>"
    by (simp add: assms lnless_def slen_lnsuc)
  then show ?thesis
    by (meson ts_well_def)
qed

lemma ts_finite_sfoot [simp]: assumes "ts \<noteq> \<epsilon>" and "#ts<\<infinity>" and "ts_well ts" 
  shows "sfoot ts = \<surd>"
by (metis assms(1) assms(2) assms(3) lnless_def sfilterl4 sfoot1 ts_well_def)


lemma ts_tick_exists: assumes "ts1 \<noteq> \<epsilon>" and "ts_well ts1"
  shows "\<exists>n. snth n ts1 = \<surd> \<and> Fin n <#ts1"
proof(cases "#ts1=\<infinity>")
  case True thus ?thesis by(metis assms(1) assms(2) ex_snth_in_sfilter_nempty lnless_def singletonD slen_empty_eq ts_well_def)
next
  case False
  hence "#ts1<\<infinity>" by (meson assms(1) assms(2) sfilterl4 ts_well_def)
  hence "sfoot ts1 = \<surd>" using assms(1) assms(2) ts_finite_sfoot by blast
  obtain n' where "Fin (Suc n') = #ts1" by (metis False Suc_le_D assms(1) less2nat lncases neq02Suclnle slen_empty_eq)
  hence "Fin n' < #ts1"
    by (metis Fin_def inject_Fin lnat.chain_take lnless_def monofun_cfun_fun n_not_Suc_n po_class.chainE)
  hence "snth n' ts1 = \<surd>" by (simp add: \<open>Fin (Suc n') = #ts1\<close> \<open>sfoot ts1 = \<surd>\<close> sfoot_exists2) 
  thus ?thesis using \<open>Fin n' < #ts1\<close> by blast 
qed


(* if 2 tstreams are in a below relation, and they have a first timeSlot (\<noteq>\<bottom>) thos are equal *)
lemma stakewhile_tsb_eq:  assumes "ts1\<sqsubseteq>ts2" and "ts1 \<noteq> \<bottom>"
  shows "stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts1) = stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts2)"
proof (cases "#(Rep_tstream ts1) = \<infinity>")
  case True thus ?thesis by (metis assms(1) below_tstream_def eq_less_and_fst_inf) 
next
  case False 
  obtain n where "snth n (Rep_tstream ts1) = \<surd>" using Rep_tstream_bottom_iff assms(2) ts_tick_exists by fastforce
  have "(Rep_tstream ts1) \<noteq> \<epsilon>" using Rep_tstream_inject assms(2) by fastforce
  have "sfoot (Rep_tstream ts1) = \<surd>" by (simp add: False \<open>Rep_tstream ts1 \<noteq> \<epsilon>\<close> lnless_def)
  have "sdom\<cdot>(stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts1)) \<noteq> sdom\<cdot>(Rep_tstream ts1)"
    by (metis (mono_tags, lifting) Rep_tstream_strict \<open>Rep_tstream ts1 \<noteq> \<epsilon>\<close> sconc_snd_empty snth2sdom stakewhile_dom ts_tick_exists ts_well_conc)
  hence "stakewhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts1) \<noteq> (Rep_tstream ts1)" by auto
  thus ?thesis by (meson assms(1) below_tstream_def stakewhile_finite_below) 
qed

lemma stwbl_tsb_eq:  assumes "ts1\<sqsubseteq>ts2" and "ts1 \<noteq> \<bottom>"
  shows "stwbl (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts1) = stwbl (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts2)"
by (smt Rep_tstream Rep_tstream_bottom_iff assms(1) assms(2) below_tstream_def mem_Collect_eq po_eq_conv sfoot12 snth2sdom stakewhileFromTS stakewhile_below stakewhile_tsb_eq strict_stakewhile stwbl2stakewhile stwbl_sfoot ts_tick_exists)


lemma tickInDom [simp]: assumes "ts_well s" and "s\<noteq>\<epsilon>"
  shows "\<surd> \<in>sdom\<cdot>s"
using assms(1) assms(2) snth2sdom ts_tick_exists by force


lemma tstakefirst_well [simp]: assumes "ts_well ts"
  shows "ts_well (stwbl (\<lambda>a. a \<noteq> \<surd>)\<cdot>ts)"
proof(cases "ts=\<epsilon>")
  case True thus ?thesis by simp
next
  case False 
  hence "\<surd>\<in>sdom\<cdot>ts" using assms tickInDom by blast
  hence "sfoot (stwbl (\<lambda>a. a \<noteq> \<surd>)\<cdot>ts) = \<surd>"
    by (metis (mono_tags, lifting) stwbl_sfoot)
  thus ?thesis by (metis assms sfoot2 stakewhileFromTS2 ts_well_def) 
qed

lemma tstakefirst_well1 [simp]: "ts_well (stwbl (\<lambda>a. a \<noteq> \<surd>)\<cdot>(Rep_tstream ts))"
by simp

lemma tstakefirst_insert: "tsTakeFirst\<cdot>ts = Abs_tstream (stwbl (\<lambda>a. a \<noteq> \<surd>)\<cdot>(Rep_tstream ts))"
by(simp add: tsTakeFirst_def)

lemma tstakefirst_insert_rep_eq: assumes "ts_well ts"
  shows "tsTakeFirst\<cdot>(Abs_tstream ts) = Abs_tstream (stwbl (\<lambda>a. a \<noteq> \<surd>)\<cdot>ts)"
by(simp add: tstakefirst_insert assms)


lemma tstakefirst_prefix[simp]: "tsTakeFirst\<cdot>ts \<sqsubseteq> ts"
apply(simp add: below_tstream_def)
by(simp add: tstakefirst_insert)


lemma [simp]: "tsTakeFirst\<cdot>\<bottom> = \<bottom>"
by(simp add: tsTakeFirst_def)

lemma tstakefirst_bot: "tsTakeFirst\<cdot>x = \<bottom> \<Longrightarrow> x=\<bottom>"
apply(simp add: tstakefirst_insert)
by (metis Abs_tstream_bottom_iff Abs_tstream_cases Abs_tstream_inverse mem_Collect_eq stwbl_notEps tstakefirst_well)

lemma tstakefirst_eq: assumes "ts1\<noteq>\<bottom>" and "ts1 \<sqsubseteq> ts2"
  shows "tsTakeFirst\<cdot>ts1 = tsTakeFirst\<cdot>ts2"
apply(simp add: tstakefirst_insert)
using assms(1) assms(2) stwbl_tsb_eq by fastforce

lemma tstakefirst2first[simp]: "tsTakeFirst\<cdot>(tsTakeFirst\<cdot>ts) = tsTakeFirst\<cdot>ts"
by(simp add: tsTakeFirst_def)

lemma tstakefirst_dom [simp]: "tsDom\<cdot>(tsTakeFirst\<cdot>ts) \<subseteq> tsDom\<cdot>ts"
by (metis monofun_cfun_arg set_cpo_simps(1) tstakefirst_prefix)




(* tsDropFirst *)
thm tsDropFirst_def


lemma dropwhile2drop: assumes "ts_well ts"
  shows "\<exists>n. sdropwhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts = sdrop n\<cdot>ts"
by (metis assms infI lnless_def stakewhileFromTS stakewhile_sdropwhilel1)

lemma srtdw2drop: assumes "ts_well ts"
  shows "\<exists>n. srtdw (\<lambda>a. a\<noteq>\<surd>)\<cdot>ts = sdrop n\<cdot>ts"
apply(simp add: srtdw_def)
by (metis assms dropwhile2drop sdrop_back_rt)

lemma ts_well_drop11 [simp]: assumes "ts_well s" and "#s<\<infinity>" and "Fin 1<#s"
  shows "ts_well (srt\<cdot>s)"
proof -
  have "s\<noteq>\<epsilon>" by (metis assms(3) bottomI lnless_def lnzero_def strict_slen)
  hence "sfoot s = \<surd>" using assms(1) assms(2) ts_finite_sfoot by blast 
  hence "sfoot (srt\<cdot>s) = \<surd>" using assms(2) assms(3) sfoot_sdrop by fastforce
  thus ?thesis
    by (metis \<open>s \<noteq> \<epsilon>\<close> assms(2) fold_inf inf_ub lnle_def lnless_def sfoot2 slen_scons surj_scons ts_well_def)
qed


lemma ts_well_dropinf [simp]: assumes "ts_well s" and "#s = \<infinity>"
  shows "ts_well (srt\<cdot>s)"
proof -
  have "#({\<surd>} \<ominus> s) = \<infinity>" by (metis Inf'_neq_0 assms(1) assms(2) lnless_def strict_slen ts_well_def)
  hence "#({\<surd>} \<ominus> (srt\<cdot>s)) = \<infinity>" by (smt Inf'_neq_0 assms(2) inf_scase inject_scons sfilter_in sfilter_nin slen_empty_eq surj_scons) 
  thus ?thesis by (meson ts_well_def)  
qed

(* if you drop the first Element the resulting stream is still wellformed *)
lemma ts_well_drop1 [simp]: assumes "ts_well s"
  shows "ts_well (srt\<cdot>s)"
apply(cases "#s=\<infinity>")
apply(simp add: assms)
apply(cases "#s\<le>Fin 1")
apply (metis Fin_02bot One_nat_def bottomI lnle_def lnzero_def slen_empty_eq slen_rt_ile_eq ts_well_def)
by (metis assms One_nat_def lnat_po_eq_conv lnle_def lnless_def neq02Suclnle sfilterl4 slen_empty_eq stream.sel_rews(2) ts_well_drop11 ts_well_def)

(* if you drop the arbitrary many Elements, the resulting stream is still welformed *)
lemma ts_well_drop [simp]: 
  shows "ts_well s \<Longrightarrow>ts_well (sdrop n\<cdot>s)"
apply(induction n arbitrary: s)
apply (simp add: assms)
by (metis One_nat_def sdrop_0 sdrop_forw_rt ts_well_drop1)

lemma tsdropfirst_well1 [simp]:  
  shows "ts_well (srt\<cdot>(sdropwhile (\<lambda>a. a\<noteq>\<surd>)\<cdot>(Rep_tstream ts)))"
by (metis Rep_tstream dropwhile2drop mem_Collect_eq sdrop_back_rt ts_well_drop)

lemma tsdropfirst_well [simp]: 
  shows "ts_well (srtdw (\<lambda>a. a \<noteq> \<surd>)\<cdot>(Rep_tstream ts))"
by (metis Rep_tstream mem_Collect_eq srtdw2drop ts_well_drop)

lemma tsdropfirst_insert: "tsDropFirst\<cdot>ts = Abs_tstream (srtdw (\<lambda>a. a \<noteq> \<surd>)\<cdot>(Rep_tstream ts))"
by(simp add: tsDropFirst_def)

lemma tsdropfirst_rep_eq: assumes "ts_well ts"
  shows "tsDropFirst\<cdot>(Abs_tstream ts) = Abs_tstream (srtdw (\<lambda>a. a \<noteq> \<surd>)\<cdot>ts)"
by(simp add: tsDropFirst_def assms)



lemma [simp]: "tsDropFirst\<cdot>\<bottom> = \<bottom>"
by(simp add: tsdropfirst_insert)


lemma tsTakeDropFirst [simp]: "tsTakeFirst\<cdot>ts \<bullet> tsDropFirst\<cdot>ts = ts"
by (metis (no_types, lifting) Abs_tstream_inverse Rep_tstream Rep_tstream_inverse mem_Collect_eq stwbl_srtdw tsconc_insert tsdropfirst_insert tsdropfirst_well tstakefirst_insert tstakefirst_well)




(* tsDrop *)
thm tsDrop_def

lemma [simp]: "tsDrop i\<cdot>\<bottom> = \<bottom>"
apply(induction i)
apply(simp)
by(simp add: tsDrop_def)

lemma tsDropNth: "tsDrop n\<cdot>ts = (tsNth n\<cdot>ts) \<bullet> tsDrop (Suc n)\<cdot>ts"
apply(induction n arbitrary: ts)
apply (simp add: tsNth_def)
by (simp add: tsNth_def)

lemma tsdrop_tick [simp] :"tsDrop (Suc n)\<cdot>(Abs_tstream (\<up>\<surd>) \<bullet> ts) = tsDrop n\<cdot>ts"
by(simp add: tsDrop.simps tsdropfirst_insert tsconc_rep_eq)


(* tsNth *)
lemma [simp]: "tsNth i\<cdot>\<bottom> = \<bottom>"
by(simp add: tsNth_def)

lemma tsNth_Suc: "tsNth (Suc i)\<cdot>ts = tsNth i\<cdot>(tsDropFirst\<cdot>ts)"
by (simp add: tsNth_def)

(* The first element of a stream is equal to the element on the zeroth position *)
lemma tsnth_shd[simp]: "tsNth 0\<cdot>s = tsTakeFirst\<cdot>s"
by (simp add: tsNth_def)






(* tsTickCount *)
lemma [simp]: "#\<surd> \<bottom> = 0"
by(simp add: tsTickCount_def)

lemma tstickcount_insert:  "#\<surd> ts =  #({\<surd>} \<ominus> Rep_tstream ts)"
by(simp add: tsTickCount_def)


lemma tstickcount_rep_eq: assumes "ts_well ts"
  shows  "#\<surd> (Abs_tstream ts) =  #({\<surd>} \<ominus> ts)"
by(simp add: tsTickCount_def assms)

lemma finititeTicks[simp]: assumes "#\<surd> ts < \<infinity>"
  shows "#(Rep_tstream ts) < \<infinity>"
proof(rule ccontr)
  assume "\<not> #(Rep_tstream ts) < \<infinity>"
  hence "#(Rep_tstream ts) = \<infinity>" using inf_ub lnle_def lnless_def by blast 
  hence "#({\<surd>} \<ominus> (Rep_tstream ts)) = \<infinity>"
    by (metis Inf'_neq_0 \<open>\<not> #(Rep_tstream ts) < \<infinity>\<close> sconc_fst_inf slen_empty_eq ts_well_conc ts_well_def)
  hence "#\<surd> ts = \<infinity>" by(simp add: tstickcount_insert)
  thus False using assms by auto 
qed

lemma finiteTicks [simp]: assumes "#\<surd> ts1 = Fin n1"
  shows "\<exists> k. #(Rep_tstream ts1) = Fin k"
proof -
  have " #(Rep_tstream ts1) < \<infinity>" using assms by auto
  thus ?thesis using infI lnless_def by blast 
qed

lemma tsInfTicks:  
  shows "#\<surd> ts = \<infinity> \<longleftrightarrow>#(Rep_tstream ts) = \<infinity>"
by (metis finititeTicks lnle_def lnless_def sfilterl4 slen_sfilterl1 tstickcount_insert)

(* Prepending to infinite streams produces infinite streams again *)
lemma slen_tsconc_snd_inf: "(#\<surd> y)=\<infinity> \<Longrightarrow> (#\<surd>(x \<bullet> y)) = \<infinity>"
by (metis Rep_tstream_inverse Rep_tstream_strict sconc_snd_empty slen_sconc_snd_inf tsInfTicks ts_well_conc tsconc_rep_eq)

lemma stickcount_conc [simp]: assumes "#\<surd> ts1 = Fin n1" and "#\<surd> ts2 = Fin n2"
  shows "#\<surd> (ts1 \<bullet> ts2) = Fin (n1 + n2)"
apply(simp add: tsTickCount_def tsConc_def)
apply(subst add_sfilter2)
apply(simp add: assms)
by (metis assms(1) assms(2) slen_sconc_all_finite tstickcount_insert)

lemma tsconc_id [simp]: assumes "#\<surd>ts1 = \<infinity>"
  shows "tsConc ts1\<cdot>ts2 = ts1"
by (metis Rep_tstream_inverse assms sconc_fst_inf tsInfTicks tsconc_insert)

lemma ts_approxl [simp]: assumes "ts1 \<sqsubseteq> ts2"
  shows "\<exists> ts. (ts2 = tsConc ts1\<cdot>ts)"
proof -
  have "(Rep_tstream ts1) \<sqsubseteq> (Rep_tstream ts2)" by (meson assms below_tstream_def)
  hence "\<exists> s. ((Rep_tstream ts2) = (Rep_tstream ts1) \<bullet> s)" by (metis approxl3) 
  thus ?thesis
    by (metis (mono_tags) Rep_tstream Rep_tstream_bottom_iff Rep_tstream_cases Rep_tstream_inverse \<open>Rep_tstream ts1 \<sqsubseteq> Rep_tstream ts2\<close> eq_less_and_fst_inf lncases mem_Collect_eq sconc_snd_empty sdropl6 ts_well_drop tsconc_insert) 
qed

(* Each prefix of a stream can be expanded to the original stream *)
(* TODO: check if duplicate *)
lemma ts_approxl3: "(s1::'a tstream) \<sqsubseteq> s2 \<Longrightarrow> \<exists>t. s1\<bullet>t = s2"
using ts_approxl by blast


lemma ts_infinite_chain: assumes "chain Y" 
  shows "\<not>finite_chain Y \<longleftrightarrow> \<not>finite_chain (\<lambda>i. Rep_tstream (Y i))"
proof -
  have f1: "\<And>f. finite_chain (\<lambda>n. Rep_tstream (f n::'a tstream)) \<or> \<not> finite_chain f"
    using cont_finch2finch rep_tstream_cont by blast
  obtain nn :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
    "\<And>f. Lub f = f (nn f) \<or> \<not> finite_chain f"
    by (metis (no_types) finite_chain_def maxinch_is_thelub)
  then show ?thesis
    using f1 by (metis (no_types) Rep_tstream_inverse assms finite_chain_def lub_tstream maxinch_is_thelub)
qed

lemma ts_finite_chain:  
  shows "finite_chain Y \<longleftrightarrow> finite_chain (\<lambda>i. Rep_tstream (Y i))"
by (metis below_tstream_def finite_chain_def po_class.chain_def ts_infinite_chain)

lemma ts_infinite_lub[simp]: assumes "chain Y" and "\<not>finite_chain Y"
  shows "#\<surd> (\<Squnion>i. Y i) = \<infinity>"
proof -
  have f1: "Rep_tstream (Lub Y) = (\<Squnion>n. Abs_cfun Rep_tstream\<cdot>(Y n))"
    by (metis (no_types) Abs_cfun_inverse2 assms(1) contlub_cfun_arg rep_tstream_cont)
  have f2: "ts_well (\<Squnion>n. Abs_cfun Rep_tstream\<cdot>(Y n))"
    by (metis (no_types) Abs_cfun_inverse2 Rep_tstream assms(1) contlub_cfun_arg mem_Collect_eq rep_tstream_cont)
  have "\<not> finite_chain (\<lambda>n. Abs_cfun Rep_tstream\<cdot>(Y n))"
    using assms(2) ts_finite_chain by auto
  then show ?thesis
    using f2 f1 by (metis (no_types) Inf'_neq_0 assms(1) ch2ch_Rep_cfunR inf_chainl4 lnless_def slen_empty_eq ts_well_def tstickcount_insert)
qed

lemma ts_infinite_fin: assumes "chain Y" and "\<not>finite_chain Y"
  shows "#\<surd> (Y i) < \<infinity>"
by (metis Fin_neq_inf assms(1) assms(2) inf_chainl1 inf_ub lnle_def lnless_def rep_tstream_chain tsInfTicks ts_infinite_chain)

(* In infinite chains, all streams are finite *)
lemma ts_inf_chainl1: "\<lbrakk>chain Y; \<not>finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>k. (#\<surd>(Y i)) = Fin k"
by (metis infI less_irrefl ts_infinite_fin)

lemma ts_0ticks: "#\<surd> ts = 0 \<Longrightarrow> ts = \<bottom>"
by (metis Inf'_neq_0 Rep_tstream Rep_tstream_bottom_iff eq_bottom_iff inf_ub less_le lnless_def lnzero_def mem_Collect_eq sconc_fst_inf sfilter_conc singletonI ts_well_def tstickcount_insert)

lemma adm_fin_below: "adm (\<lambda>x . \<not> Fin n \<sqsubseteq> #\<surd> x)"
  apply(rule admI)
  apply auto
  by (metis (no_types) LNat.inf_chainl3 ch2ch_Rep_cfunR contlub_cfun_arg finite_chainE lnle_def maxinch_is_thelub)

lemma adm_fin_below2: "adm (\<lambda>x . \<not> Fin n \<le> #\<surd> x)"
by(simp only: lnle_def adm_fin_below)

lemma exist_tslen: assumes "chain Y" and "\<not>finite_chain Y"
  shows "\<exists>i. Fin n \<le> #\<surd>(Y i)"
apply(rule ccontr)
apply auto
by (metis (no_types, lifting) adm_def adm_fin_below2 assms(1) assms(2) inf_ub ts_infinite_lub)

(* In infinite chains, there is an element which is a true prefix of another one *)
lemma ts_inf_chainl2: "\<lbrakk>chain Y; \<not> finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>j. Y k \<sqsubseteq> Y j \<and> (#\<surd>(Y k)) < #\<surd>(Y j)"
proof -
  assume a1: "chain Y"
  assume a2: "\<not> finite_chain Y"
  moreover
  { assume "\<infinity> \<noteq> #\<surd> Y k"
    then have "\<exists>n. \<not> #\<surd> Y n \<le> #\<surd> Y k"
      using a2 a1 by (metis (no_types) exist_tslen inf_belowI lnle_def trans_lnle)
    then have ?thesis
      using a1 by (meson chain_tord lnle_def monofun_cfun_arg not_less) }
  ultimately show ?thesis
    using a1 by (metis (no_types) chain_tord ts_infinite_fin)
qed





lemma tsdom_conc[simp]:"tsDom\<cdot>ts1 \<subseteq> tsDom\<cdot>(ts1 \<bullet> ts2)"
by (metis eq_iff finititeTicks inf_ub less_le sdom_sconc tsabs_conc tsabs_tsdom tsconc_id)

lemma tsdom_tsconc: assumes "#\<surd>ts1 < \<infinity>"
  shows "tsDom\<cdot>(ts1 \<bullet> ts2) = tsDom\<cdot>ts1 \<union> tsDom\<cdot>ts2"
apply rule
apply (metis assms finititeTicks sconc_sdom tsabs_conc tsabs_tsdom)
proof -
  have "#(Rep_tstream ts1) < \<infinity>" using assms by simp
  hence "sdom\<cdot>((Rep_tstream ts1) \<bullet> (Rep_tstream ts2)) = sdom\<cdot>(Rep_tstream ts1) \<union>  sdom\<cdot>(Rep_tstream ts2)"
    using infI lnless_def sdom_sconc2un by blast
  thus "tsDom\<cdot>ts1 \<union> tsDom\<cdot>ts2 \<subseteq> tsDom\<cdot>(ts1 \<bullet> ts2)"
  by (smt Abs_tstream_inverse UnCI UnE mem_Collect_eq subsetI ts_well_conc tsconc_insert tsdom_insert) 
qed

lemma tsinftickDrop[simp]: assumes "#\<surd>ts = \<infinity>"
  shows "#\<surd>(tsDropFirst\<cdot>ts) = \<infinity>"
apply(simp add: tsdropfirst_insert tstickcount_insert)
by (metis assms slen_sfilter_sdrop srtdw2drop ts_well_def tstickcount_insert)


lemma tsinf_nth [simp]: "#\<surd>ts = \<infinity> \<Longrightarrow> tsNth n\<cdot>ts \<noteq> \<bottom>"
apply(induction n arbitrary: ts)
apply(simp add: tsNth_def)
using tstakefirst_bot apply force
by (simp add: tsNth_Suc)





(* tsTake *)
thm tsTake_def


(* transforming the rest of a timed stream using a continuous function na is a continuous function *)
lemma tstake_cont [simp]:"cont (\<lambda> ts. if ts=\<bottom> then \<bottom> else tsTakeFirst\<cdot>ts \<bullet> na\<cdot>(tsDropFirst\<cdot>ts))" (is "cont (?F)")
apply(rule contI2)
apply (smt eq_bottom_iff minimal monofunI monofun_cfun_arg tstakefirst_eq)
apply rule+
proof -
   fix Y :: "nat \<Rightarrow> 'a tstream"
   assume y_chain: "chain Y"
   thus "?F (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ?F (Y i))" 
   proof (cases "\<bottom> = (\<Squnion>i. Y i) ")
    case True thus ?thesis by (simp add: minimal) 
   next
    case False 
    obtain j where "Y j \<noteq> \<bottom>" by (metis False lub_chain_maxelem minimal) 
    have "\<And>i. ?F (Y i) \<sqsubseteq> ?F (Y (Suc i))" by (smt below_bottom_iff minimal monofun_cfun_arg po_class.chainE tstakefirst_eq y_chain)
    hence f_chain: "chain (\<lambda>i. ?F (Y i))" by (simp add: po_class.chainI) 

    have d_chain: "chain (\<lambda>i. Y (i+j))" (is "chain ?D") by (simp add: chain_shift y_chain) 
    have d_notBot: "\<And>i. ?D i \<noteq> \<bottom>"
      by (metis \<open>(Y::nat \<Rightarrow> 'a tstream) (j::nat) \<noteq> \<bottom>\<close> eq_bottom_iff le_add2 po_class.chain_mono y_chain)
    hence "tsTakeFirst\<cdot> (\<Squnion>i. ?D i) \<bullet> na\<cdot>(tsDropFirst\<cdot> (\<Squnion>i. ?D i)) = (\<Squnion>i. tsTakeFirst\<cdot> (?D i) \<bullet> na\<cdot>(tsDropFirst\<cdot> (?D i)))"
      by (smt d_chain contlub_cfun_arg is_ub_thelub lub_eq monofun_cfun_arg po_class.chainE po_class.chainI tstakefirst_eq)
    hence eq: "?F (\<Squnion>i. ?D i) = (\<Squnion>i. ?F (?D i))" using d_notBot d_chain is_ub_thelub by fastforce
    have "(\<Squnion>i. ?F (?D i)) = (\<Squnion>i. ?F (Y i))" using lub_range_shift f_chain by fastforce
    thus ?thesis using eq lub_range_shift y_chain by fastforce 
  qed
qed

lemma [simp]: "ts \<down> 0 = \<bottom>"
by(simp add: tsTake.simps)

lemma [simp]: "\<bottom> \<down> n = \<bottom>"
by(induction n, auto simp add: tsTake.simps)


lemma tsTake_def2:  "ts \<down> (Suc n) = (tsTakeFirst\<cdot>ts) \<bullet> ((tsDropFirst\<cdot>ts) \<down> n)"
by(simp add: tsTake.simps)

lemma tstake_tsnth: "ts \<down> (Suc i) = (ts \<down> i) \<bullet> tsNth i\<cdot>ts"
proof(induction i arbitrary: ts)
  case 0 thus ?case by(simp add: tsNth_def tsTake.simps)
next
  case (Suc i)
  fix i  :: nat
  fix ts :: "'a tstream"
  assume "(\<And>ts :: 'a tstream. ts \<down> Suc i  = ts \<down> i  \<bullet> tsNth i\<cdot>ts)"
  hence eq1: "(tsDropFirst\<cdot>ts) \<down> (Suc i) = ((tsDropFirst\<cdot>ts) \<down> i)  \<bullet> tsNth (Suc i)\<cdot>(ts)" by (simp only: tsNth_Suc) 
  hence "ts \<down> (Suc (Suc i)) = (tsTakeFirst\<cdot>ts) \<bullet> ((tsDropFirst\<cdot>ts) \<down> (Suc i))" by(simp add: tsTake.simps)
  hence "ts \<down> (Suc (Suc i)) = tsTakeFirst\<cdot>ts \<bullet> ((tsDropFirst\<cdot>ts) \<down> i)  \<bullet> tsNth (Suc i)\<cdot>(ts)" using eq1 tsconc_assoc by simp
  thus "ts \<down> (Suc (Suc i))  = ts \<down> (Suc i)  \<bullet> tsNth (Suc i)\<cdot>ts" by(simp add: tsTake.simps)
qed


lemma tstake_below [simp]: "ts \<down> i  \<sqsubseteq> ts \<down> Suc i"
by (metis Rep_tstream_inverse Rep_tstream_strict minimal monofun_cfun_arg sconc_snd_empty tsconc_insert tstake_tsnth)

lemma tstake_chain [simp]: "chain (\<lambda>i. ts \<down> i)"
by (simp add: po_class.chainI)


lemma tsConc_notEq: 
  fixes ts1 ts2 :: "'a tstream"
  assumes "ts1 \<noteq> ts2" and "#\<surd>a < \<infinity>"
  shows "a \<bullet> ts1 \<noteq> a \<bullet> ts2"
proof -
  have "#(Rep_tstream a) < \<infinity>" by (simp add: assms(2))
  hence "(Rep_tstream a) \<bullet> (Rep_tstream ts1) \<noteq> (Rep_tstream a) \<bullet> (Rep_tstream ts2)"
    by (metis Rep_tstream_inverse assms(1) sconc_neq)
  thus ?thesis
    by (metis Rep_tstream Rep_tstream_inverse mem_Collect_eq tsconc_rep_eq) 
qed

lemma tstakefirst_len [simp]: "#\<surd> tsTakeFirst\<cdot>ts < \<infinity>"
apply(simp add: tstakefirst_insert tstickcount_insert)
by (metis inf_ub less_le sfilterl4 stakewhileFromTS2 stwbl2stbl tstakefirst_well1)


lemma tstake_noteq: "ts \<down> i \<noteq> ts \<Longrightarrow> ts \<down> i \<noteq> ts \<down> Suc i"
apply(induction i arbitrary: ts)
apply (metis Rep_cfun_strict1 Rep_tstream_inverse Rep_tstream_strict sconc_snd_empty tsTake.simps(1) tsTake_def2 tsconc_insert tstakefirst_bot)
by (metis tsConc_notEq tsTakeDropFirst tsTake_def2 tstakefirst_len)



lemma tsTakeDrop [simp]: "(ts \<down> i) \<bullet> (tsDrop i\<cdot>ts) = ts"
apply(induction i arbitrary: ts)
apply simp
by (metis tsDropNth tsconc_assoc tstake_tsnth)


lemma tsTake_prefix [simp]:"ts \<down> i \<sqsubseteq> ts"
apply(induction i arbitrary: ts)
apply simp
by (metis cfcomp1 cfcomp2 monofun_cfun_arg tsNth_def tsTakeDrop tstake_tsnth tstakefirst_prefix)



lemma tstakeFirst_len [simp]: "ts \<noteq> \<bottom> \<Longrightarrow> #\<surd> tsTakeFirst\<cdot>ts = Fin 1"
apply(simp add: tstakefirst_insert tstickcount_insert)
by (metis Abs_tstream_cases Abs_tstream_inverse Rep_tstream_strict sconc_fst_empty stwbl_filterlen tickInDom ts_well_conc)

lemma tsfirstConclen [simp]: assumes "ts\<noteq>\<bottom>" shows "#\<surd>tsTakeFirst\<cdot>ts \<bullet> ts2 = lnsuc\<cdot>(#\<surd>ts2)"
proof -
  have "#({\<surd>} \<ominus> (Rep_tstream (tsTakeFirst\<cdot>ts))) = Fin 1"
    by (metis assms tstakeFirst_len tstickcount_insert)
  hence "({\<surd>} \<ominus> (Rep_tstream (tsTakeFirst\<cdot>ts))) = \<up>\<surd>"
    by (smt Fin_02bot Fin_Suc One_nat_def inject_lnsuc lnzero_def lscons_conv sfilter_ne_resup singletonD slen_empty_eq slen_scons sup'_def surj_scons)
  hence "{\<surd>} \<ominus> ((Rep_tstream (tsTakeFirst\<cdot>ts)) \<bullet> Rep_tstream ts2) = \<up>\<surd> \<bullet> {\<surd>} \<ominus> Rep_tstream ts2"
    by (simp add: add_sfilter2)
  thus ?thesis by (simp add: tsconc_insert tstickcount_insert) 
qed

lemma tstake_len[simp]: "#\<surd> (ts \<down> i) = min (#\<surd> ts) (Fin i)"
  apply(induction i arbitrary: ts)
   apply (simp)
  apply(auto simp add: tsTake.simps)
  by (metis Fin_Suc lnsuc_lnle_emb min_def tsTakeDropFirst tsfirstConclen)



lemma tsdropfirst_len: "ts \<noteq> \<bottom> \<Longrightarrow> lnsuc\<cdot>(#\<surd> (tsDropFirst\<cdot>ts)) = #\<surd> ts"
  apply(simp add: tsdropfirst_insert tstickcount_insert)
  apply(subst strdw_filter)
   apply (simp add: Rep_tstream_bottom_iff)
  by simp


lemma tstake_fin: "Fin n = #\<surd>ts \<Longrightarrow> ts \<down> n = ts"
  apply(induction n arbitrary: ts)
   apply simp
   using ts_0ticks apply blast
  apply (auto simp add: tsTake.simps)
  by (metis Fin_Suc lnat.injects tsTakeDropFirst tsdropfirst_len)

lemma tstake_fin2: "ts\<down>i = ts \<Longrightarrow> ts \<down> (Suc i) = ts"
  apply(induction i arbitrary: ts)
   apply simp
  by (metis tsConc_notEq tsTakeDropFirst tsTake_def2 tstakefirst_len)

lemma tstake_fin3: "ts\<down>i = ts \<Longrightarrow> i\<le>j \<Longrightarrow> ts \<down> j = ts"
  apply(induction j)
   apply simp
  apply simp
  using le_Suc_eq tstake_fin2 by blast

lemma tstake_maxinch: "Fin n = #\<surd>ts \<Longrightarrow> max_in_chain n (\<lambda>i. ts\<down>i)"
apply(rule max_in_chainI)
using tstake_fin tstake_fin3 by fastforce

lemma tstake_finite: assumes "#\<surd>ts < \<infinity>" shows "finite_chain (\<lambda>i. ts\<down>i)"
apply(simp add: finite_chain_def)
by (metis (full_types) assms infI less_irrefl tstake_maxinch)

lemma tstake_infinite_chain: assumes "#\<surd>ts = \<infinity>" shows "\<not> max_in_chain n (\<lambda>i. ts \<down> i)"
by (metis Suc_n_not_le_n assms cfcomp2 fold_inf inject_Fin le_cases max_in_chain_def min_def n_not_Suc_n notinfI3 tsTakeDropFirst tstake_len)

lemma tstake_infinite_lub: assumes "#\<surd>ts = \<infinity>" shows "#\<surd>(\<Squnion>i. (ts \<down> i)) = \<infinity>"
by (simp add: assms finite_chain_def tstake_infinite_chain)

lemma ts_below_eq: assumes "#\<surd> ts1 = \<infinity>" and "ts1 \<sqsubseteq> ts2"
  shows "ts1 = ts2"
using assms(1) assms(2) ts_approxl by fastforce

lemma tstake_inf_lub: assumes "#\<surd> ts = \<infinity>" shows "(\<Squnion>i. (ts \<down> i ) )= ts"
proof -
  have f1: "(\<Squnion>i. (ts \<down> i ) ) \<sqsubseteq> ts" by (simp add: lub_below)
  have "#\<surd>(\<Squnion>i. (ts \<down> i ) ) = \<infinity>" using assms tstake_infinite_lub by blast
  thus ?thesis using local.f1 ts_below_eq by blast 
qed

lemma tstake_lub [simp]: "(\<Squnion>i. (ts \<down> i ) )= ts"
  apply(cases "#\<surd>ts < \<infinity>")
   apply (metis (mono_tags) finite_chain_def infI less_irrefl maxinch_is_thelub tstake_fin tstake_finite tstake_maxinch)
  by (simp add: less_le tstake_inf_lub)


lemma tsttake_dom [simp]: "tsDom\<cdot>(ts \<down> n) \<subseteq> tsDom\<cdot>ts"
by (metis tsTakeDrop tsdom_conc)


lemma tstake2tsnth_eq: "ts1 \<down> n  = ts2 \<down> n \<Longrightarrow> i<n \<Longrightarrow> tsNth i\<cdot>ts1 = tsNth i\<cdot>ts2"
  apply(induction i arbitrary: n ts1 ts2)
   apply (simp add: tsNth_def)
   apply (metis Suc_pred below_bottom_iff tsTake_prefix tstake_below tstake_noteq tstakefirst_eq)
  apply(simp add: tsNth_Suc)
  by (smt Suc_lessE strictI tsConc_notEq tsTake_def2 tsTake_prefix tstakefirst_eq tstakefirst_len)


lemma tstake_bot: "ts1 \<down> (Suc n) = \<bottom> \<Longrightarrow> ts1 = \<bottom>"
by (metis Fin_02bot Rep_cfun_strict1 Zero_not_Suc bottomI inject_Fin lnle_def lnzero_def min_def tsTake.simps(1) ts_0ticks tstake_len)

lemma tstakefirst_eq2: assumes "ts1 \<down> (Suc n) = ts2 \<down> (Suc n)" shows " tsTakeFirst\<cdot>ts1 = tsTakeFirst\<cdot>ts2"
by (metis assms tsTake_prefix tstake_bot tstakefirst_eq)


lemma [simp]: "ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirst\<cdot>(tsTakeFirst\<cdot>ts) = \<bottom>"
by(simp add: tstakefirst_insert tsdropfirst_insert)




lemma tsdropfirst_conc: "ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirst \<cdot>(ts \<bullet> as) = (tsDropFirst\<cdot>ts) \<bullet> as"
apply(simp add: tsdropfirst_insert tsconc_insert)
by (simp add: Rep_tstream_bottom_iff srtdw_conc)

lemma [simp]: "ts \<noteq>\<bottom> \<Longrightarrow> tsDropFirst\<cdot>((tsTakeFirst\<cdot>ts) \<bullet> as ) = as"
  apply(simp add: tstakefirst_insert tsconc_rep_eq tsdropfirst_insert)
  by (smt Abs_tstream_bottom_iff Rep_tstream_inject Rep_tstream_strict mem_Collect_eq sconc_fst_empty srtdw_stwbl stwbl_eps tsconc_rep_eq tsdropfirst_conc tsdropfirst_insert tsdropfirst_rep_eq tstakefirst_well1)

lemma tstakefirst_conc: "ts\<noteq>\<bottom> \<Longrightarrow> tsTakeFirst\<cdot>(ts \<bullet> as ) =  tsTakeFirst\<cdot>ts"
by (metis Rep_tstream_inverse Rep_tstream_strict minimal monofun_cfun_arg sconc_snd_empty tsconc_insert tstakefirst_eq)


lemma [simp]:  "ts \<noteq>\<bottom> \<Longrightarrow> tsTakeFirst\<cdot>((tsTakeFirst\<cdot>ts) \<bullet> xs ) = tsTakeFirst\<cdot>ts"
  apply(simp add: tstakefirst_insert tsconc_insert)
  by (simp add: Rep_tstream_bottom_iff stwbl_conc)


lemma tsTake2take [simp]: "ts \<down> n \<down> n = ts \<down> n"
  apply(cases "ts=\<bottom>")
   apply simp
  apply(induction n arbitrary:ts)
   apply simp
  apply (auto simp add: tsTake.simps)
  by (metis below_bottom_iff tsTake_prefix)

(* Each chain becomes finite by mapping @{term "stake n"} to every element *)
lemma ts_finite_chain_stake: "chain Y \<Longrightarrow> finite_chain (\<lambda>i. tsTake n\<cdot>(Y i))"
proof -
  assume a1: "chain Y"
  have f2: "\<And>n t. max_in_chain n (tsTake_abbrv (t::'a tstream)) \<or> t \<noteq> t \<down> n"
    by (simp add: maxinch_is_thelub)
  have f3: "\<And>f n. finite_chain f \<or> \<not> max_in_chain n (tsTake_abbrv (Lub f::'a tstream)) \<or> \<not> chain f"
    using ts_infinite_lub tstake_infinite_chain by blast
  have "\<And>n t. max_in_chain n (tsTake_abbrv t::'a tstream \<down> n )"
    using f2 by (metis tsTake2take)
  then show ?thesis
    using f3 a1 by (metis chain_monofun contlub_cfun_arg)
qed

lemma tsDropTake: "(tsDropFirst\<cdot>(ts \<down> (Suc n))) \<down> n = (tsDropFirst\<cdot>ts) \<down>  n"
by(auto simp add: tsTake.simps)

lemma tsSucTake: 
  shows "ts1 \<down> (Suc n) = ts2 \<down> (Suc n) \<Longrightarrow> ts1 \<down> n = ts2 \<down> n"
apply(induction n arbitrary: ts1 ts2)
apply simp
by (metis tsDropTake tsTake_def2 tstakefirst_eq2)

lemma ts_take_eq: assumes "\<And>n. ts1 \<down>n = ts2 \<down> n"
  shows "ts1 = ts2"
proof -
  have "(\<Squnion>i. (ts1 \<down> i)) = (\<Squnion>i. (ts2 \<down> i))" by (simp add: assms)
  thus ?thesis by simp
qed

lemma tsnth2tstake_eq: assumes "\<And>n. n<i \<Longrightarrow> tsNth n\<cdot>ts1 = tsNth n\<cdot>ts2"
  shows "ts1 \<down> i = ts2 \<down> i"
using assms apply (induction i)
apply simp
by(simp add: tstake_tsnth)

lemma tstake_tick [simp] :"(Abs_tstream (\<up>\<surd>) \<bullet> ts) \<down> (Suc n)= Abs_tstream (\<up>\<surd>) \<bullet> (ts \<down> n)"
apply(simp add: tsTake_def2 tstakefirst_insert tsconc_rep_eq)
by (metis (mono_tags, lifting) stwbl_f tick_msg tsConc_notEq tsTakeDropFirst tsconc_rep_eq tstakefirst_insert tstakefirst_len)


lemma ts_tsnth_eq: assumes "\<And>n. tsNth n\<cdot>ts1 = tsNth n\<cdot>ts2"
  shows "ts1 = ts2"
using assms ts_take_eq tsnth2tstake_eq by blast


lemma "tsNth n\<cdot>(ts \<down> (Suc n)) = tsNth n \<cdot> ts"
using tsTake2take tstake2tsnth_eq by blast

lemma tstake_less: assumes "ts1 \<down> n = ts2 \<down> n" and "i \<le> n"
  shows "ts1 \<down> i = ts2 \<down> i"
by (meson assms(1) assms(2) less_le_trans tsnth2tstake_eq tstake2tsnth_eq)

lemma tsDropTake1 [simp]: "tsDrop n\<cdot>(ts \<down> n) = \<bottom>"
  apply(induction n arbitrary: ts)
   apply simp
  apply(auto simp add: tstake_tsnth)
  by (metis tsConc_notEq tsTake2take tsTakeDropFirst tsTake_def2 tstake_tsnth tstakefirst_len)

lemma tsDropBot:  "tsDrop n\<cdot>ts = \<bottom> \<Longrightarrow> n\<le>i \<Longrightarrow> tsDrop i\<cdot>ts = \<bottom>"
by (metis tsDropTake1 tsTake2take tsTakeDrop tstake_fin3)

lemma tstake2 [simp]: "ts \<down> n \<down> m = ts \<down> min n m"
by (metis min.cobounded1 min_def tsTake2take tstake_fin3 tstake_less)



lemma tsDropTakeFirstConc: "ts \<noteq> \<bottom> \<Longrightarrow> (tsDropFirst\<cdot>(tsTakeFirst\<cdot>ts \<bullet> xs )) = xs"
apply(simp add: tsdropfirst_insert tstakefirst_insert)
by (smt Abs_tstream_inverse Rep_tstream_inject Rep_tstream_strict mem_Collect_eq sconc_fst_empty srtdw_stwbl strict_stwbl stwbl_notEps tsconc_rep_eq tsdropfirst_conc tsdropfirst_insert tsdropfirst_rep_eq tsdropfirst_well tstakefirst_well1)


lemma tsDropFirstConc: "#\<surd>ts = Fin 1 \<Longrightarrow> tsDropFirst\<cdot>(ts \<bullet> xs) = xs"
by (metis Fin_02bot Fin_Suc One_nat_def Rep_tstream_inverse Rep_tstream_strict cfcomp2 lnat.con_rews lnat.sel_rews(2) lnzero_def sconc_fst_empty strict_sfilter strict_slen ts_0ticks tsconc_insert tsdropfirst_conc tsdropfirst_len tstickcount_insert)

lemma snth_tscons[simp]: assumes "tsTickCount\<cdot>a = Fin 1 "
  shows "tsNth (Suc k)\<cdot>(a \<bullet> s) = tsNth k\<cdot>s"
by (simp add: assms tsDropFirstConc tsNth_Suc)

lemma tsTakeFirst_first[simp]: "#\<surd>ts = Fin 1  \<Longrightarrow> tsTakeFirst\<cdot>ts = ts"
by (metis (mono_tags, lifting) Fin_02bot Fin_Suc One_nat_def Rep_tstream_inverse Rep_tstream_strict bottomI lnat.sel_rews(2) lnzero_def sconc_snd_empty tsTakeDropFirst ts_0ticks tsconc_rep_eq tsdropfirst_len tstakefirst_insert tstakefirst_prefix tstakefirst_well1)


lemma tsTakeFirstConc: "#\<surd>ts = Fin 1 \<Longrightarrow> tsTakeFirst\<cdot>(ts \<bullet> xs) = ts"
by (metis (mono_tags, hide_lams) Fin_Suc One_nat_def Rep_tstream_inverse Rep_tstream_strict lnat.con_rews lnzero_def minimal monofun_cfun_arg sconc_snd_empty strict_sfilter strict_slen tsTakeFirst_first tsconc_insert tstakefirst_eq tstickcount_insert)




lemma tsnth_len [simp]: "#\<surd> tsNth n\<cdot>ts \<le> Fin 1"
apply(simp add: tsNth_def)
by (metis bottomI min.bounded_iff order_refl tsTake_prefix tstakeFirst_len tstake_len tstakefirst2first)

lemma tstake_conc [simp]: assumes "#\<surd>ts = Fin n"
  shows "(ts \<bullet> ts2) \<down> n = ts"
using assms apply(induction n arbitrary: ts)
apply (simp add: ts_0ticks)
apply (auto simp add: tsTake_def2)
apply(subst tsdropfirst_conc)
apply auto[1]
apply(subst tstakefirst_conc)
apply auto[1]
by (metis Fin_Suc Rep_tstream_strict inject_lnsuc lnat.con_rews lnzero_def strict_sfilter strict_slen tsTakeDropFirst tsdropfirst_len tstickcount_insert)

(* A finite prefix of length @{term "k"} is created by @{term "stake k"} *)
lemma ts_approxl1: "\<forall>s1 s2. s1 \<sqsubseteq> s2 \<and> (#\<surd> s1) = Fin k \<longrightarrow> tsTake k\<cdot>s2 = s1"
using ts_approxl tstake_conc by blast

(* A prefix of a stream is equal to the original one or a finite prefix *)
lemma ts_approxl2: "s1 \<sqsubseteq> s2 \<Longrightarrow> (s1 = s2) \<or> (\<exists>n. tsTake n\<cdot>s2 = s1 \<and> Fin n = #\<surd>s1)"
by (metis ts_approxl1 ninf2Fin ts_below_eq)

lemma tsconc_eq: "#\<surd>ts1 = #\<surd>ts2 \<Longrightarrow> (ts1 \<bullet> a1) = (ts2 \<bullet> a2) \<Longrightarrow> ts1 = ts2"
by (metis lncases tsconc_id tstake_conc)

lemma tsnth_more: assumes "#\<surd>ts = Fin n" and "n\<le>i"  shows "tsNth i\<cdot>ts = \<bottom>"
  using assms apply(induction i arbitrary: ts n)
   apply simp
   using ts_0ticks apply fastforce
proof -
  fix ia :: nat and tsa :: "'a tstream" and na :: nat
  assume a1: "#\<surd> tsa = Fin na"
  assume "na \<le> Suc ia"
  then have "tsDrop (Suc ia)\<cdot>tsa = \<bottom>"
    using a1 by (metis tsDropBot tsDropTake1 tstake_fin)
  then show "tsNth (Suc ia)\<cdot>tsa = \<bottom>"
    by (simp add: tsNth_def)
qed

lemma tsnth_less: "tsNth i\<cdot>ts = \<bottom> \<Longrightarrow> #\<surd>ts \<le> Fin i"
  apply(induction i arbitrary: ts)
   apply (simp add: tsNth_def)
   using tstakefirst_bot apply fastforce
  apply(simp add: tsNth_Suc)
  by (metis Fin_Suc Rep_tstream_strict lnle_def lnsuc_lnle_emb lnzero_def minimal strict_sfilter strict_slen tsdropfirst_len tstickcount_insert)



lemma ts_take_below: assumes "(\<And>i. x\<down>i \<sqsubseteq> y \<down>i)"
  shows "x\<sqsubseteq>y"
proof -
  have "(\<Squnion>i. (x\<down>i)) \<sqsubseteq> (\<Squnion>i. (y \<down> i))" using assms lub_mono tstake_chain by blast
  thus ?thesis by simp
qed


lemma tstake_less_below: assumes "x\<sqsubseteq>y" and "Fin i\<le>#\<surd> x"
  shows "x\<down>i = y\<down>i"
by (smt assms(1) assms(2) min.absorb2 tsTakeDrop ts_approxl tsconc_assoc tstake_conc tstake_len)

(* every finite prefix of the lub is also prefix of some element in the chain *)
lemma ts_lub_approx: "chain Y \<Longrightarrow> \<exists>k. tsTake n\<cdot>(lub (range Y)) = tsTake n\<cdot>(Y k)"
by (metis exist_tslen finite_chain_def is_ub_thelub maxinch_is_thelub tstake_less_below)

lemma tstake_below_eq: assumes "x\<sqsubseteq>y" and "#\<surd> x = #\<surd>y"
  shows "x = y"
by (metis assms(1) assms(2) below_refl ts_approxl tsconc_eq)

(* If two timed streams of same length agree on every element, all their finite prefixes are equal *)
lemma tsnths_eq_lemma [rule_format]: 
  "\<forall>x y. (#\<surd>x) = (#\<surd>y) \<and> (\<forall>n. Fin n < (#\<surd>x) \<longrightarrow> tsNth n\<cdot>x = tsNth n\<cdot>y) 
           \<longrightarrow>tsTake  k\<cdot>x = tsTake k\<cdot>y"
by (smt less2nat_lemma less_SucI min.commute min_def not_less trans_lnle 
    tsDropNth tsDropTake1 tsTakeDrop tsTake_prefix tsnth2tstake_eq tsnth_len 
    tstake_below_eq tstake_len)

(* If two timed streams of same length agree on every element, they are equal *)
lemma tsnths_eq: "\<lbrakk>(#\<surd>x) = (#\<surd>y); \<forall>n. Fin n < (#\<surd>x) \<longrightarrow> tsNth n\<cdot>x = tsNth n\<cdot>y\<rbrakk> \<Longrightarrow> x = y"
using ts_take_eq tsnths_eq_lemma by blast

lemma ts_below: assumes "\<And>i. Fin i \<le>#\<surd>x \<Longrightarrow> x\<down>i = y\<down>i"
  shows "x\<sqsubseteq>y"
  apply(rule ts_take_below, rename_tac i)
  apply(induct_tac i)
   apply simp
  apply simp
  apply(case_tac "Fin (Suc n)\<le>#\<surd>x")
   apply (simp add: assms)
  by (smt box_below leI le_cases less2lnleD min_def tstake_below tstake_below_eq tstake_len)

  
lemma ts_existsNBot[simp]: "\<exists>ts :: 'a tstream. ts\<noteq>\<bottom>"
proof -
  have "Abs_tstream (\<up>\<surd>) \<noteq> \<bottom>" by simp
  thus ?thesis by blast 
qed

lemma tstakeBot: "y \<down> i  = \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> x \<down> i  = \<bottom>"
apply(cases "i=0")
apply simp
by (metis list_decode.cases tstake_bot)

(*tsntimes tsinftimes*)

(*1 times a timed stream is the timed stream itself*)
lemma tsntimes_id[simp]: "tsntimes (Suc 0) ts = ts"
by simp

(*times a timed stream is \<bottom>*)
lemma ts0tmsSubTs1tms: "tsntimes 0 ts1 \<sqsubseteq> ts2"
by simp

(*Concatenation to @{term tsntimes} is commutative*)
lemma tsConc_eqts_comm: "ts \<bullet> (tsntimes n ts) =(tsntimes n ts) \<bullet> ts"
apply (induct_tac n)
apply simp
by simp

(*Concatenation of a timed stream to @{term tsntimes} of the same timed stream is Suc n times the timed stream *)
lemma tsntmsSubTsSucntms: "tsntimes (Suc n) ts = (tsntimes n ts) \<bullet> ts"
using tsConc_eqts_comm
using tsntimes.simps(2) by auto

(*n times a timed stream is prefix of Suc n times a stream*)
lemma tsSucntmsSubTsinftms: "tsntimes n ts \<sqsubseteq> tsntimes (Suc n) ts"
using ts_tsconc_prefix tsntmsSubTsSucntms
by metis

(*If a timed stream is not \<bottom>, then it contains some \<surd>*)
lemma lenmin: assumes "ts \<noteq>\<bottom> "
 shows "(#\<surd>(ts)) > 0"
using assms lnless_def ts_0ticks by fastforce


(*ntimes a finite timed stream is still a finite timed stream*)
lemma fintsntms2fin:assumes "#\<surd>ts < \<infinity>"
 shows "#\<surd>(tsntimes n ts) < \<infinity>"
using assms tsntmsSubTsSucntms
apply(induct_tac n)
apply(simp add: tsntimes_def)
apply (smt fold_inf)
proof -
  fix na :: nat
  assume a1: "#\<surd> tsntimes na ts < \<infinity>"
  assume a2: "#\<surd> ts < \<infinity>"
  { assume "#\<surd> tsntimes na ts \<noteq> \<infinity>"
    moreover
    { assume "tsntimes na ts \<noteq> tsntimes (Suc na) ts"
      then have "tsntimes na ts \<noteq> ts \<bullet> tsntimes na ts"
        by (metis tsntimes.simps(2))
      then have "#\<surd> ts \<bullet> tsntimes na ts \<noteq> \<infinity>"
        using a2 by (metis (full_types) tsConc_eqts_comm tsConc_notEq tsconc_id tsntimes.simps(2))
      then have "#\<surd> tsntimes (Suc na) ts \<noteq> \<infinity>"
        by (metis tsntimes.simps(2)) }
    ultimately have "#\<surd> tsntimes (Suc na) ts \<noteq> \<infinity>"
      by force }
  then show "#\<surd> tsntimes (Suc na) ts < \<infinity>"
    using a1 by (metis (no_types) inf_less_eq leI)
qed


end





