(*  Title:        TStreamTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Definition of "Timed Streams"
*)

chapter {* Timed Streams *}                                                              

theory TStream

imports  Streams
begin
default_sort countable
setup_lifting type_definition_cfun


(* ----------------------------------------------------------------------- *)
section {* Type definition *}
(* ----------------------------------------------------------------------- *)


text {* Definition of  datatype  @{text "'m event"}; extends @{text "'m"} with a @{term "Tick"}. *}
datatype 'm event = Msg 'm ( "\<M> _" 65)| Tick

text {* Inverse of Msg.*}
abbreviation
  inversMsg ::  "'a event \<Rightarrow> 'a"  ("\<M>\<inverse> _")
    where "inversMsg e \<equiv> ( case e of \<M> m \<Rightarrow> m)"

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
definition tsMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tstream \<rightarrow> 'b tstream" where
"tsMap f \<equiv> \<Lambda> s. espf2tspf (smap (\<lambda>x. case x of Msg m \<Rightarrow> Msg (f m) | \<surd> \<Rightarrow> \<surd>)) s"

text {* "Unzipping" of timed streams: project to the first element of a tuple of tstreams. *}
definition tsProjFst :: "('a \<times> 'b) tstream \<rightarrow> 'a tstream" where
"tsProjFst = tsMap fst"

text {* "Unzipping" of timed streams: project to the second element of tuple of tstreams. *}
definition tsProjSnd :: "('a \<times> 'b) tstream \<rightarrow> 'b tstream" where
"tsProjSnd = tsMap snd"

text {* @{term tsFilter}: Remove all elements from the tstream which are
  not included in the given set. *}
definition tsFilter :: "'a set \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsFilter M \<equiv> \<Lambda> ts. Abs_tstream (insert \<surd> (Msg ` M) \<ominus> Rep_tstream ts)"

text {* Fairness predicate on timed stream processing function. An espf is considered fair
  if all inputs with infinitely many ticks are mapped to outputs with infinitely many ticks. *}
definition tspfair :: "('a tstream \<rightarrow> 'b tstream ) \<Rightarrow> bool" where
"tspfair f \<equiv> \<forall>ts. tsTickCount\<cdot> ts = \<infinity> \<longrightarrow> tsTickCount \<cdot> (f\<cdot> ts) = \<infinity>"
    

        
lift_definition uMsg :: "'a discr \<rightarrow> 'a event discr" is
"\<lambda> t. case t of (Discr m) \<Rightarrow> (Discr (Msg m))"
  by(simp add: cfun_def)


(* remove the Msg layer. Return bottom on ticks *)
lift_definition unpackMsg::"'a event discr u \<rightarrow> 'a discr u" is
  "\<lambda>t. upApply (\<lambda>x. case x of Msg m \<Rightarrow> m )\<cdot>t"
  using Cfun.cfun.Rep_cfun by blast
  
    
thm lshd_def  (* similar to lshd *)  
(* get First Element of tStream *)
definition tsLshd :: "'a tstream \<rightarrow> 'a event discr u" where
"tsLshd \<equiv> \<Lambda> ts.  lshd\<cdot>(Rep_tstream ts)"

  
(* get rest of tStream *)
thm srt_def   (* similar to srt *)
definition tsRt :: "'a tstream \<rightarrow> 'a tstream" where
"tsRt \<equiv> \<Lambda> ts. espf2tspf srt ts"
  
(* create new tStream by appending a new first Element *)
  (* sadly the function must be ts_well... 
  .. hence for the input (updis Msg m) and the empty stream a special case must be made *)
thm lscons_def (* similar to lscons *)
definition tsLscons :: "'a event discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsLscons \<equiv> \<Lambda> t ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts"

(* append a Message as first element. 
  Returns bot if the tstream is bot *)
definition tsMLscons :: "'a discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsMLscons \<equiv> \<Lambda> t ts. tsLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"

definition DiscrTick :: "'a event discr" where
  "DiscrTick = Discr \<surd>"



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

lemma msg_nwell [simp]: "\<not>ts_well (\<up>(Msg m))"
apply (simp add: ts_well_def, auto)
by (metis Inf'_neq_0 event.distinct(1) fold_inf inf_ub inject_lnsuc less_le lscons_conv sfoot1
    sfoot_one slen_scons strict_slen sup'_def)

lemma msg_nwell2: "t\<noteq>\<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> \<not>ts_well (t && \<bottom>)"
apply (simp add: ts_well_def, auto)
using sfilter_srt_sinf apply fastforce
by (metis sfoot1 sfoot_one sup'_def updis_exists)

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
  hence "Msg a \<in> (\<Union>i. sdom\<cdot>(Rep_tstream (Y i)))" by (simp add: lub_eq_Union)
  hence "(a \<in> (\<Squnion>i. {u. Msg u \<in> sdom\<cdot>(Rep_tstream (Y i))}))" by (simp add: lub_eq_Union)
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

(* appending to a singleton tstream can never yield the empty stream *)
lemma [simp]: "\<bottom> \<noteq> Abs_tstream(\<up>\<surd>) \<bullet> as"
by (simp add: tsconc_insert)

lemma [simp]: "Abs_tstream(\<up>\<surd>) \<bullet> as \<noteq> \<bottom>"
by (simp add: tsconc_insert)

(* the singleton tstream is never equal to the empty stream *)
lemma [simp]: "Abs_tstream(\<up>\<surd>) \<noteq> \<bottom>"
by simp

lemma ts_well_sing_conc: "ts_well (\<up>a\<bullet>\<up>\<surd>)"
by (simp add: ts_well_def)

(* singleton in first time slot are only in an ordered relation if the two elements are equal *)
lemma [simp]: "(Abs_tstream(\<up>a\<bullet>\<up>\<surd>) \<sqsubseteq> Abs_tstream((\<up>b\<bullet>\<up>\<surd>))) = (a = b)"
apply (rule iffI)
apply (simp add: below_tstream_def ts_well_sing_conc)
apply (metis less_all_sconsD)
by simp

(* uparrow is a bijection *)
lemma "\<up>(Msg a)= \<up>(Msg b) = (a=b)"
by simp

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

lemma tsabs_bot[simp]: "tsAbs\<cdot>\<bottom>=\<bottom>"
  by(simp add: tsabs_insert)
  

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

text {* If for every stream, which has either infinite many ticks, or is finite, a property P holds,
then the property P holds for any timed stream. *}
lemma PAbs_tstreamI: "\<lbrakk>\<And>x. #\<surd>x = \<infinity> \<or> #\<surd>x \<noteq> \<infinity>  \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (Abs_tstream y)"
using tstreaml1 
apply blast
done

(* tsTakdaneFirst *)



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

(*event stream with one element just contain \<surd>, or are not ts_well*)
lemma tsOneTick: "(\<up>e) \<noteq> (\<up>\<surd>) \<Longrightarrow> \<not> ts_well (\<up>e)"
apply (simp add: ts_well_def)
by (metis (mono_tags, lifting) Inf'_def Inf'_neq_0 bot_is_0 fix_strict lscons_conv sfoot_one slen_scons stakewhileFromTS2 strict_slen stwbl_f sup'_def tick_msg ts_finite_sfoot ts_well_def)


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

lemma [simp]: "tsTakeFirst\<cdot>(Abs_tstream(\<up>\<surd>)) = Abs_tstream(\<up>\<surd>)"
apply (simp add: tstakefirst_insert)
apply (subst stwbl_def [THEN fix_eq2])
by (simp)

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
apply simp
  by (simp add: sdrop_forw_rt)

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

lemma [simp]: "tsDropFirst\<cdot>(tsTakeFirst\<cdot> ts) = \<bottom>"
apply (simp add: tsDropFirst_def tsTakeFirst_def)
done


lemma [simp]: "tsDropFirst\<cdot>\<bottom> = \<bottom>"
by(simp add: tsdropfirst_insert)


lemma tsTakeDropFirst [simp]: "tsTakeFirst\<cdot>ts \<bullet> tsDropFirst\<cdot>ts = ts"
by (metis (no_types, lifting) Abs_tstream_inverse Rep_tstream Rep_tstream_inverse mem_Collect_eq stwbl_srtdw tsconc_insert tsdropfirst_insert tsdropfirst_well tstakefirst_insert tstakefirst_well)

(* the rest of the singleton tstream is empty *)
lemma [simp]: "tsDropFirst\<cdot>(Abs_tstream(\<up>\<surd>)) = \<bottom>"
by (simp add: tsdropfirst_insert)

(* tsDrop *)
thm tsDrop_def

lemma [simp]: "tsDrop i\<cdot>\<bottom> = \<bottom>"
apply(induction i)
apply(simp)
by(simp add: tsDrop_def)

(*To drop n+1 timeslots is the same as dropping n timeslots and then one *)
lemma tsDrop_tsDropFirst: "tsDrop (Suc n)\<cdot> x = tsDrop n\<cdot> (tsDropFirst\<cdot> x)"
by simp

lemma tsDropNth: "tsDrop n\<cdot>ts = (tsNth n\<cdot>ts) \<bullet> tsDrop (Suc n)\<cdot>ts"
apply(induction n arbitrary: ts)
apply (simp add: tsNth_def)
by (simp add: tsNth_def)

lemma tsdrop_tick [simp] :"tsDrop (Suc n)\<cdot>(Abs_tstream (\<up>\<surd>) \<bullet> ts) = tsDrop n\<cdot>ts"
by(simp add: tsDrop.simps tsdropfirst_insert tsconc_rep_eq)

lemma [simp]: "tsDrop 0\<cdot> x = x"
by (simp add: tsDrop_def)

(* tsNth *)
lemma [simp]: "tsNth i\<cdot>\<bottom> = \<bottom>"
by(simp add: tsNth_def)

lemma tsNth_Suc: "tsNth (Suc i)\<cdot>ts = tsNth i\<cdot>(tsDropFirst\<cdot>ts)"
by (simp add: tsNth_def)

(* The first element of a stream is equal to the element on the zeroth position *)
lemma tsnth_shd[simp]: "tsNth 0\<cdot>s = tsTakeFirst\<cdot>s"
by (simp add: tsNth_def)


(* tsTickCount *)
lemma strict_tstickcount[simp]: "#\<surd> \<bottom> = 0"
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

text {* In infinite chains, the length of the streams is unbounded *}
lemma inf_chainl3:
  "chain Y \<and> \<not>finite_chain Y \<longrightarrow> (\<exists>k. Fin n \<le> #\<surd>(Y k))"
by (simp add: exist_tslen)



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

text {* Appending to an inifite tstream does not change its @{text "n"}th element *}
lemma tsconc_fst_inf_lemma: "\<forall>x. #\<surd>x=\<infinity> \<longrightarrow> tstake n\<cdot>(x\<bullet>y) = tstake n\<cdot>x"
by simp

(* concatenating finite tstreams produces another finite tstream *)
lemma tsconc_tstickcount[simp]: assumes "(#\<surd>s)<\<infinity>" and "(#\<surd>xs)<\<infinity>"
  shows "(#\<surd>(s\<bullet>xs))<\<infinity>"
by (metis Fin_neq_inf assms(1) assms(2) infI inf_ub lnle_def lnless_def stickcount_conc)

(* prepending a singleton tstream increases the length by 1 *)
lemma tstickcount_tscons[simp]: "#\<surd>(Abs_tstream(\<up>\<surd>)\<bullet>as) = lnsuc\<cdot>(#\<surd>as)"
by (simp add: tstickcount_insert tsconc_rep_eq)

(* the singleton tstream has length 1 *)
lemma [simp]: "#\<surd>Abs_tstream(\<up>\<surd>) = Fin (Suc 0)"
by (simp add: tstickcount_rep_eq)

(* only the empty tstream has length 0 *)
lemma tstickcount_empty_eq[simp]: "(#\<surd>x = 0) = (x = \<bottom>)"
apply (rule iffI)
apply (simp add: ts_0ticks) 
by simp


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

(* tsWeak- and tsStrongCasuality*)

definition tsWeakCausal:: "('a tstream \<Rightarrow> 'b tstream) \<Rightarrow> bool" where
"tsWeakCausal \<equiv> \<lambda>f. \<forall>i ts1 ts2. (ts1 \<down> i = ts2 \<down> i) \<longrightarrow> (f ts1) \<down> i = (f ts2) \<down> i"

definition tsStrongCausal:: "('a tstream \<Rightarrow> 'b tstream) \<Rightarrow> bool" where
"tsStrongCausal \<equiv> \<lambda>f. \<forall>i ts1 ts2. (ts1 \<down> i = ts2 \<down> i) \<longrightarrow> (f ts1) \<down> (Suc i) = (f ts2) \<down> (Suc i)"

lemma tsWeakCausalI: fixes f::"('a tstream \<Rightarrow> 'b tstream)"
  assumes "\<And>i ts1 ts2. (ts1 \<down> i = ts2 \<down> i) \<Longrightarrow> (f ts1) \<down>  i = (f ts2) \<down> i"
  shows "tsWeakCausal f"
by (metis assms tsWeakCausal_def)

lemma tsStrongCausalI: fixes f::"('a tstream \<Rightarrow> 'b tstream)"
  assumes "\<And>i ts1 ts2. (ts1 \<down>i = ts2 \<down> i) \<Longrightarrow> (f ts1) \<down> (Suc i) = (f ts2) \<down> (Suc i)"
  shows "tsStrongCausal f"
by (meson assms tsStrongCausal_def)

lemma tsStrong2Weak: "tsStrongCausal f \<Longrightarrow> tsWeakCausal f"
by (meson tsStrongCausal_def tsWeakCausalI tsSucTake)

lemma tsWeak_eq: assumes "tsWeakCausal f" and "x\<down>i = y\<down>i"
  shows "(f x)\<down>i = (f y) \<down>i"
by (meson assms(1) assms(2) tsWeakCausal_def)

lemma tsWeak2Mono: assumes "tsWeakCausal f" and "\<And>x. #\<surd>f x \<le> #\<surd> x"
  shows "monofun f"
apply (rule monofunI)
apply (rule ts_below)
using assms(1) assms(2) tsWeak_eq trans_lnle tstake_less_below by blast

lemma tsMono2Weak: assumes "monofun f" and "\<And>x. #\<surd> x \<le> #\<surd> f x"
  shows "x \<down> i  = y \<down> i  \<Longrightarrow> (f x) \<down> i  = (f y) \<down> i"
apply (induction i arbitrary: x y, auto)
apply (subst tstake_tsnth)
apply (subst tstake_tsnth)
by (smt assms(1) assms(2) min_def monofun_def tsTake_prefix tstake_below_eq tstake_len
    tstake_less_below tstake_tsnth)

lemma tsMono2Weak2: assumes "monofun f" and "\<And>x. #\<surd> x \<le> #\<surd> f x"
  shows "tsWeakCausal f"
using assms(1) assms(2) tsMono2Weak tsWeakCausalI by blast

lemma tsMonoEqWeak: "(\<And>x. #\<surd> x = #\<surd> f x) \<Longrightarrow> monofun f \<longleftrightarrow> tsWeakCausal f"
by (metis (mono_tags, lifting) order_refl tsMono2Weak tsWeak2Mono tsWeakCausal_def)

lemma [simp]: "tsWeakCausal f \<Longrightarrow> (\<And>x. #\<surd>f x \<le> #\<surd> x) \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. f (Y i))"
using ch2ch_monofun tsWeak2Mono by blast

lemma tsWeak_lub: assumes "tsWeakCausal f" and "\<And>x. #\<surd>f x = #\<surd> x" and "chain Y"
  shows "f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
proof (cases "finite_chain Y")
  case True 
  have "\<And>x. #\<surd>f x \<le> #\<surd> x" by (simp add: assms(2)) 
  thus ?thesis by (metis assms(1) assms(2) assms(3) finite_chain_lub tsWeak2Mono True)  
next
  case False
  hence "#\<surd>(\<Squnion>i. Y i) = \<infinity>" using assms(3) ts_infinite_lub by blast
  have assms2: "\<And>x. #\<surd>f x \<le> #\<surd> x" by (simp add: assms(2)) 
  show ?thesis
  proof (rule ts_take_eq)
    fix n
    obtain i where "Fin n < #\<surd>Y i" by (meson False Suc_n_not_le_n assms(3) exist_tslen less2nat less_le_trans not_less)
    hence eq1: "(f (\<Squnion>i. Y i)) \<down> n = (f (Y i)) \<down> n"
      by (metis assms(1) assms(3) is_ub_thelub less_le tsWeak_eq tstake_less_below)
    have eq2: "(\<Squnion>i. f (Y i)) \<down> n =  (f (Y i)) \<down> n"
      by (metis \<open>Fin n < #\<surd> Y i\<close> assms(1) assms2 assms(2) assms(3) is_ub_thelub less_le monofun_def po_class.chain_def tsWeak2Mono tstake_less_below)
    show "(f (\<Squnion>i. Y i)) \<down> n  = (\<Squnion>i. f (Y i)) \<down> n " by (simp add: eq1 eq2) 
  qed
qed

lemma tsWeak2cont: assumes "tsWeakCausal f" and "\<And>x. #\<surd>f x = #\<surd> x"
  shows "cont f"
apply (rule contI2)
apply (simp add: assms(1) assms(2) tsWeak2Mono)
by (simp add: assms(1) assms(2) tsWeak_lub)

lemma tsWeak2cont2: assumes "\<And>x. #\<surd>f x = #\<surd> x"
  shows "tsWeakCausal f \<longleftrightarrow> cont f"
apply rule
using assms tsWeak2cont apply blast
by (simp add: assms cont2mono tsMono2Weak2)

lemma tsMono2weak2cont: assumes "\<And>x. #\<surd>f x = #\<surd> x"
  shows"monofun f \<longleftrightarrow> cont f"
apply (subst tsMonoEqWeak)
using assms apply simp
apply (subst tsWeak2cont2, auto)
using assms by simp

lemma monoweak_lub_below: assumes "monofun f" and "tsWeakCausal f" and "chain Y"
  shows "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
proof -
  have h1: "\<forall>n. (f (Y n)) \<sqsubseteq> (\<Squnion>i. f (Y i))"
    using assms(1) assms(3) ch2ch_monofun is_ub_thelub by blast
  hence h2: "\<forall>n. (f (\<Squnion>i. Y i)) \<down> n \<sqsubseteq> (\<Squnion>i. f (Y i)) \<down> n"
    by (metis assms(2) assms(3) monofun_cfun_arg tsWeak_eq ts_lub_approx)
  thus "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
    using ts_take_below by blast
qed

lemma monoweak2cont: assumes "monofun f" and "tsWeakCausal f"
  shows "cont f"
by (simp add: contI2 assms(1) assms(2) monoweak_lub_below)

(* The type of weak causal functions *)

(* Definition of weak causal function type *)

definition "spfw = {f ::'a tstream => 'b tstream. tsWeakCausal f}"

lemma bottom_spfw: "\<bottom> \<in> spfw"
by (simp add: spfw_def tsWeakCausal_def)

(* tsTake is cont, tsTake is chain *)
lemma adm_spfw: "adm (\<lambda>x. x \<in> spfw)"
apply (simp only: spfw_def tsWeakCausal_def adm_def mem_Collect_eq)
by (metis (mono_tags, lifting) ch2ch_fun contlub_cfun_arg lub_eq lub_fun)

pcpodef ('a, 'b) spfw ("(_ \<leadsto>w/ _)" [1, 0] 0) = "spfw :: ('a tstream => 'b tstream) set"
apply (simp add: bottom_spfw)
by (simp add: adm_spfw)

(* Syntax for weak causal lambda abstraction *)

syntax "_wabs" :: "[logic, logic] \<Rightarrow> logic"

parse_translation \<open>
(* Rewrite (_wabs x t) => (Abs_spfw (%x. t)) *)
  [Syntax_Trans.mk_binder_tr (@{syntax_const "_wabs"}, @{const_syntax Abs_spfw})];
\<close>

print_translation \<open>
  [(@{const_syntax Abs_spfw}, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const @{syntax_const "_wabs"} $ x $ t end)]
\<close>  \<comment> \<open>To avoid eta-contraction of body\<close>

(* Syntax for nested abstractions *)

syntax (ASCII)
  "_L" :: "[cargs, logic] \<Rightarrow> logic"  ("(3L _./ _)" [1000, 10] 10)

syntax
  "_L" :: "[cargs, logic] \<Rightarrow> logic" ("(3\<L> _./ _)" [1000, 10] 10)

parse_ast_translation \<open>
(* Rewrite (L x y z. t) => (_wabs x (_wabs y (_wabs z t))) *)
(* cf. Syntax.l_ast_tr from src/Pure/Syntax/syn_trans.ML *)
  let
    fun L_ast_tr [pats, body] =
          Ast.fold_ast_p @{syntax_const "_wabs"}
            (Ast.unfold_ast @{syntax_const "_cargs"} (Ast.strip_positions pats), body)
      | L_ast_tr asts = raise Ast.AST ("L_ast_tr", asts);
  in [(@{syntax_const "_L"}, K L_ast_tr)] end;
\<close>

print_ast_translation \<open>
(* rewrite (_wabs x (_wabs y (_wabs z t))) => (L x y z. t) *)
(* cf. Syntax.abs_ast_tr' from src/Pure/Syntax/syn_trans.ML *)
  let
    fun wabs_ast_tr' asts =
      (case Ast.unfold_ast_p @{syntax_const "_wabs"}
          (Ast.Appl (Ast.Constant @{syntax_const "_wabs"} :: asts)) of
        ([], _) => raise Ast.AST ("wabs_ast_tr'", asts)
      | (xs, body) => Ast.Appl
          [Ast.Constant @{syntax_const "_L"},
           Ast.fold_ast @{syntax_const "_cargs"} xs, body]);
  in [(@{syntax_const "_wabs"}, K wabs_ast_tr')] end
\<close>

(* Dummy patterns for weak causal abstraction *)
translations
  "\<L> _. t" => "CONST Abs_cfun (\<lambda> _. t)"

(* Basic properties for weak causal function type *)

lemma rep_spfw_cont[simp]: "cont Rep_spfw"
using cont_Rep_spfw cont_id by blast

lemma rep_spfw_chain2chain[simp]: "chain Y \<Longrightarrow> chain (\<lambda>i. Rep_spfw (Y i))"
by (simp add: ch2ch_cont)

lemma abs_spfw_cont: "\<forall>x. tsWeakCausal (f x) \<Longrightarrow> cont f \<Longrightarrow> cont (\<lambda>x. Abs_spfw (f x))"
using cont_Abs_spfw spfw_def by auto

(* Beta equality for weak causal functions *)
lemma abs_spfw_inverse2: "tsWeakCausal f \<Longrightarrow> Rep_spfw (Abs_spfw f) = f"
by (simp add: Abs_spfw_inverse spfw_def)

lemma rep_spwf_inverse[simp]: "Abs_spfw (Rep_spfw f) = f"
by (simp add: Rep_spfw_inverse)

lemma beta_spfw: "tsWeakCausal f \<Longrightarrow> Rep_spfw (\<L> x. f x) u = f u"
by (simp add: abs_spfw_inverse2)

lemma rep_spwf_strict[simp]: "Rep_spfw \<bottom> = \<bottom>"
by (simp add: Rep_spfw_strict)

lemma abs_spwf_strict[simp]: "Abs_spfw \<bottom> = \<bottom>"
by (simp add: Abs_spfw_strict)

(* Function application is strict in its first argument *)
lemma rep_spwf_strict1[simp]: "Rep_spfw \<bottom> x = \<bottom>"
by (simp add: Rep_cfun_strict)

lemma lam_strict[simp]: "(\<L> x. \<bottom>) = \<bottom>"
by (simp add: lambda_strict)

lemma [simp]: "tsWeakCausal f \<and> f\<noteq>\<bottom> \<Longrightarrow> Abs_spfw f \<noteq> \<bottom>"
using abs_spfw_inverse2 by fastforce

lemma [simp]: "Rep_spfw f\<noteq>\<bottom> \<Longrightarrow> f \<noteq> \<bottom>"
using Rep_spfw_strict by blast

lemma [simp]: "Abs_spfw f\<noteq>\<bottom> \<Longrightarrow> f \<noteq> \<bottom>"
using Abs_spfw_strict by blast

lemma abs_spfw_inverse2tsweak[simp]: "Rep_spfw (Abs_spfw f) = g \<Longrightarrow> tsWeakCausal g"
using Rep_spfw spfw_def by auto

lemma abs_spfw_inverse2tsweak2[simp]: "Rep_spfw (Abs_spfw f) = f \<Longrightarrow> tsWeakCausal f"
using Rep_spfw spfw_def by auto

lemma tsweak_bot[simp]: "tsWeakCausal \<bottom>"
by (metis bottom_spfw mem_Collect_eq spfw_def)

lemma tsweak_rep_spwf[simp]: "tsWeakCausal (Rep_spfw ts)"
using Rep_spfw spfw_def by auto

(*Definition of inftimes \<surd>*)

(* the tStream with just time *)
lift_definition tsInfTick :: "'m tstream" is "\<up>\<surd> \<infinity>"
by(simp add: ts_well_def)


lemma [simp]: "tsInfTick \<noteq> \<bottom>"
by(simp add: tsInfTick.rep_eq)

lemma [simp]: "tsAbs\<cdot>tsInfTick = \<epsilon>"
by(simp add: tsabs_insert tsInfTick.rep_eq sfilter_sdom_eps)

(* no message is transmitted *)
lemma [simp]: "tsDom\<cdot>tsInfTick = {}"
by(simp add: tsdom_insert tsInfTick.rep_eq)

lemma [simp]:  "tsDom\<cdot>(ts \<bullet> tsInfTick) = tsDom\<cdot>ts"
apply(cases "#\<surd>ts = \<infinity>")
apply simp
by(simp add: tsdom_tsconc less_le)

lemma [simp]: "#\<surd>tsInfTick = \<infinity>"
by(simp add: tstickcount_insert tsInfTick.rep_eq)

lemma [simp]: "#\<surd> (ts \<bullet> tsInfTick) = \<infinity>"
  apply(simp add: tstickcount_insert)
  apply(simp add: tsconc_insert)
  apply(cases "#\<surd> ts = \<infinity>")
   apply (simp add: tstickcount_insert)
  by (metis Abs_tstream_inverse mem_Collect_eq slen_sconc_snd_inf slen_sinftimes stream.con_rews(2) sup'_def tsInfTick.rep_eq tsInfTicks ts_well_conc tstickcount_insert up_defined)

lemma "tsInfTick \<down> 1 = (Abs_tstream ((\<up>\<surd>)))"
  apply (simp add: tsTake_def One_nat_def)
  apply(simp add: tstakefirst_insert tsInfTick.rep_eq)
  apply(subst sinftimes_unfold)
  by simp

lemma [simp]: "tsTakeFirst\<cdot>tsInfTick = Abs_tstream ((\<up>\<surd>))"
  apply(simp add: tstakefirst_insert tsInfTick.rep_eq)
  apply(subst sinftimes_unfold)
  by simp

lemma [simp]: "tsDropFirst\<cdot>tsInfTick = tsInfTick"
  apply(simp add: tsDropFirst_def "tsInfTick.rep_eq")
  apply(subst sinftimes_unfold)
  by (metis eq_onp_same_args sdrops_sinf sinftimes_unfold srtdw2drop tsInfTick.rsp tsInfTick_def)

lemma [simp]:"ts_well (n\<star>\<up>\<surd>)"
  by(induction n, simp_all)

lemma tsInfTick_take: "tsInfTick \<down> n = (Abs_tstream ((sntimes n (\<up>\<surd>))))"
  apply(induction n)
   apply simp
  by (simp add: tsConc_def tsTake.simps)

lemma tsInfTick_tsNth:  "tsNth n\<cdot>tsInfTick = Abs_tstream (\<up>\<surd>)"
  apply(induction n)
   apply (simp add: tsNth_def)
  by(simp add: tsNth_Suc)




(* ID Funktion*)

(* the identity function is monotonic & weak causal, but not strong Causal *)

definition tsId ::"'a tstream \<Rightarrow> 'a tstream" where
"tsId \<equiv> (\<lambda>ts :: 'a tstream. ts)"

lemma "monofun (tsId)"
apply(subst tsId_def)
apply(rule monofunI)
by simp

lemma "tsWeakCausal (tsId)"
by (simp add: tsId_def tsWeakCausalI)

lemma "\<not>tsStrongCausal (tsId)"
apply(auto simp add: tsId_def tsStrongCausal_def)
by (metis Rep_cfun_strict1 tsTake.simps(1) ts_existsNBot tstake_bot tstake_fin2)

(* eine stark Causale, stetige function appends a \<surd> to a timed stream *)
lift_definition delayFun :: "'m tstream \<rightarrow> 'm tstream" is
"\<lambda>ts . (Abs_tstream (\<up>\<surd>)) \<bullet> ts"
  by (simp add: Cfun.cfun.Rep_cfun)

lemma delayFun_dropFirst[simp]: "tsDropFirst\<cdot>(delayFun\<cdot>ts) = ts"
  apply(simp add: tsdropfirst_insert "delayFun.rep_eq")
  by(subst tsconc_rep_eq, auto)

lemma delayFun_takeFirst [simp]: "tsTakeFirst\<cdot>(delayFun\<cdot>ts) = Abs_tstream (\<up>\<surd>)"
  by (simp add: delayFun.abs_eq tsconc_rep_eq tstakefirst_insert)

lemma delayFun_takeN: "(delayFun\<cdot>ts1) \<down> (Suc n) = delayFun\<cdot>(ts1 \<down> n)"
  apply(subst tsTake.simps,auto)
    apply (metis below_bottom_iff delayFun_dropFirst strictI tsTake_prefix)
  by(simp add: delayFun_def)

lemma delayFun_sCausal: "(ts1 \<down> n) = (ts2 \<down> n) \<Longrightarrow> (delayFun\<cdot>ts1) \<down> (Suc n) = (delayFun\<cdot>ts2) \<down> (Suc n)"
by (simp add: delayFun_takeN)

lemma "tsStrongCausal (Rep_cfun delayFun)"
apply(rule tsStrongCausalI)
using delayFun_sCausal by blast


lemma delayFun_dom [simp]: "tsDom\<cdot>(delayFun\<cdot>ts) = tsDom\<cdot>ts"
by(simp add: delayFun_def tsdom_insert tsconc_rep_eq)

lemma delay_infTick [simp]: "#\<surd>ts = \<infinity> \<Longrightarrow> #\<surd> (delayFun\<cdot>ts) = \<infinity>"
by(simp add: delayFun_def)

lemma [simp]: "delayFun\<cdot>tsInfTick = tsInfTick"
apply(simp add: delayFun_def tsInfTick_def)
by (metis (no_types) Abs_tstream_inverse mem_Collect_eq sinftimes_unfold tick_msg tsInfTick.abs_eq tsInfTick.rep_eq tsconc_insert)

lemma delayfun_nbot[simp]: "delayFun\<cdot>ts \<noteq> \<bottom>"
  by(simp add: delayFun_def)  
        
lemma delayfun_abststream: "ts_well s\<Longrightarrow>delayFun\<cdot>(Abs_tstream s) = Abs_tstream (updis \<surd> && s)"
  by (simp add: delayFun.rep_eq lscons_conv tsconc_insert)    



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

lemma tsntimes_eps[simp]: "tsntimes n \<bottom> = \<bottom>"
by (induct n, simp+)

(* infinitely cycling the empty tstream produces the empty tstream again *)
lemma tsinftimes_eps[simp]: "tsinftimes \<bottom> = \<bottom>"
by (subst tsinftimes_def [THEN fix_eq2], simp)

(* repeating a tstream infinitely often is equivalent to repeating it once and then infinitely often *)
lemma tsinftimes_unfold: "tsinftimes s = s \<bullet> tsinftimes s"
by (subst tsinftimes_def [THEN fix_eq2], simp)

(* tsTake*)

text {* We prove that taking the first 1,2,...,n,... timeslots of an timed stream with tsTake forms a chain. 
Thus, we have to show that for all i: tsTake i \<sqsubseteq> tsTake (Suc i) *}
lemma chain_tsTake[simp]: "chain tsTake"
by (simp add: cfun_belowI po_class.chainI)


lemma esttake_tsTake[simp]: "tsTake k\<cdot>(tsTake n\<cdot>s) = tsTake (min k n)\<cdot>s"
by (simp add: min.commute)

lemma esttake_infD: "#\<surd>(tsTake k\<cdot>x) = \<infinity> \<Longrightarrow> tsTake k\<cdot>x = x"
by (simp add: ts_below_eq)

text {* Retrieving the first 0 elements of a stream returns the empty stream. *}
lemma [simp]: "tsTake 0\<cdot> x =  \<bottom>"
by (simp)

(* tspfair*)

text {* *If for all streams, all inputs with infinitely many ticks are mapped apply a function to outputs with
 infinitely many ticks, then the function is fair. *}
lemma tspfairI: "(\<And>s. tsTickCount \<cdot>s = \<infinity> \<Longrightarrow> tsTickCount \<cdot>(f\<cdot>s) = \<infinity>) \<Longrightarrow> tspfair f"
apply (simp add: tspfair_def)
done

text {* If a function is fair and an input stream has many ticks, then the output stream of f also has 
infinitely many ticks. *}
lemma tspfairD: "\<lbrakk>tspfair f;#\<surd>s = \<infinity>\<rbrakk> \<Longrightarrow> #\<surd>(f\<cdot>s) = \<infinity>"
apply (simp add: tspfair_def)
done

(* tsMap *)
thm tsMap_def

lemma tsmap_h_fair: "#({\<surd>} \<ominus> (smap (\<lambda>x. case x of \<M> m \<Rightarrow> \<M> f m | \<surd> \<Rightarrow> \<surd>)\<cdot>s)) = #({\<surd>} \<ominus> s)"
  apply (rule ind [of _ s], auto)
  by (case_tac "a", auto)

lemma tsmap_h_fair2:
  "#({e. e \<noteq> \<surd>} \<ominus> (smap (\<lambda>x. case x of \<M> m \<Rightarrow> \<M> f m | \<surd> \<Rightarrow> \<surd>)\<cdot>s)) = #({e. e \<noteq> \<surd>} \<ominus> s)"
  apply (rule ind [of _ s], auto)
  by (case_tac "a", auto)

lemma tsmap_h_sfoot: assumes "#s<\<infinity>" 
  shows "sfoot (smap (\<lambda>x. case x of \<M> m \<Rightarrow> \<M> f m | \<surd> \<Rightarrow> \<surd>)\<cdot>(s \<bullet> \<up>\<surd>)) = \<surd>"
  by (simp add: smap_split assms)

lemma tsmap_h_well: assumes "ts_well s"
  shows "ts_well (smap (\<lambda>x. case x of \<M> m \<Rightarrow> \<M> f m | \<surd> \<Rightarrow> \<surd>)\<cdot>s)"
  apply (simp add: ts_well_def tsmap_h_fair tsmap_h_sfoot)
  apply (cases "s = \<epsilon>", auto)
  apply (meson assms ts_well_def)
  by (metis (no_types, lifting)
      assms event.simps(5) sconc_snd_empty smap_scons smap_split strict_smap ts_fin_well)

lemma tsmap_unfold:
  "tsMap f\<cdot>ts = Abs_tstream (smap (\<lambda>x. case x of \<M> m \<Rightarrow> \<M> f m | \<surd> \<Rightarrow> \<surd>)\<cdot>(Rep_tstream ts))"
  apply (simp add:tsMap_def)
  apply (simp add: espf2tspf_def)
  by (simp add: tsmap_h_well)
    

lemma tsmap_strict[simp]: "tsMap f\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsmap_unfold)

 
lemma tsmap_tstickcount[simp]:  "#\<surd>(tsMap f\<cdot>ts) = #\<surd>ts"
  apply(simp add: tsTickCount_def)
  apply(simp only: tsmap_unfold)
  apply(subst Abs_tstream_inverse)
  apply(simp add:tsmap_h_well)
  apply(simp add: tsmap_h_fair)
  done

lemma tsmap_weak:"tsWeakCausal (Rep_cfun (tsMap f))"
apply (subst tsWeak2cont2, auto)  
done

(* tsProjFst and tsProjSnd *)
thm tsProjFst_def
thm tsProjSnd_def

lemma tsprojfst_strict[simp]: "tsProjFst\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsProjFst_def)

lemma tsprojsnd_strict[simp]: "tsProjSnd\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsProjSnd_def)

lemma tsprojfst_strict_rev: "tsProjFst\<cdot>ts = \<bottom> \<Longrightarrow> ts = \<bottom>"
  apply (simp add: tsProjFst_def)
  by (metis strict_tstickcount ts_0ticks tsmap_tstickcount)

lemma tsprojsnd_strict_rev: "tsProjSnd\<cdot>ts = \<bottom> \<Longrightarrow> ts = \<bottom>"
  apply (simp add: tsProjSnd_def)
  by (metis strict_tstickcount ts_0ticks tsmap_tstickcount)

lemma tsprojfst_tstickcount[simp]: "#\<surd>(tsProjFst\<cdot>ts) = #\<surd>ts"
  by (simp add: tsProjFst_def)

lemma tsprojsnd_tstickcount[simp]: "#\<surd>(tsProjSnd\<cdot>ts) = #\<surd>ts"
  by (simp add: tsProjSnd_def)

lemma tsabs_tsprojfst[simp]: "#(tsAbs\<cdot>(tsProjFst\<cdot>ts)) = #(tsAbs\<cdot>ts)"
  apply (simp add: tsProjFst_def tsAbs_def tsmap_unfold)
  apply (induct_tac ts, auto)
  apply (simp add: tsmap_h_well)
  apply (rule ind [of _ y], auto)
  by (simp add: tsmap_h_fair2)

lemma tsabs_tsprojsnd [simp]: "#(tsAbs\<cdot>(tsProjSnd\<cdot>ts)) = #(tsAbs\<cdot>ts)"
  apply (simp add: tsProjSnd_def tsAbs_def tsmap_unfold)
  apply (induct_tac ts, auto)
  apply (simp add: tsmap_h_well)
  apply (rule ind [of _ y], auto)
  by (simp add: tsmap_h_fair2)

lemma tsprojfst_delayfun: "tsProjFst\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsProjFst\<cdot>ts)"    
  apply (simp add: delayFun_def delayfun_abststream tsProjFst_def tsmap_unfold tsconc_rep_eq)
  apply (induct_tac ts, auto)
  by (simp add: tsConc_def tsmap_h_well)

lemma tsprojsnd_delayfun: "tsProjSnd\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsProjSnd\<cdot>ts)"    
  apply (simp add: delayFun_def delayfun_abststream tsProjSnd_def tsmap_unfold tsconc_rep_eq)
  apply (induct_tac ts, auto)
  by (simp add: tsConc_def tsmap_h_well)
    
(* tsFilter *)
thm tsFilter_def

lemma tsfilter_h_well: assumes "ts_well s"
  shows "ts_well (insert \<surd> (Msg ` M) \<ominus> s)"
apply (simp add: ts_well_def, auto)
apply (metis assms inf_ub less_le sfilterl4 strict_sfilter ts_well_def)
by (metis (no_types, lifting) add_sfilter2 assms fold_inf insertI1 lnsuc_lnle_emb not_less
    sconc_snd_empty sfilter_in slen_lnsuc strict_sfilter ts_well_def)

lemma tsfilter_unfold:
  "tsFilter M\<cdot>ts = Abs_tstream (insert \<surd> (Msg ` M) \<ominus> Rep_tstream ts)"
by (simp add: tsFilter_def tsfilter_h_well)

lemma tsfilter_strict[simp]: "tsFilter M\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsfilter_unfold)
  
lemma tsfilter_tstickcount [simp]: "#\<surd>(tsFilter M\<cdot>ts) = #\<surd>ts"
  apply(simp add: tsTickCount_def)
  apply(simp only: tsfilter_unfold)
  apply(subst Abs_tstream_inverse)
   apply (simp add: tsfilter_h_well)
   by simp
                                                
lemma tsfilter_weak:"tsWeakCausal (Rep_cfun (tsFilter M))"
  by (subst tsWeak2cont2, auto)  

(* tsscanl *)

(* Takes a nat indicating the number of elements to scan, a reducing function, an initial element,
   and an input event stream. Returns a event stream consisting of the partial reductions of the
   input event stream. Ticks will be mapped to ticks. *)
primrec TSSCANL :: "nat \<Rightarrow> ('o \<Rightarrow> 'i  \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'i event  stream \<Rightarrow> 'o event stream" where
"TSSCANL 0 f q s = \<epsilon>" |
"TSSCANL (Suc n) f q s = (if s=\<epsilon> then \<epsilon> 
                           else (if (shd s = \<surd>) then (\<up>\<surd> \<bullet> TSSCANL n f q (srt\<cdot>s)) 
                                 else \<up>(\<M> (f q \<M>\<inverse> shd s)) 
                                      \<bullet> (TSSCANL n f (f q (\<M>\<inverse> shd s)) (srt\<cdot>s))))"

(* Apply a function elementwise to the input event stream. Behaves like map, but also takes the
   previously generated output element as additional input to the function. For the first computation,
   an initial value is provided. *)
definition tsscanl_h :: "('o \<Rightarrow> 'i \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'i event  stream \<rightarrow> 'o event stream" where
"tsscanl_h f q \<equiv> \<Lambda> s. \<Squnion>i. TSSCANL i f q s"

(* Apply tsscanl_h on tstreams *)
definition tsscanl     :: "('o  \<Rightarrow> 'i   \<Rightarrow> 'o) \<Rightarrow> 'o  \<Rightarrow> 'i tstream \<rightarrow> 'o tstream" where
"tsscanl f q \<equiv> (\<Lambda> ts. Abs_tstream (tsscanl_h f q\<cdot>(Rep_tstream ts)))"

lemma TSSCANL_empty[simp]: "TSSCANL n f q \<epsilon> = \<epsilon>"
by (induct_tac n, auto)

(* Monotonicity of TSSCANL *)
lemma mono_TSSCANL: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> TSSCANL n f q x \<sqsubseteq> TSSCANL n f q y"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
apply (simp, rule monofun_cfun_arg, simp)
apply (simp add: below_shd)+
by (simp add: below_shd monofun_cfun_arg)

(* Result of TSSCANL n only depends on first n elements of input stream *)
lemma contlub_TSSCANL:
  "\<forall>f q s. TSSCANL n f q s = TSSCANL n f q (stake n\<cdot>s)"
apply (induct_tac n, auto)
apply (rule_tac x=s in scases)
apply (auto)
apply (metis (no_types, lifting) inject_scons stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis inject_scons stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis Fin_0 Fin_Suc bot_is_0 nat.simps(3) slen_scons stake_Suc strictI strict_slen surj_scons)
apply (rule_tac x=s in scases)
by (auto)

(* TSSCANL is a chain. This means that, for all fixed inputs, TSSCANL i returns a prefix of 
   TSSCANL (Suc i) *)
lemma chain_TSSCANL: "chain TSSCANL"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply (rule monofun_cfun_arg)
apply (erule_tac x="x" in allE)
apply presburger
by (smt monofun_cfun_arg)+

(* tsscanl is a continuous function *)
lemma cont_lub_TSSCANL: "cont (\<lambda>s. \<Squnion>i. TSSCANL i f q s)"
apply (rule cont2cont_lub)
apply (rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "q"])
apply (rule fun_belowD [of _ _ "f"])
apply (rule chainE)
apply (rule chain_TSSCANL)
apply (rule pr_contI)
apply (rule monofunI)
apply (rule mono_TSSCANL [rule_format], assumption)
apply (rule allI)
apply (rule_tac x="i" in exI)
by (rule contlub_TSSCANL [rule_format])

lemma tsscanl_h_empty[simp]: "tsscanl_h f q\<cdot>\<epsilon> = \<epsilon>"
by (simp add: cont_lub_TSSCANL tsscanl_h_def)

(* Scanning \<up>a\<bullet>s using q as the initial element is equivalent to computing \<up>(f q a) and appending
   the result of scanning s with (f q a) as the initial element *)
lemma tsscanl_h_scons:
  "a\<noteq>\<surd> \<Longrightarrow> tsscanl_h f q\<cdot>(\<up>a\<bullet>s) = \<up>(\<M>(f q (\<M>\<inverse> a))) \<bullet> tsscanl_h f (f q (\<M>\<inverse> a))\<cdot>s" 
apply (simp add: tsscanl_h_def)
apply (subst beta_cfun, rule cont_lub_TSSCANL)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (rule chain_TSSCANL [THEN chainE])
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
by (rule chain_TSSCANL [THEN chainE], simp)

lemma tsscanl_h_scons_tick: "tsscanl_h f q\<cdot>(\<up>\<surd>\<bullet>s) = \<up>\<surd> \<bullet> (tsscanl_h f q\<cdot>s)"
apply (simp add: tsscanl_h_def)
apply (subst beta_cfun, rule cont_lub_TSSCANL)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (rule chain_TSSCANL [THEN chainE])
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
by (rule chain_TSSCANL [THEN chainE], simp)

(* Variants for tsscanl_h_scons *)
lemma tsscanl_h_unfold: "shd s\<noteq>\<surd> \<and> s\<noteq>\<epsilon> 
  \<Longrightarrow> tsscanl_h f q\<cdot>s = \<up>(\<M>(f q (\<M>\<inverse> shd s))) \<bullet> tsscanl_h f (f q (\<M>\<inverse> shd s))\<cdot>(srt\<cdot>s)"
by (metis surj_scons tsscanl_h_scons)

lemma tsscanl_h_unfold_tick: "shd s=\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> tsscanl_h f q\<cdot>s = \<up>\<surd> \<bullet> tsscanl_h f q\<cdot>(srt\<cdot>s)"
by (metis surj_scons tsscanl_h_scons_tick)

(* Scanning a singleton event stream is equivalent to computing \<up>(f q a) *)
lemma [simp]: "a\<noteq>\<surd> \<Longrightarrow> tsscanl_h f q\<cdot>(\<up>a) = \<up>(\<M>(f q (\<M>\<inverse> a)))"
by (insert tsscanl_h_scons [of a f q \<epsilon>], auto)

lemma [simp]: "tsscanl_h f q\<cdot>(\<up>\<surd>) = \<up>\<surd>"
by (insert tsscanl_h_scons_tick [of f q \<epsilon>], auto)

(* The first element of the result of tsscanl_h is (f q a) *)
lemma tsscanl_h_shd[simp]: "a\<noteq>\<surd> \<Longrightarrow> shd (tsscanl_h f q\<cdot>(\<up>a\<bullet>s)) = (\<M>(f q (\<M>\<inverse> a)))"
by (simp add: tsscanl_h_scons)

lemma tsscanl_h_shd_tick[simp]: "shd (tsscanl_h f q\<cdot>(\<up>\<surd>\<bullet>s)) = \<surd>"
by (simp add: tsscanl_h_scons_tick)

(* Variants for tsscanl_h_shd *)
lemma tsscanl_h_unfold_shd: "shd s\<noteq>\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> shd (tsscanl_h f q\<cdot>s) = \<M>(f q \<M>\<inverse> shd s)"
by (simp add: tsscanl_h_unfold)

lemma tsscanl_h_unfold_shd_tick: "shd s=\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> shd (tsscanl_h f q\<cdot>s) = \<surd>"
by (simp add: tsscanl_h_unfold_tick)

(* Dropping the first element of the result of tsscanl_h is equivalent to using 
   (f q a) as initial element and proceeding with the rest of the input *)
lemma tsscanl_h_srt: "a\<noteq>\<surd> \<Longrightarrow> srt\<cdot>(tsscanl_h f q\<cdot>(\<up>a\<bullet>s)) = tsscanl_h f (f q (\<M>\<inverse> a))\<cdot>s"
by (insert tsscanl_h_scons [of a f q s], auto)

lemma tsscanl_h_srt_tick: "srt\<cdot>(tsscanl_h f q\<cdot>(\<up>\<surd>\<bullet>s)) = tsscanl_h f q\<cdot>s"
by (insert tsscanl_h_scons_tick [of f q s], auto)

(* Variants for tsscanl_h_srt *)
lemma tsscanl_h_unfold_srt: "shd s\<noteq>\<surd> \<Longrightarrow> srt\<cdot>(tsscanl_h f q\<cdot>s) = tsscanl_h f (f q (\<M>\<inverse> shd s))\<cdot>(srt\<cdot>s)"
by (metis stream.sel_rews(2) surj_scons tsscanl_h_empty tsscanl_h_srt)

lemma tsscanl_h_unfold_srt_tick: "shd s=\<surd> \<Longrightarrow> srt\<cdot>(tsscanl_h f q\<cdot>s) = tsscanl_h f q\<cdot>(srt\<cdot>s)"
by (metis stream.sel_rews(2) surj_scons tsscanl_h_empty tsscanl_h_srt_tick)

(* The n+1st element produced by tsscanl_h is the nth element of the result of using (f q (shd s))
   as initial element and proceeding with the rest of the input *)
lemma tsscanl_h_snth:"Fin n<#s \<and> shd s\<noteq>\<surd> 
  \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = snth n (tsscanl_h f (f q \<M>\<inverse> (shd s))\<cdot>(srt\<cdot>s))"
by (simp add: snth_rt tsscanl_h_unfold_srt)

lemma tsscanl_h_snth_tick:"Fin n<#s \<and> shd s=\<surd> 
  \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = snth n (tsscanl_h f q\<cdot>(srt\<cdot>s))"
by (simp add: snth_rt tsscanl_h_unfold_srt_tick)

(* Applying tsscanl_h never shortens the event stream *)
lemma fair_tsscanl_h1: "#s \<le> #(tsscanl_h f q\<cdot>s)"
apply (rule spec [where x = q])
apply (rule ind [of _ s], auto)
apply (subst lnle_def, simp del: lnle_conv)
by (metis (no_types, lifting) lnle_def monofun_cfun_arg slen_scons tsscanl_h_scons 
    tsscanl_h_scons_tick)

(* The result of tsscanl_h has the same length as the input event stream *)
lemma fair_tsscanl_h[simp]: "#(tsscanl_h f q\<cdot>s) = #s"
apply (rule spec [where x = q])
apply (rule ind [of _ s], auto)
by (metis slen_scons tsscanl_h_scons tsscanl_h_scons_tick)

(* Lemma for tsscanl_h is ts_well *)

(* Without ticks has the result of tsscanl_h the same length as the input event stream *)
lemma fair_tsscanl_h_tick[simp]: "#({\<surd>} \<ominus> tsscanl_h f q\<cdot>s) = #({\<surd>} \<ominus> s)"
apply (rule spec [where x = q])
apply (rule ind [of _ s], auto)
by (smt assoc_sconc event.distinct(1) inject_scons sconc_fst_empty sconc_snd_empty sfilter_in
    sfilter_in sfilter_nin sfilter_nin shd1 singletonD singletonD singletonI singletonI slen_scons
    slen_scons strict_sfilter strict_sfilter strict_slen strict_slen surj_scons tsscanl_h_empty
    tsscanl_h_scons tsscanl_h_scons_tick)

(* tsscanl_h mapped tick to tick *)
lemma tsscanl_h_snth_tick2tick: "Fin n<#s \<and> snth n s=\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<surd>"
apply (induction n arbitrary: q s)
apply (simp add: snth_rt, subst tsscanl_h_unfold_shd_tick, auto)
by (metis (mono_tags, lifting) Fin_leq_Suc_leq less_le not_less slen_rt_ile_eq snth_rt 
    tsscanl_h_snth tsscanl_h_snth_tick)

(* For every finite event stream with tick as last element ends the result of tsscanl_h with tick *)
lemma tsscanl_h_sfoot: assumes "#s<\<infinity>" 
  shows "sfoot (tsscanl_h f q\<cdot>(s \<bullet> \<up>\<surd>)) = \<surd>"
proof -
  obtain h1: "#(s\<bullet>\<up>\<surd>)<\<infinity>"
    using assms by auto
  obtain h2: "s\<bullet>\<up>\<surd>\<noteq>\<epsilon>"
    by (metis bot_is_0 lnat.con_rews slen_lnsuc strict_slen)
  obtain n where h3: "#(s\<bullet>\<up>\<surd>) = Fin n"
    by (metis Fin_Suc assms lncases neq_iff slen_lnsuc)   
  hence h4: "(THE a. Fin (Suc a)=#(s\<bullet>\<up>\<surd>)) = n-1"
    by (smt Fin_02bot Fin_Suc Suc_diff_1 h2 bot_is_0 inject_Fin inject_lnsuc neq0_conv slen_empty_eq
        the_equality)
  thus "sfoot (tsscanl_h f q\<cdot>(s \<bullet> \<up>\<surd>)) = \<surd>"
    apply (simp add: sfoot_def)
    by (metis Fin_0 Fin_Suc Suc_diff_1 assms diff_le_self h1 h2 h3 less2nat less_le ln_less 
        neq0_conv sfoot12 sfoot_exists2 slen_empty_eq tsscanl_h_snth_tick2tick)
qed

(* tsscanl_h is ts_well *)
lemma ts_well_tsscanl_h: "ts_well s \<Longrightarrow> ts_well (tsscanl_h f q\<cdot>s)"
apply (simp add: ts_well_def, auto)
by (metis (no_types, lifting) fold_inf lnsuc_lnle_emb not_less sfoot2 slen_lnsuc tsscanl_h_sfoot)

(* tsscanl is weak causal *)
lemma tsscanl_tsweak:"tsWeakCausal (\<lambda>ts. tsscanl f q \<cdot>ts)"
apply (subst tsWeak2cont2, auto)
by (simp add: tsscanl_def ts_well_tsscanl_h tsTickCount_def)

lemma tsscanl_unfold: "tsscanl f q\<cdot>ts = Abs_tstream (tsscanl_h f q\<cdot>(Rep_tstream ts))"
by (simp add: tsscanl_def ts_well_tsscanl_h) 

lemma tsscanl_empty[simp]: "tsscanl f q\<cdot>\<bottom> = \<bottom>"
by (simp add: tsscanl_unfold)

(* lemma for tsscanl equals sscanl without tick *)

(* Filter out tick in the input or the output does not matter for tsscanl_h *)
lemma tsscanl_h_sfilter_msg: "{e. e \<noteq> \<surd>} \<ominus> tsscanl_h f q\<cdot>s = tsscanl_h f q\<cdot>({e. e \<noteq> \<surd>} \<ominus> s)"
proof (induction s arbitrary: q, auto)
  fix u :: "'b event discr\<^sub>\<bottom>" and q :: "'a" and s :: "'b event stream"
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "\<And>q. {e. e \<noteq> \<surd>} \<ominus> tsscanl_h f q\<cdot>s = tsscanl_h f q\<cdot>({e. e \<noteq> \<surd>} \<ominus> s)"
  obtain ua where "(updis ua) = u"
    by (metis (full_types) Exh_Up a1 discr.exhaust)
  hence h1: "u && s = \<up>ua \<bullet> s"
    by (metis sconc_fst_empty sconc_scons' sup'_def)
  thus "{e. e \<noteq> \<surd>} \<ominus> tsscanl_h f q\<cdot>(u && s) = tsscanl_h f q\<cdot>({e. e \<noteq> \<surd>} \<ominus> u && s)"
    by (smt h1 a1 a2 event.distinct(1) mem_Collect_eq sfilter_in sfilter_nin shd1 stream.con_rews(2) 
        stream.sel_rews(5) tsscanl_h_scons tsscanl_h_unfold_tick)
qed

(* Without ticks the n+1st element produced by t_hsscanl is the result of merging the n+1st item of 
   s with the nth element produced by tsscanl *)
lemma tsscanl_h_sfilter_msg_snth: 
  "Fin (Suc n) < #({e. e\<noteq>\<surd>} \<ominus> s) \<Longrightarrow> \<M>\<inverse> snth (Suc n) (tsscanl_h f q\<cdot>({e. e\<noteq>\<surd>} \<ominus> s)) 
      = f (\<M>\<inverse> snth n (tsscanl_h f q\<cdot>({e. e\<noteq>\<surd>} \<ominus> s))) (\<M>\<inverse> (snth (Suc n) ({e. e\<noteq>\<surd>} \<ominus> s)))"
apply (induction n arbitrary: f q s)
apply (smt Fin_02bot Fin_Suc Zero_lnless_infty event.simps(4) fair_tsscanl_h ln_less lnzero_def 
       mem_Collect_eq neq_iff sfilterl7 slen_empty_eq slen_scons snth_rt snth_shd trans_lnless
       tsscanl_h_unfold tsscanl_h_unfold_shd tsscanl_h_unfold_srt)
by (smt not_less sfilter_srtdwl3 slen_rt_ile_eq snth_rt tsscanl_h_unfold_srt tsscanl_h_unfold_srt_tick)

(* Without tick is the nth of tsscanl_h equal to the nth of sscanl  *)
lemma tsscanl_h2sscanl_snth: "Fin n<#({e. e\<noteq>\<surd>} \<ominus> s) \<Longrightarrow>
 \<M>\<inverse> snth n (tsscanl_h f q\<cdot>({e. e\<noteq>\<surd>} \<ominus> s)) = snth n (sscanl f q\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>} \<ominus> s)))"
apply (induction n arbitrary: f q s, auto)
apply (subst tsscanl_h_unfold_shd, auto)
using sfilter_ne_resup apply force
apply (smt lnat.con_rews lnzero_def shd1 slen_empty_eq smap_scons sscanl_scons surj_scons)
apply (simp add: sscanl_snth tsscanl_h_sfilter_msg_snth)
by (smt Fin_def Fin_leq_Suc_leq Suc_n_not_le_n less2nat_lemma less_le smap_snth_lemma sscanl_snth)

(* Without tick tsscanl_h equals sscanl *)
lemma tsscanl_h2sscanl_sfilter_msg: 
  "smap (\<lambda>e. \<M>\<inverse> e)\<cdot>(tsscanl_h f q\<cdot>({e. e\<noteq>\<surd>} \<ominus> s)) = sscanl f q\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>} \<ominus> s))"
apply (rule snths_eq, auto)
by (simp add: smap_snth_lemma tsscanl_h2sscanl_snth)

(* Without tick tsscanl equals sscanl *)
lemma tsscanl2sscanl_tsAbs: "tsAbs\<cdot>(tsscanl f q\<cdot>ts) = sscanl f q\<cdot>(tsAbs\<cdot>ts)"
by (simp add: tsabs_insert tsscanl_unfold ts_well_Rep ts_well_tsscanl_h tsscanl_h_sfilter_msg
    tsscanl_h2sscanl_sfilter_msg)

(* Verification of tsscanl with tsscanl_nth *)

(* Calculates like scanl the event stream elements until the nth element *)
primrec tsscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a event stream \<Rightarrow> 'a" where
"tsscanl_nth 0 f q s = (if shd s=\<surd> then q else f q (\<M>\<inverse> shd s))" |
"tsscanl_nth (Suc n) f q s = (if shd s=\<surd> then tsscanl_nth n f q (srt\<cdot>s)
                              else tsscanl_nth n f (f q (\<M>\<inverse> shd s)) (srt\<cdot>s))"

(* Nth element of tsscanl_h is equal to tsscanl_nth *)
lemma tsscanl_h2tsscanl_nth_snth: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
proof (induction n arbitrary: q s, auto)
  fix q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  assume a2: "shd s \<noteq> \<surd>"
  thus "shd (tsscanl_h f q\<cdot>s) = \<M> f q \<M>\<inverse> shd s"
    using a1 lnat.con_rews lnzero_def strict_slen tsscanl_h_unfold_shd by fastforce
next  
  fix n :: "nat" and  q :: "'a" and s :: "'a event stream"
  assume a4: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> 
                \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
  assume a5: "Fin (Suc n) < #s"
  assume a6: "snth (Suc n) s \<noteq> \<surd>"
  thus "shd s = \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q (srt\<cdot>s)"
    by (metis (no_types, lifting) a4 a5 convert_inductive_asm not_less slen_rt_ile_eq snth_rt
        tsscanl_h_snth_tick)
  thus "shd s \<noteq> \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f (f q \<M>\<inverse> shd s) (srt\<cdot>s)"
    by (smt a4 a5 a6 not_less sdrop_forw_rt slen_rt_ile_eq snth_def tsscanl_h_unfold_srt)
qed

(* Nth element of tsscanl_h is equal to tsscanl_nth otherwise tick *)
lemma tsscanl_h2tsscanl_nth: 
  "Fin n<#s
     \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = (case (snth n s) of Msg a \<Rightarrow> \<M> tsscanl_nth n f q s | \<surd> \<Rightarrow> \<surd>)"
apply (cases "snth n s=\<surd>", simp add: tsscanl_h_snth_tick2tick)
by (metis event.exhaust event.simps(4) tsscanl_h2tsscanl_nth_snth)

(* Nth element of tsscanl is equal to tsscanl_nth otherwise tick *)
lemma tsscanl2tsscanl_nth:
  "Fin n<#(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream (tsscanl f q\<cdot>ts)) =
   (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> tsscanl_nth n f q (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>)"
by (simp add: tsscanl_unfold ts_well_tsscanl_h tsscanl_h2tsscanl_nth)

  
  
  
  
  
  
  
  
  
  
section \<open>Lemmata required for fixrec\<close>
(* Gespendet von Sebastian Stüber *)
  



(************************************************)
  subsection \<open>uMsg\<close>    
(************************************************)
  
lemma upapply2umsg [simp]: "upApply Msg\<cdot>(up\<cdot>x) = up\<cdot>(uMsg\<cdot>x)"  
apply(simp add: upapply_insert uMsg_def)
  by (metis (mono_tags) Discr_undiscr discr.case the_equality undiscr_def)  

    
(************************************************)
  subsection \<open>tsLshd\<close>    
(************************************************)
    
lemma tslshd_eq: "ts\<sqsubseteq>xs \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>ts = tsLshd\<cdot>xs"
  apply(simp add: tsLshd_def)
  by (simp add: Rep_tstream_bottom_iff below_tstream_def lshd_eq)

    
    
(************************************************)
  subsection \<open>tsLscons\<close>    
(************************************************)
        
lemma lscons_well [simp]: assumes "ts_well ts" and "ts\<noteq>\<bottom>"
  shows "ts_well (t&&ts)"
apply(auto simp add: ts_well_def)
  apply (metis Rep_Abs assms(1) sConc_Rep_fin_fin stream.con_rews(2) stream.sel_rews(5) surj_scons)
  by (metis Rep_Abs Rep_tstream_bottom_iff assms(1) assms(2) sConc_fin_well stream.con_rews(2) stream.sel_rews(5) surj_scons ts_well_def)    

 lemma lsconc_well2 [simp]: assumes "ts\<noteq>\<bottom>"
  shows "ts_well (t&&(Rep_tstream ts))"
   using Rep_tstream_bottom_iff assms lscons_well ts_well_Rep by blast
     
lemma lscons_tick_well[simp]: "ts_well ts \<Longrightarrow> ts_well (updis \<surd> && ts)"
  by (metis lscons_well sup'_def tick_msg)

lemma tslscons_mono [simp]: "monofun (\<lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule monofunI)
    apply (auto simp add: espf2tspf_def below_tstream_def)
  using Rep_tstream_bottom_iff apply blast
  by (metis (mono_tags, hide_lams) Abs_tstream_inverse Rep_tstream Rep_tstream_bottom_iff lscons_well mem_Collect_eq monofun_cfun_arg)

lemma tslscons_chain2 [simp]: assumes "chain Y" 
  shows "chain (\<lambda>i. if ((Y i)=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))" (is "chain (\<lambda>i. ?f (Y i))")
proof -
  have "monofun ?f" by simp
  thus ?thesis by (meson assms monofun_def po_class.chain_def)
qed
 
lemma tslscons_mono2[simp]: "monofun (\<lambda> t ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule monofunI, rule fun_belowI)
    apply (auto simp add: espf2tspf_def below_tstream_def)
  using stream.inverts apply force
  using stream.inverts apply force
  by (metis Discr_undiscr Exh_Up not_up_less_UU updis_eq2)

lemma tslscons_chain: "chain Y \<Longrightarrow> chain (\<lambda>i. espf2tspf (lscons\<cdot>(updis \<surd>)) (Y i))"
  by (simp add: below_tstream_def po_class.chain_def espf2tspf_def)
    
lemma tslsconc_cont_h: assumes "chain Y" and "t=updis \<surd>"
  shows "Abs_tstream (updis \<surd> && Rep_tstream (Lub Y)) \<sqsubseteq> (\<Squnion>i. Abs_tstream (updis \<surd> && Rep_tstream (Y i)))"
proof -
  have "\<And>i. ts_well (updis \<surd> && Rep_tstream (Y i))" by simp
  hence "chain (\<lambda>i. Abs_tstream (updis \<surd> && Rep_tstream (Y i)))"
    by (metis (no_types, lifting) Rep_Abs assms(1) below_tstream_def monofun_cfun_arg po_class.chain_def)
  thus ?thesis
    by (smt Abs_tstream_inverse Rep_tstream assms(1) below_tstream_def cont2contlubE contlub_cfun_arg lscons_tick_well lub_eq mem_Collect_eq po_class.chain_def po_eq_conv rep_tstream_cont)
qed      

lemma tslscons_cont_h3:"t \<noteq> updis \<surd> \<Longrightarrow>
         chain Y \<Longrightarrow> (\<And>i. Y i \<noteq>\<bottom>) \<Longrightarrow>
         (if (\<Squnion>i. Y i) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (\<Squnion>i. Y i)) \<sqsubseteq>
         (\<Squnion>i. if Y i = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))"
proof -
  assume a1: "chain Y"
  assume a2: "\<And>i. Y i \<noteq> \<bottom>"
  have f3: "\<forall>s. s \<notin> Collect ts_well \<or> Rep_tstream (Abs_tstream s::'a tstream) = s"
    using Abs_tstream_inverse by blast
  have f4: "\<forall>f fa. \<not> cont f \<or> \<not> chain fa \<or> (f (Lub fa::'a tstream)::'a event stream) = (\<Squnion>n. f (fa n))"
    using cont2contlubE by blast
  obtain nn :: "(nat \<Rightarrow> 'a tstream) \<Rightarrow> nat" where
    f5: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
    using po_class.chain_def by moura
  then have f6: "\<forall>n. Y n \<sqsubseteq> Y (Suc n)"
    using a1 by blast
  then have f7: "(if Y (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))))) \<sqsubseteq> (if Y (Suc (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y (Suc (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))))))"
    using a2 by (simp add: below_tstream_def espf2tspf_def monofun_cfun_arg)
  obtain nna :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> (nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
    f8: "\<forall>f fa. f (nna fa f) \<noteq> fa (nna fa f) \<or> Lub f = Lub fa"
    by (meson lub_eq)
  have f9: "Rep_tstream (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)) = (\<Squnion>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    using f7 f5 f4 by (meson rep_tstream_cont)
  have f10: "Rep_tstream (Abs_tstream (t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n)))))) = t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))))"
    using f3 a2 lsconc_well2 by blast
  have "Abs_tstream (t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))))) = espf2tspf (lscons\<cdot>t) (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))))"
    by (simp add: espf2tspf_def)
  then have "t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n)))) = Rep_tstream (if Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n)))))"
    using f10 a2 by fastforce
  then have f11: "(\<Squnion>n. t && Rep_tstream (Y n)) = (\<Squnion>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    using f8 by meson
  obtain nnb :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
    f12: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nnb f) \<notsqsubseteq> f (Suc (nnb f)))"
    using po_class.chain_def by moura
  { assume "Abs_tstream (Rep_tstream (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)) = Abs_tstream (Rep_tstream (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    then have "(\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)) = (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)"
      by simp
    then have "(if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>) \<sqsubseteq> (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))"
      using po_eq_conv by blast }
  moreover
  { assume "Abs_tstream (Rep_tstream (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)) \<noteq> Abs_tstream (Rep_tstream (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    then have "Abs_tstream (Rep_tstream (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)) \<noteq> espf2tspf (lscons\<cdot>t) (Lub Y)"
      using f12 f11 f9 f6 f4 a1 by (metis (no_types) below_tstream_def contlub_cfun_arg espf2tspf_def rep_tstream_cont)
    then have "(if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>) \<sqsubseteq> (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))"
      by fastforce }
  ultimately have "(if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>) \<sqsubseteq> (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))"
    by fastforce
  then show ?thesis
    by presburger
qed

lemma tslscons_cont_h2: assumes "t \<noteq> updis \<surd>" and "chain Y"
    shows "(if (\<Squnion>i. Y i) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (\<Squnion>i. Y i)) \<sqsubseteq>
         (\<Squnion>i. if Y i = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))" (is "?f (\<Squnion>i. Y i) \<sqsubseteq> ?x")
  proof(cases "(\<Squnion>i. Y i) = \<bottom>")
    case True
    then show ?thesis by (simp add: assms)
  next
    case False
    have f_chain: "chain (\<lambda>i. ?f (Y i))"  by (simp add: assms(2))
    obtain n  where n_def: "(\<And>i. ((Y ( i+n)) \<noteq>\<bottom>))"  using False assms(2) chain_nbot False by blast
    have lub_eq: "(\<Squnion>i. Y(i+n)) = (\<Squnion>i. Y i)" by(simp add: lub_range_shift assms)
    hence "?f (\<Squnion>i. Y (i+n)) \<sqsubseteq> (\<Squnion>i. ?f (Y (i+n)))" using assms(1) assms(2) chain_shift n_def tslscons_cont_h3 by blast
    also have "?f (\<Squnion>i. Y (i+n)) = ?f (\<Squnion>i. Y i)" using assms(2) lub_range_shift2 by fastforce
    also have "(\<Squnion>i. ?f (Y (i+n))) = (\<Squnion>i. ?f (Y i))" using f_chain lub_range_shift2 by fastforce
    finally show ?thesis by simp
  qed 
    
lemma tslscons_cont: "cont (\<lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule contI2)
   apply simp
  apply(cases "t\<noteq>updis \<surd>")
  using tslscons_cont_h2 apply fastforce 
   by (simp add: tslsconc_cont_h tslscons_cont_h2 espf2tspf_def)

lemma tslscons_cont2[simp]: "cont (\<lambda> t . \<Lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
proof -
  obtain uu :: "('a event discr\<^sub>\<bottom> \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream) \<Rightarrow> 'a event discr\<^sub>\<bottom>" and tt :: "('a event discr\<^sub>\<bottom> \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream) \<Rightarrow> 'a tstream" where
    f1: "\<forall>f. \<not> cont (f (uu f)) \<or> \<not> cont (\<lambda>u. f u (tt f)) \<or> cont (\<lambda>u. Abs_cfun (f u))"
    by (metis (no_types) cont2cont_LAM)
  have "\<forall>t. monofun (\<lambda>u. if (t::'a tstream) = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t)"
    using mono2mono_fun tslscons_mono2 by fastforce
  then have "cont (\<lambda>t. if t = \<bottom> \<and> uu (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t) \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot> (uu (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t))) t) \<and> cont (\<lambda>u. if tt (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t) = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) (tt (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t)))"
    using chfindom_monofun2cont tslscons_cont by blast
  then show ?thesis
    using f1 by presburger
qed
  
  
lemma tslscons_insert: "tsLscons\<cdot>t\<cdot>ts = (if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"
  unfolding tsLscons_def
  by (simp only: beta_cfun tslscons_cont2 tslscons_cont)

lemma tslscons_bot [simp]: "tsLscons\<cdot>\<bottom>\<cdot>ts = \<bottom>"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)

lemma tslscons_bot2 [simp]: "tsLscons\<cdot>(updis \<surd>)\<cdot>\<bottom>= Abs_tstream (updis \<surd> && \<bottom>)"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)
    
lemma tslscons_bot3 [simp]: "t\<noteq>(updis \<surd>) \<Longrightarrow> tsLscons\<cdot>t\<cdot>\<bottom>= \<bottom>"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)    
    
lemma tslscons_nbot [simp]: "t\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>t\<cdot>ts \<noteq>\<bottom>"
  unfolding tslscons_insert
  by (simp add: espf2tspf_def)

lemma tslscons_nbot2 [simp]: "tsLscons\<cdot>(updis \<surd>)\<cdot>ts\<noteq>\<bottom>"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)

lemma tslscons_nbot3 [simp]: "tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts\<noteq>\<bottom>"
by (simp add: DiscrTick_def)

lemma tslscons2lscons: "ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>t\<cdot>ts = Abs_tstream (lscons\<cdot>t\<cdot>(Rep_tstream ts))"
by (simp add: tslscons_insert espf2tspf_def)

lemma tslscons_lscons: "ts\<noteq>\<bottom> \<Longrightarrow> Rep_tstream (tsLscons\<cdot>t\<cdot>ts) = t && (Rep_tstream ts)"
by(simp add: tslscons2lscons)  

lemma tslscons_lscons2: "ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>(updis \<surd>)\<cdot>ts = Abs_tstream (updis \<surd> && (Rep_tstream ts))"
by (simp add: tslscons2lscons)

lemma tslscons_lshd [simp]: "ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>(tsLscons\<cdot>t\<cdot>ts) = t"
by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)  

lemma tslscons_lshd2 [simp]: "tsLshd\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = (updis \<surd>)"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)  

lemma tslscons_srt [simp]: "t\<noteq>\<bottom> \<Longrightarrow> tsRt\<cdot>(tsLscons\<cdot>t\<cdot>ts) = ts"
by(auto simp add: tslscons_insert tsRt_def espf2tspf_def)  

lemma tslscons_srt2 [simp]: "tsRt\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = ts"
  by(auto simp add: tslscons_insert tsRt_def espf2tspf_def) 
  
  
(************************************************)
  subsection \<open>tsMLscons\<close>    
(************************************************)
    
lemma tsmlscons2tslscons: "tsMLscons\<cdot>(updis m)\<cdot>ts = tsLscons\<cdot>(updis (Msg m))\<cdot>ts"
  by(simp add: tsMLscons_def)  

lemma tsmlscons_bot[simp]: "tsMLscons\<cdot>\<bottom>\<cdot>ts = \<bottom>"    
  by(simp add: tsMLscons_def)    

lemma tsmlscons_bot2[simp]: "tsMLscons\<cdot>t\<cdot>\<bottom> = \<bottom>"    
  apply(simp add: tsMLscons_def)    
    by(auto simp add: tslscons_insert upapply_insert)
    
lemma tsmlscons_nbot[simp]: "t\<noteq>\<bottom>\<Longrightarrow>ts \<noteq>\<bottom> \<Longrightarrow> tsMLscons\<cdot>t\<cdot>ts \<noteq>\<bottom>"    
  by(simp add: tsMLscons_def)    

lemma tsmlscons_lscons: "tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts = tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts"
  by(simp add: uMsg_def tsMLscons_def)

lemma tsmlscons_lscons2: "tsMLscons\<cdot>(updis t)\<cdot>ts = tsLscons\<cdot>(updis (Msg t))\<cdot>ts"
      by(simp add: tsMLscons_def)

lemma tsmlscons_lscons3: "ts\<noteq>\<bottom> \<Longrightarrow> Rep_tstream (tsMLscons\<cdot>(updis t)\<cdot>ts) = (updis (Msg t)) && Rep_tstream ts"
  by(simp add: tsMLscons_def tslscons_lscons)
    
lemma tsmlscons_lscons4: 
  "ts\<noteq>\<bottom> \<Longrightarrow> tsMLscons\<cdot>(updis t)\<cdot>ts = Abs_tstream (updis (Msg t) && Rep_tstream ts)"
by (simp add: tsMLscons_def tslscons2lscons)

(* ----------------------------------------------------------------------- *)
subsection {* delayFun  *}
(* ----------------------------------------------------------------------- *)

lemma tick_eq_discrtick: "updis \<surd> = up\<cdot>DiscrTick"
by (simp add: DiscrTick_def)

lemma delayfun_insert: "delayFun\<cdot>ts = (Abs_tstream (\<up>\<surd>)\<bullet>ts)"  
by (simp add: delayFun_def)

lemma tsrt_delayfun [simp]: "tsRt\<cdot>(delayFun\<cdot>ts) = ts"
  by (simp add: delayFun_def tsRt_def espf2tspf_def tsconc_rep_eq)
    
lemma tslshd_delayfun [simp]: "tsLshd\<cdot>(delayFun\<cdot>ts) = updis \<surd>"  
    by (simp add: delayFun_def tsLshd_def espf2tspf_def tsconc_rep_eq)
  
lemma delayfun_tslscons: "delayFun\<cdot>ts = tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
by (simp add: delayFun_def tslscons_insert tsconc_insert DiscrTick_def espf2tspf_def lscons_conv)

lemma delayfun_tslscons_bot: "delayFun\<cdot>\<bottom> = tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>\<bottom>"
by (simp add: delayfun_tslscons tick_eq_discrtick)  

(* ----------------------------------------------------------------------- *)
subsection {* Abs_tstream converter  *}
(* ----------------------------------------------------------------------- *)

lemma absts2tslscons: "ts_well (t&&ts) \<Longrightarrow> Abs_tstream (t&&ts) = tsLscons\<cdot>t\<cdot>(Abs_tstream ts)"
apply (simp add: tslscons_insert, auto)
apply (metis Abs_tstream_bottom_iff mem_Collect_eq stream.con_rews(2) stream.sel_rews(5)
       ts_well_drop1 msg_nwell2)
apply (metis Rep_Abs espf2tspf_def stream.con_rews(2) stream.sel_rews(5) ts_well_drop1)
by (metis Rep_Abs espf2tspf_def stream.sel_rews(5) ts_well_drop1 up_defined)
  
lemma absts2tsmlscons_msg: "ts_well (updis (Msg m) && ts) \<Longrightarrow> 
  Abs_tstream ((updis (Msg m))&&ts) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream ts)"
by(simp add: tsMLscons_def absts2tslscons)

lemma absts2tsmlscons_msg2: "ts_well (\<up>(Msg m) \<bullet>  ts) \<Longrightarrow> 
  Abs_tstream (\<up>(Msg m) \<bullet>  ts) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream ts)"
by (metis absts2tsmlscons_msg lscons_conv)

lemma absts2delayfun: "ts_well ts \<Longrightarrow> Abs_tstream (updis \<surd>&&ts) = delayFun\<cdot>(Abs_tstream ts)"
by (metis delayfun_abststream)
      
(************************************************)
(************************************************)      
    section \<open>Match definitions\<close>
(************************************************)
(************************************************)
  
definition
  match_tstream :: "'a tstream \<rightarrow> ('a event discr u \<rightarrow> 'a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
  "match_tstream = (\<Lambda> xs k.  strictify\<cdot>(\<Lambda> xs. k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs))\<cdot>xs)"
  
 (* match if element is tick *) 
definition match_tick:: "'a event discr \<rightarrow> ('b ::cpo) match \<rightarrow> 'b match" where
 "match_tick = (\<Lambda> t k . if t=(Discr \<surd>) then k else Fixrec.fail)" 

 (* match if element is message *)
definition match_umsg:: "'a event discr \<rightarrow> ('a discr \<rightarrow> 'b::cpo match) \<rightarrow> 'b match"  where
"match_umsg = (\<Lambda> t k. case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
  
  

(************************************************)      
    subsection \<open>Match Lemmata\<close>
(************************************************)
      
lemma match_umsg_mono: "monofun (\<lambda>k. case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
  apply(rule monofunI)
  apply(cases "\<exists>m. t = Discr (Msg m)", auto)
  apply (simp add: monofun_cfun_fun)
  by (metis Discr_undiscr discr.case event.exhaust event.simps(5) po_eq_conv)

lemma match_umsg_cont[simp]: "cont (\<lambda>k. case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
  apply(rule contI2)
  apply(simp add: match_umsg_mono)
  apply(cases "\<exists>m. t = Discr (Msg m)", auto)
  using contlub_cfun_fun po_eq_conv apply blast
  using Discr_undiscr discr.case event.exhaust event.simps(5) po_eq_conv by (smt below_lub po_class.chain_def)

lemma match_umsg_insert: "match_umsg\<cdot>t\<cdot>k = (case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
by(simp add: match_umsg_def)  
  
   
  
lemma match_tstream_simps [simp]:
  "match_tstream\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "ts\<noteq>\<bottom> \<Longrightarrow> t\<noteq>\<bottom> \<Longrightarrow> match_tstream\<cdot>(tsLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts" 
  "match_tstream\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>k = k\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
  "match_tstream\<cdot>(delayFun\<cdot>ts)\<cdot>k = k\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
  "xs\<noteq>\<bottom>\<Longrightarrow> match_tstream\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs)\<cdot>k = k\<cdot>(up\<cdot>(uMsg\<cdot>x))\<cdot>xs"
     by(simp_all add: match_tstream_def DiscrTick_def tsMLscons_def uMsg_def)
    
lemma match_tick_simps [simp]:
  "a\<noteq>\<surd> \<Longrightarrow> match_tick\<cdot>(Discr a)\<cdot>k = Fixrec.fail"
  "b\<noteq>(Discr \<surd>) \<Longrightarrow> match_tick\<cdot>b\<cdot>k = Fixrec.fail"
  "t\<noteq>DiscrTick \<Longrightarrow> match_tick\<cdot>t\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(uMsg\<cdot>m)\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(Discr \<surd>)\<cdot>k = k"
  "match_tick\<cdot>DiscrTick\<cdot>k = k"
  apply (auto simp add: match_tick_def DiscrTick_def uMsg_def)
  by (metis Discr_undiscr discr.case event.distinct(1) undiscr_Discr)

lemma match_umsg_simps [simp]:
  "match_umsg\<cdot>(Discr \<surd>)\<cdot>k = Fixrec.fail"
  "match_umsg\<cdot>DiscrTick\<cdot>k = Fixrec.fail"
  "match_umsg\<cdot>(Discr (Msg m))\<cdot>k = k\<cdot>(Discr m)"
  "match_umsg\<cdot>(uMsg\<cdot>m2)\<cdot>k = k\<cdot>m2"
  unfolding match_umsg_insert
  apply (auto simp add: DiscrTick_def)
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 Discr_undiscr cont_discrete_cpo discr.case event.case(1) uMsg_def)
   
setup \<open>
  Fixrec.add_matchers
    [ (@{const_name tsLscons},  @{const_name match_tstream}) , 
      (@{const_name DiscrTick}, @{const_name match_tick}),
      (@{const_name uMsg},      @{const_name match_umsg})
    ]
\<close>
  
(* ----------------------------------------------------------------------- *)
subsection {* tsZip *}
(* ----------------------------------------------------------------------- *)     
  
fixrec tsZip :: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
  (* Bottom case *)
"tsZip\<cdot>ts\<cdot>\<bottom> = \<bottom>" | 

  (* One Message, then directly a Tick. Return Pair an Tick directly. 
    (Neccessary, because if the 'stream' ends we would not return a Tick) *)
"x\<noteq>\<bottom> \<Longrightarrow>                
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts))\<cdot>(x && xs)
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs))" | 

  (* two messages in tStream. Work on the first *)
"x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>              
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t2))\<cdot>ts))\<cdot>(x && xs) 
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>(tsMLscons\<cdot>(up\<cdot>t2)\<cdot>ts)\<cdot>xs)" | 

  (* ignore ticks *)
"xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"

lemma tszip_strict [simp]: 
"tsZip\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>ts\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>\<bottom>\<cdot>s = \<bottom>"
by (fixrec_simp)+

lemma tszip_tslscons_fixrec: "x\<noteq>\<bottom>  \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>               
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t2))\<cdot>ts))\<cdot>(x && xs) 
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>(tsMLscons\<cdot>(up\<cdot>t2)\<cdot>ts)\<cdot>xs)"
by (fixrec_simp)

lemma tszip_tslscons_fixrec_tick: "x\<noteq>\<bottom> \<Longrightarrow>           
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts))\<cdot>(lscons\<cdot>x\<cdot>xs)
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs))"
by (fixrec_simp)

lemma tszip_tslscons_tick_fixrec: "xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma tszip_mlscons:
  "tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>(tsMLscons\<cdot>(updis u)\<cdot>ts))\<cdot>((updis x) && xs)
                           = tsMLscons\<cdot>(updis (t,x))\<cdot>(tsZip\<cdot>(tsMLscons\<cdot>(updis u)\<cdot>ts)\<cdot>xs)"
by (metis (no_types, lifting) tsmlscons_bot2 tsmlscons_lscons tszip_strict(3) tszip_tslscons_fixrec
    up_defined upapply2_rep_eq)

lemma tszip_mlscons_delayfun:
  "tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>(delayFun\<cdot>ts))\<cdot>((updis x) && xs)
                           = tsMLscons\<cdot>(updis (t,x))\<cdot>(delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs))"
by (metis (no_types, lifting) delayfun_tslscons tsmlscons_lscons tszip_tslscons_fixrec_tick 
    up_defined upapply2_rep_eq)

lemma tszip_delayfun: "xs\<noteq>\<epsilon> \<Longrightarrow> tsZip\<cdot>(delayFun\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (simp add: delayfun_tslscons)

(************************************************)      
    section \<open>Induction Lemmata\<close>
(************************************************)
      
lemma tstream_infs: "(\<And>s. #\<surd>s<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
  by (metis (no_types, lifting) adm_def finite_chain_def inf_less_eq leI ts_infinite_fin tstake_chain tstake_inf_lub tstake_infinite_chain)
        
lemma tstream_adm_fin: "adm P \<Longrightarrow> (\<forall>ts. #\<surd>ts<\<infinity> \<longrightarrow> P ts) \<Longrightarrow>  adm (\<lambda>a. ts_well a \<longrightarrow> P (Abs_tstream a))"    
  apply(rule admI)
    apply auto
  by (metis (no_types, lifting) adm_def finite_chain_def inf_less_eq leI ts_infinite_fin tstake_chain tstake_inf_lub tstake_infinite_chain)  

lemma tsmsg_notwell: "\<not>ts_well((updis (Msg m)) && \<bottom>)"
  apply(simp add: ts_well_def)
  by (metis Inf'_neq_0 event.distinct(1) fold_inf lnat.sel_rews(2) lscons_conv sfilterl4 sfoot1 sfoot_one slen_scons strict_slen sup'_def)

lemma tstream_fin_induct_h:
  assumes 
        "P \<bottom>" 
    and "\<And>xs. P xs \<Longrightarrow> P (delayFun\<cdot>xs)" and "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>x\<cdot>xs)"
    and "#s<\<infinity>"
  shows "ts_well s \<Longrightarrow> P (Abs_tstream s)"
proof (induction rule: stream_fin_induct)
  case 1
  then show ?case
    by (simp add: assms(1)) 
next
  case (2 u s)
   assume u_def: "u \<noteq> \<bottom>" and "(ts_well s \<Longrightarrow> P (Abs_tstream s))" and  "ts_well (u && s)"
      have s_well: "ts_well s"  using "2.prems"(1) ts_well_drop1 u_def by fastforce
      then show "P (Abs_tstream (u && s))"
                proof (cases "u=updis \<surd>")
                  case True
                    have "delayFun\<cdot>(Abs_tstream s) = Abs_tstream (u&&s)"
                      by (simp add: True delayfun_abststream s_well)
                  then show ?thesis
                    using \<open>ts_well s \<Longrightarrow> P (Abs_tstream s)\<close> assms(2) s_well by force
                next
                  case False
                    obtain m where m_def: "u = up\<cdot>(Discr (Msg m))"
                      by (metis (full_types) Exh_Up False discr.exhaust event.exhaust u_def)                        
                    have "s\<noteq>\<bottom>"
                      using "2.prems" m_def tsmsg_notwell by blast
                     hence "Abs_tstream (u&&s) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream s)"
                       by (metis Abs_Rep Rep_Abs Rep_tstream_bottom_iff m_def s_well tslscons_lscons tsmlscons2tslscons)
                  then show ?thesis
                    by (metis \<open>ts_well s \<Longrightarrow> P (Abs_tstream s)\<close> assms(3) s_well tsmlscons_bot2 up_defined)
                qed   
next
  case 3
  then show ?case by (simp add: assms(4))
qed

lemma tstream_fin_induct:
  assumes 
        Bot: "P \<bottom>" 
    and delayFun: "\<And>xs. P xs \<Longrightarrow> P (delayFun\<cdot>xs)" 
    and tsMLscons: "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>x\<cdot>xs)"
    and fin: "#\<surd>ts<\<infinity>"
  shows "P ts"
proof -
  obtain s where s_def: "Abs_tstream s = ts" and s_well: "ts_well s" using Abs_Rep ts_well_Rep by blast
  hence "#s < \<infinity>" using assms(4) finititeTicks by force
  hence "P (Abs_tstream s)"
    by (simp add: assms(1) assms(2) assms(3) s_well tstream_fin_induct_h)
  thus ?thesis by (simp add: s_def)    
qed     
  

(* this term creates an induction rule for tstream *)  
lemma tstream_induct [case_names Adm Bot delayFun tsMLscons, induct type: tstream]:
  fixes ts
  assumes 
        "adm P"
    and "P \<bottom>"  
    and "\<And>ts. P ts \<Longrightarrow> P (delayFun\<cdot>ts)" and "\<And>ts t. P ts\<Longrightarrow> t\<noteq>\<bottom>\<Longrightarrow>ts\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>t\<cdot>ts)"
  shows "P ts"
  by (metis assms(1) assms(2) assms(3) assms(4) tstream_fin_induct tstream_infs)

    
  
(*TODO

(*-----------------------------*)
     old TStream.thy (now TStream_old.thy)
     some lemmas may be not necessary because of pcpodef
(*-----------------------------*)



(*To drop n+1 timeslots is the same as dropping one timeslot and then n *)
lemma tsdrop_back_tsrt:"tsDrop (Suc n)\<cdot> x = tsDropFirst \<cdot> (tsDrop n\<cdot> x)"
apply (simp add: tsDrop_def tsDropFirst_def)
sorry


(*The domain of every timeslot is in the domain of all timeslots*)
lemma tsNth_tsDom1: "tsDom\<cdot> (tsNth n\<cdot> ts)\<subseteq> tsDom\<cdot> ts"
apply(simp add: tsNth_def)
apply auto
sorry


text {* If the domain of a stream is a subset of a set M, then the domain of the remainder
of the stream after removing the head element, is also a subset of the set M. *}
lemma tsDom_tsDropI: "tsDom\<cdot> x \<subseteq> M \<Longrightarrow> tsDom\<cdot> (tsDropFirst\<cdot> x) \<subseteq> M"
apply (simp add: tsDom_def)
apply (simp add: tsDropFirst_def)
sorry


text {* If the domain of a stream is a subset of a set M, then the domain of the remainder
of the stream after removing n elements, is also a subset of the set M. *}
lemma tsdom_tsdropI: "tsDom\<cdot> s \<subseteq> M \<Longrightarrow> tsDom\<cdot> (tsDrop n\<cdot> s) \<subseteq> M"
sorry


lemma[simp]: "tsDom\<cdot> (Abs_tstream(\<up>\<surd>)) = {}"
apply(simp add: tsDom_def)
sorry

lemma tsDom_tsConc[simp]: "tsDom\<cdot> (tsConc ts\<cdot> ts)= tsDom\<cdot> ts"
apply(simp add: tsConc_def tsDom_def sdom_def)
sorry

lemma tsDom_tsntimes_eq: "tsDom\<cdot>(tsntimes n ts) = tsDom\<cdot>ts"
apply(simp add:tsntimes_def)
apply simp
using tsDom_tsConc
sorry

lemma tsDom_tsinftimes_empty: "tsDom\<cdot>( tsinftimes ts) = tsDom\<cdot> ts"
apply(simp add: tsinftimes_def)
using tsDom_tsntimes_eq
sorry


text {* The domain of the infinite stream consisting only of ticks is empty. *}
lemma tsDom_infTick_empty: "ts= tsinftimes(Abs_tstream(\<up>\<surd>)) \<Longrightarrow> tsDom\<cdot> ts = {}"
apply (simp add: tsDom_def tsinftimes_def)
sorry

text {* The remainder of the concatenation of a list with a timed stream is the same as
the concatenation of the remainder of the list with the timed stream. **}
lemma [simp]: "tsrt ((e#es) \<bullet>+ rs) = (es \<bullet>+ rs)"
apply (simp add: tsrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst tstream_scons_eq Abs_tstream_inverse)
apply (subst tstream_scons_eq)
apply (subst list_conc_tstream)
apply simp
apply simp
done


text {* Taking n+1 elements from the concatenation of a 1-element list with a timed stream
is like appending the element of the list to the n-prefix of the timed stream.*}
lemma [simp]: "tstake (Suc n) ([e] \<bullet>+ rs) =  Abs_tstream (\<up>e \<bullet> Rep_tstream (tstake n rs))"
apply (simp add: tstake_def)
apply (simp add: tsconc_def )
apply (simp add: espf2tspf_def)
apply (simp add: Rep_Abs)
done

text {*If all k-prefixes of two timed streams are equal for all k, then the two streams are equal.*}
lemma tstake_lemma: "(\<And>k. tstake k x = tstake k y) \<Longrightarrow> x = y" 
apply (rule Rep_tstream_inject [THEN iffD1])
apply (rule stream.take_lemma)
apply (simp add: tstake_def)
apply (smt tstake_def Abs_tstream_inverse Rep_Abs Rep_tstream sconc_fst_inf split_streaml1)
done


text {* After dropping n elements, a timed stream remains a timed stream. *}
lemma Rep_Abs_sdrop[simp]: 
  "sdrop n\<cdot>(Rep_tstream x) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (metis (mono_tags, lifting) fair_sdrop_rev mem_Collect_eq slen_sfilter_sdrop tstreaml1)
done

text {* Dropping n+1 elements from a stream is the same as dropping n elements out of the
rest(without the head element) of the stream. *}
lemma tsdrop_forw_tsrt: "tsdrop (Suc n) x = tsdrop n (tsrt x)"
apply (simp add: tsdrop_def)
apply (simp add: tsrt_def)
apply (simp add: espf2tspf_def)
apply (smt Abs_tstream_inverse Rep_Abs Rep_Abs_sdrop fair_sdrop inf_less_eq sdrop_forw_rt 
slen_sfilter_sdrop_ile tstreaml1)
done

text {* Dropping n+1 elements from a stream is the same as dropping n elements out of the stream, 
and then removing the head element from it. *}
lemma tsdrop_back_tsrt:"tsdrop (Suc n) x = tsrt (tsdrop n x)"
apply (simp add: tsdrop_def)
apply (simp add: tsrt_def)
apply (simp add: espf2tspf_def)
apply (metis (no_types, lifting) Abs_tstream_inverse Rep_Abs_sdrop sdrop_back_rt)
done

text {* If the domain of a stream is a subset of a set M, then the domain of the remainder
of the stream after removing the head element, is also a subset of the set M. *}
lemma tsdom_tsrtI: "tsdom x \<subseteq> M \<Longrightarrow> tsdom (tsrt x) \<subseteq> M"
apply (simp add: tsdom_def)
apply (simp add: tsrt_def)
apply (simp add: espf2tspf_def)
apply (simp add: tsnth_def)
apply (subst Abs_tstream_inverse)
apply simp
using srt_tstream 
apply blast
apply (rule_tac B="{m. \<exists>k. snth k (Rep_tstream x) = Msg m}" in subset_trans)
apply (rule subsetI)
apply simp
apply (erule exE)
apply (rule_tac x="Suc k" in exI)
apply (simp add: snth_rt)
apply simp
done

text {* If the domain of a stream is a subset of a set M, then the domain of the remainder
of the stream after removing n elements, is also a subset of the set M. *}
lemma tsdom_tsdropI: "tsdom s \<subseteq> M \<Longrightarrow> tsdom (tsdrop n s) \<subseteq> M"
apply (simp add: atomize_imp)
apply (rule_tac x="s" in spec)
apply (induct_tac n)
apply simp
apply (rule allI)
apply (rule impI)
apply (erule_tac x="tsrt x" in allE)
apply (drule mp)
apply (rule tsdom_tsrtI)
apply assumption
apply (simp add: tsdrop_forw_tsrt)
done

text {* Every infinite timed stream has at least a tick in it. *}
lemma tsnth_tickl: "#(Rep_tstream x) = \<infinity> \<Longrightarrow> \<exists>n. tsnth n x = \<surd>"
apply (simp add: tsnth_def)
apply (rule ccontr)
apply simp
apply (insert ex_snth_in_sfilter_nempty [of "Rep_tstream x" "{\<surd>}"])
apply simp
apply (insert Rep_tstream [of x])
apply simp
done

text {* The remainder of the concatenation of an 1-element list with a timed stream is the
timed stream itself. *}
lemma [simp]: "tstrt ([Msg m] \<bullet>+ rs) = tstrt rs"
apply (simp add: tstrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* Concatenating an 1-element list consisting of a tick, with a timed stream, 
and then removing the first block of it, yields the timed stream again. *}
lemma [simp]: "tstrt ([\<surd>] \<bullet>+ rs) = rs"
apply (simp add: tstrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* Taking the (n+1)-th element of the concatenation of an 1-element list with a timed stream
is the same as taking the n-th element of the timed stream. *}
lemma [simp]: "tsnth (Suc n) ([e] \<bullet>+ rs) = tsnth n rs"
apply (simp add: tsnth_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {*  Taking the 0-th element of the stream is apply definition of tsnth the same as 
taking the head of the stream. *}
lemma [simp]: "tsnth 0 x = tshd x"
apply (simp add: tsnth_def)
apply (simp add: tshd_def)
done

text {* Dropping n+1 elements from the concatenation of an 1-element list with a timed stream
is the same as dropping n elements from the timed stream. *}
lemma [simp]: "tsdrop (Suc n) ([e] \<bullet>+ rs) = tsdrop n rs"
apply (simp add: tsdrop_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* The domain of the infinite stream consisting only of ticks is empty. *}
lemma tsdom_tsjusttime[simp]: "tsdom justtime = {}"
apply (simp add: justtime_def)
apply (simp add: tsdom_def)
apply (simp add: tsnth_def)
apply (subst Abs_tstream_inverse)
apply simp
apply (simp add: snth_def)
done

text {* Taking at least one block from the concatenation of an 1-message list with a stream is the
 same as taking these blocks from the timed stream and then appending the list message on it. *}
lemma tsttake_Suc_Msg [simp]: "tsttake (Suc n) ([Msg m] \<bullet>+ rs) = \<up>(Msg m) \<bullet> tsttake (Suc n) rs"
apply (simp add: tsttake_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst fix_eq2, simp+)
done

text {* Taking at least one block from the concatenation of a list consisting of one tick
with a stream is the same as taking one less block from the timed stream and then appending the tick
on it. *}
lemma tsttake_Suc_Tick [simp]: "tsttake (Suc n) ([\<surd>] \<bullet>+ rs) = \<up>\<surd> \<bullet> tsttake n rs"
apply (simp add: tsttake_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst fix_eq2, simp+)
done

text {* If for every stream, which has either infinite many ticks, or is finite, a property P holds,
then the property P holds for any timed stream. *}
lemma PRep_tstreamI: "\<lbrakk>\<And>x. (#(sfilter {\<surd>}\<cdot>x) = \<infinity> \<or> #x \<noteq> \<infinity>)  \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (Rep_tstream y)"
using tstreaml1 
apply blast
done



text {* Take the first n+1 blocks of an event stream, where the stream has no messages in the first block,
 is the same as taking the first tick and n blocks. *}
lemma esttake_Tick[simp]: "esttake (Suc n)\<cdot>(\<up>\<surd> \<bullet> x) = \<up>\<surd> \<bullet> esttake n\<cdot>x"
apply simp
apply (subst fix_eq2, auto)
done

text {* Take the first n+1 blocks of an event stream, where the stream has one message in the first block,
 is the same as taking the first message and continue checking that same first block. *}
lemma esttake_Msg[simp]: "esttake (Suc n)\<cdot>(\<up>(Msg m) \<bullet> x) = \<up>(Msg m) \<bullet> esttake (Suc n)\<cdot>x"
apply simp
apply (subst fix_eq2, auto)
done

text {* Take the first x blocks of an empty stream returns the empty stream. *}
lemma esttake_ep[simp]: "esttake x\<cdot>\<epsilon> = \<epsilon>"
apply (induct_tac x)
apply simp
apply simp
apply (subst fix_eq2, auto)
done

text {* To prove the following lemmas, it is easier to remove e esttake_Suc from simplifier: *}
declare esttake_Suc [simp del]


text {* We prove that taking the first 1,2,...,n,... blocks of an event stream with esttake forms a chain. 
Thus, we have to show that for all i: esttake i \<sqsubseteq> esttake (Suc i) *}
lemma chain_esttake[simp]: "chain esttake"
apply (rule chainI)
apply (rule cfun_belowI)
apply (rule_tac x=i in spec)
apply (rule_tac x=x in ind)
apply auto
apply (case_tac "x")
apply auto
apply (case_tac "a")
apply auto
apply (rule monofun_cfun_arg)
apply auto
apply (rule monofun_cfun_arg)
apply auto
done

text {* Same for esttake. *}
lemma reach_estream: "(\<Squnion>k. esttake k\<cdot>x) = x"
apply (rule stream.take_lemma)
apply (rule_tac x=x in spec)
apply (induct_tac n)
apply auto
apply (rule_tac x=x in scases)
apply auto
apply (case_tac "a")
apply auto
apply (subst lub_range_shift [where j = "Suc 0", THEN sym])
apply simp
apply auto
apply (subst contlub_cfun_arg [THEN sym])
apply simp
apply (rule ch2ch_Rep_cfunL)
apply (rule chainI)
apply (rule chain_esttake [THEN chainE])
apply simp
apply (rule cfun_arg_cong)
apply (erule_tac x="s" in allE)
apply (erule subst)
apply (rule cfun_arg_cong)
apply (rule sym)
apply (subst lub_range_shift [where j = "Suc 0", THEN sym])
apply simp
apply simp
apply (subst lub_range_shift [where j = "Suc 0", THEN sym])
apply auto
apply (subst contlub_cfun_arg [THEN sym])
apply auto
done

text {* esttake of esttake.*}
lemma esttake_esttake[simp]: "esttake k\<cdot>(esttake n\<cdot>s) = esttake (min k n)\<cdot>s"
apply (rule_tac x="k" in spec)
apply (rule_tac x="n" in spec)
apply (rule ind [of _ s])
apply simp
apply simp
apply (case_tac "a")
apply simp
apply (rule allI)
apply (rule allI)
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "xa")
apply simp
apply simp
apply (rule allI)
apply (rule allI)
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "xa")
apply simp
apply simp
done

text {*If all k-prefixes of two timed streams are equal for all k, then the two streams are equal.*}
lemma esttake_lemma: "(\<And>k. esttake k\<cdot>x = esttake k\<cdot>y) \<Longrightarrow> x = y"
apply (subst reach_estream [THEN sym])
apply (rule sym)
apply (subst reach_estream [THEN sym])
apply (rule lub_eq)
apply auto
done

text {* The take functions give apply definition prefixes of the stream: *}
lemma ub_of_esttake[simp]: "esttake k\<cdot>x \<sqsubseteq> x"
apply (rule_tac y="\<Squnion> k. esttake k\<cdot>x" in below_trans)
apply (rule is_ub_thelub)
apply simp
apply (subst reach_estream)
apply simp
done

text {* If length of prefix is infinite, then the prefix equals the stream itself. *}
lemma esttake_infD: "#(esttake k\<cdot>x) = \<infinity> \<Longrightarrow> esttake k\<cdot>x = x"
apply (subgoal_tac "esttake k\<cdot>x \<sqsubseteq> x")
apply (rule eq_less_and_fst_inf)
apply simp
apply simp
apply simp
done

text {* If the number of elements from a set X in a stream s is infinite, then it remains infinite
even after we drop from the stream all elements not in X. *}
lemma srtdw_tstream[simp]: "srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream x) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (insert sfilter_srtdwl2 [of "{\<surd>}" "Rep_tstream x"])
apply simp
apply (metis inf_less_eq slen_srtdw tstreaml1)
done

text {* Using the above lemma, we can add the following rewriting rule for srtdw:*}
lemma [simp]: 
"Rep_tstream (Abs_tstream (srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream x))) =  srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream x)"
using Abs_tstream_inverse 
using srtdw_tstream 
apply blast
done

text {* Now we can show that, apply using srtdw multiple times for dropping blocks out of a stream, 
the result still remains timed stream. *}
lemma [simp]: 
  "iterate n\<cdot>(srtdw (\<lambda>x. x \<noteq> \<surd>))\<cdot>(Rep_tstream s) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (rule_tac x="s" in spec)
apply (induct_tac n)
apply (simp del: iterate_Suc)
apply (rule allI)
using tstreaml1 
apply blast
apply (smt Abs_tstream_inverse iterate_Suc2 srtdw_tstream)
done

text {*For a timed stream which has at least a tick: if the function sdropwhile is used to drop
all the messages until a tick comes, then it fulfills: *}
lemma sfilterl5:
  "sfilter {\<surd>}\<cdot>x \<noteq> \<epsilon> \<Longrightarrow> \<up>\<surd> \<bullet> srt\<cdot>(sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x) = sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x"
apply (simp add: atomize_imp)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (case_tac "a")
apply simp
apply simp
done

text {*Taking events from a stream until a tick is found, and then taking from the result n events,
is same as first taking n events, and then from the result taking events until a tick is found. *}
lemma esttake_stakewhilel1:
  "esttake n\<cdot>(stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x) = stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>(esttake n\<cdot>x)"
apply (rule_tac x="n" in spec)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (rule allI)
apply (case_tac "a")
apply simp
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "x")
apply simp
apply simp
done

text {*Dropping events from a stream until a tick is found, and then taking from the result n
events, is same as first taking n events, and then from result taking events until tick found. *}
lemma esttake_sdropwhilel1:
  "esttake n\<cdot>(sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x) = sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>(esttake n\<cdot>x)"
apply (rule_tac x="n" in spec)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (rule allI)
apply (case_tac "a")
apply simp
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "x")
apply simp
apply simp
done

text {*If we use stakewhile to retreave all messages until a tick is found, we automatically get a
prefix stream consisting of only one block. This means, applying on the left side esttake (Suc n) 
for any n=0,1,.., won't make any difference and the result will just be the first block. *}
lemma esttake_stakewhilel2:
  "stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x = esttake (Suc n)\<cdot>(stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x)"
apply (rule_tac x="n" in spec)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (rule allI)
apply (case_tac "a")
apply simp
apply simp
done

text {*For any stream, its prefix concatenated with its suffix returns the stream itself. *}
lemma stakewhile_sdropwhile[simp]:"stakewhile p\<cdot>x \<bullet> sdropwhile p\<cdot>x = x"
apply (rule stream.take_lemma)
apply (rule_tac x="x" in spec)
apply (induct_tac n)
apply simp
apply simp
done

text {*Taking n+1 blocks is the same as initially taking the first block, and then taking the 
remaining blocks. *}
lemma esttake_tstreaml1: "sfilter {\<surd>}\<cdot>x \<noteq> \<epsilon> \<Longrightarrow> 
   esttake (Suc n)\<cdot>x = stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x \<bullet> \<up>\<surd> \<bullet> esttake n\<cdot>(srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>x)"
apply (simp add: srtdw_def)
apply (subst esttake_Tick [THEN sym])
apply (subst sfilterl5)
apply (rule notI)
apply simp
apply (subst esttake_stakewhilel2 [where n="n"])
apply (subst esttake_stakewhilel1)
apply (subst esttake_sdropwhilel1)
apply simp
done

(*-----------------------------------------------------------------------*)





    Lemmas to lift from streams to tstreams:
    some may be equivalent to another lemma in TStream_old.thy (above)





(*-----------------------------------------------------------------------*)

(*-----------------------------*)
smap
(*-----------------------------*)

(* smap distributes over concatenation *)
lemma smap_scons[simp]: "smap f\<cdot>(\<up>a \<bullet> s) = \<up>(f a) \<bullet> smap f\<cdot>s"

(* mapping f over a singleton stream is equivalent to applying f to the only element in the stream *) 
lemma [simp]: "smap f\<cdot>(\<up>a) = \<up>(f a)"

text {* @{term smap} maps each element @{term x} to @{term "f(x)"} *}
lemma smap_snth_lemma:
  "Fin n < #s \<Longrightarrow> snth n (smap f\<cdot>s) = f (snth n s)"

text {* @{term sdrop} after @{term smap} is like @{term smap} after @{term sdrop} *}
lemma sdrop_smap[simp]: "sdrop k\<cdot>(smap f\<cdot>s) = smap f\<cdot>(sdrop k\<cdot>s)"

text {* @{term "smap f"} is a homomorphism on streams with respect to concatenation *}
lemma smap_split: "smap f\<cdot>(a \<bullet> b) = (smap f\<cdot>a) \<bullet> (smap f\<cdot>b)"

lemma smap2sinf[simp]: "smap f\<cdot>(x\<infinity>)= (smap f\<cdot>x)\<infinity>"

lemma rek2smap: assumes "\<And>a as. f\<cdot>(\<up>a \<bullet> as) = \<up>(g a) \<bullet> f\<cdot>as"
  and "f\<cdot>\<bottom> = \<bottom>"
  shows "f\<cdot>s = smap g\<cdot>s"

(* smap for streams is equivalent to map for lists *)
lemma smap2map: "smap g\<cdot>(<ls>) = <(map g ls)>"

(* the notion of length is the same for streams as for lists *)
lemma list2streamFin: "#(<ls>) = Fin (length ls)"

(*-----------------------------*)
siterate
(*-----------------------------*)

  lemma niterate_Suc2: "niterate (Suc n) F x = niterate n F (F x)"

  (* Kopieren in Prelude. *)
  lemma niter2iter: "iterate g\<cdot>h\<cdot>x = niterate g (Rep_cfun h) x"
  
  (* Prelude *)
  lemma iterate_eps [simp]: assumes "g \<epsilon> = \<epsilon>"
    shows "(iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<bullet> h (g s)))\<cdot>\<bottom>) \<epsilon> = \<epsilon>" 
  
  (* prelude *)
  lemma fix_eps [simp]: assumes "g \<epsilon> = \<epsilon>"
    shows "(\<mu> h. (\<lambda>s. s \<bullet> h (g s))) \<epsilon> = \<epsilon>"
  
(* beginning the iteration of the function h with the element (h x) is equivalent to beginning the
   iteration with x and dropping the head of the iteration *)
lemma siterate_sdrop: "siterate h (h x) = sdrop 1\<cdot>(siterate h x)"

(* iterating the function h infinitely often after having already iterated i times is equivalent to
   beginning the iteration with x and then dropping i elements from the resulting stream *)
lemma siterate_drop2iter: "siterate h (niterate i h x) = sdrop i\<cdot>(siterate h x)" 

(* the head of iterating the function g on x doesn't have any applications of g *)
lemma shd_siter[simp]: "shd (siterate g x) = x"

(* dropping i elements from the infinite iteration of the function g on x and then extracting the head
   is equivalent to computing the i'th iteration via niterate *)
lemma shd_siters: "shd (sdrop i\<cdot>(siterate g x)) = niterate i g x"          

(* the i'th element of the infinite stream of iterating the function g on x can alternatively be found
   with (niterate i g x) *)
lemma snth_siter: "snth i (siterate g x) = niterate i g x"

(* dropping j elements from the stream x and then extracting the i'th element is equivalent to extracting
   the i+j'th element directly *)
lemma snth_sdrop: "snth i (sdrop j\<cdot>x) = snth (i+j) x"

(* extracting the i+1'st element from the stream of iterating the function g on x is equivalent to extracting
   the i'th element and then applying g one more time *)
lemma snth_snth_siter: "snth (Suc i) (siterate g x) = g (snth i (siterate g x))"

(* dropping the first element from the chain of iterates is equivalent to shifting the chain by applying g *)
lemma sdrop_siter:  "sdrop 1\<cdot>(siterate g x) = smap g\<cdot>(siterate g x)"

(* if the functions g and h commute then g also commutes with any number of iterations of h *)
lemma iterate_insert: assumes "\<forall>z. h (g z) = g (h z)"
  shows "niterate i h (g x) = g (niterate i h x)"

(* lifts iterate_insert from particular iterations to streams of iterations *)
lemma siterate_smap:  assumes "\<forall>z. g (h z) = h (g z)"
  shows "smap g\<cdot>(siterate h x) = siterate h (g x)"

(* shows the equivalence of an alternative recursive definition of iteration *)
lemma rek2niter: assumes "xs = \<up>x \<bullet> (smap g\<cdot>xs)"
  shows "snth i xs = niterate i g x"

(* wichtig *)
(* recursively mapping the function g over the rest of xs is equivalent to the stream of iterations of g on x *)
lemma rek2siter: assumes "xs = \<up>x \<bullet> (smap g\<cdot>xs)"
  shows "xs = siterate g x" 

(* shows that siterate produces the least fixed point of the alternative recursive definition *)
lemma fixrek2siter: "fix\<cdot>(\<Lambda> s . (\<up>x \<bullet> smap g\<cdot>s)) =  siterate g x"

(* dropping elements from a stream of iterations is equivalent to adding iterations to every element *)
lemma sdrop2smap: "sdrop i\<cdot>(siterate g x) = smap (niterate i g)\<cdot>(siterate g x)"

(* doing smap in two passes, applying h in the first pass and g in the second is equivalent to applying
   g \<circ> h in a single pass *)
lemma smaps2smap: "smap g\<cdot>(smap h\<cdot>xs) =  smap (\<lambda> x. g (h x))\<cdot>xs"

(* iterating the function g on x is equivalent to the stream produced by concatenating \<up>x and the 
   iteration of g on x shifted by another application of g *)
lemma siterate_unfold: "siterate g x = \<up>x \<bullet> smap g\<cdot>(siterate g x)"

(* iterating the identity function produces an infinite constant stream of the element x *)
lemma siter2sinf: "siterate id x = sinftimes (\<up>x)"

(* if g acts as the identity for the element x then iterating g on x produces an infinite constant
   stream of x *)
lemma siter2sinf2: assumes "g x = x"
  shows "siterate g x = sinftimes (\<up>x)"

(*-----------------------------*)
siterateBlock
(*-----------------------------*)

(* block-iterating the function f on the stream x is equivalent to the stream produced by concatenating x
   and the iteration of f on x shifted by another application of f *)
lemma siterateBlock_unfold: "siterateBlock f x = x \<bullet> siterateBlock f (f x)"

(* if g doesn't change the length of the input, then iterating g doesn't either *)
lemma niterate_len[simp]: assumes "\<forall>z. #z = #(g z)" 
  shows "#((niterate i g) x) = #x"

(* dropping i blocks from siterateBlock g x is equivalent to beginning siterateBlock after i iterations
   of g have already been applied *)
lemma siterateBlock_sdrop2: assumes "#x = Fin y" and "\<forall>z. #z = #(g z)" 
  shows "sdrop (y*i)\<cdot>(siterateBlock g x) = siterateBlock g ((niterate i g) x)"

(* the y*i'th element of siterateBlock is the same as the head of the i'th iteration *)
lemma siterateBlock_snth: assumes "#x = Fin y" and "\<forall>z. #z = #(g z)" and "#x > Fin 0" 
  shows "snth (y*i) (siterateBlock g x) = shd ((niterate i g) x)"

(* dropping a single block from siterateBlock is equivalent to beginning the iteration with (g x) *)
lemma siterateBlock_sdrop: assumes "#x = Fin y"
  shows "sdrop y\<cdot>(siterateBlock g x) = siterateBlock g (g x)"

(* block-iterating the function g on the empty stream produces the empty stream again *)
lemma siterateBlock_eps[simp]: assumes "g \<epsilon> = \<epsilon>"
  shows "siterateBlock g \<epsilon> = \<epsilon>" 

(* block-iterating the identity on the element x is equivalent to infinitely repeating x *)
lemma siterateBlock2sinf: "siterateBlock id x = sinftimes x"

(* siterateBlock doesn't affect infinite streams *)
lemma siterBlock_inf [simp]: assumes "#s = \<infinity>"
  shows "siterateBlock f s = s"

(* the first element of siterateBlock doesn't have any applications of g *)
lemma siterateBlock_shd [simp]: "shd (siterateBlock g (\<up>x)) = x"

(* helper lemma for siterateBlock2siter *)
lemma siterateBlock2niter: "snth i (siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = niterate i g x" (is "snth i (?B) = ?N i")

(* siterateBlock creates an infinitely long stream *)
lemma siterateBlock_len [simp]: "#(siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = \<infinity>"

(* iterating the identity function commutes with any function f *)
lemma siterateBlock_smap: "siterateBlock id (smap f\<cdot>x) =  smap f\<cdot>(siterateBlock id x)"

(* converting x to a singleton stream and applying siterateBlock using smap g is equivalent to
   iterating using g directly on x *)
lemma siterateBlock2siter [simp]: "siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x) = siterate g x" 

(*-----------------------------*)
szip
(*-----------------------------*)
(* zipping the infinite constant streams \<up>x\<infinity> and \<up>y\<infinity> is equivalent to infinitely repeating the tuple
   \<up>(x, y) *)
lemma szip2sinftimes[simp]: "szip\<cdot>\<up>x\<infinity>\<cdot>\<up>y\<infinity> = \<up>(x, y)\<infinity> "

lemma szip_len [simp]: "#(szip\<cdot>as\<cdot>bs) = min (#as) (#bs)"

lemma stake_mono[simp]: assumes "i\<le>j"
  shows "stake i\<cdot>s \<sqsubseteq> stake j\<cdot>s"

lemma sconc_sdom: "sdom\<cdot>(s1\<bullet>s2) \<subseteq> sdom\<cdot>s1 \<union> sdom\<cdot>s2"

lemma sntimes_sdom1[simp]: "sdom\<cdot>(sntimes n s) \<subseteq> sdom\<cdot>s"

(*-----------------------------*)
adm
(*-----------------------------*)

(* for functions g and h producing sets the following predicate is admissible *)
lemma adm_subsetEq [simp]: "adm (\<lambda>s. g\<cdot>s \<subseteq> h\<cdot>s)"

(* for a function g producing sets and a set cs the following predicate is admissible *)
lemma adm_subsetEq_rc [simp]: "adm (\<lambda>s. g\<cdot>s \<subseteq> cs)"

(* for a function h producing sets and a set cs the following predicate is admissible *)
lemma adm_subsetEq_lc [simp]: "adm (\<lambda>s. cs \<subseteq> h\<cdot>s)"

(* for a set cs and a function g producing sets, the following predicate is admissible *)
lemma adm_subsetNEq_rc [simp]: "adm (\<lambda>s. \<not> g\<cdot>s \<subseteq> cs)"

(* for a function g over streams, the admissiblity of the following predicate over streams holds *)
lemma sdom_adm2[simp]: "adm (\<lambda>a. sdom\<cdot>(g\<cdot>a) \<subseteq> sdom\<cdot>a)"

lemma adm_finstream [simp]: "adm (\<lambda>s. #s<\<infinity> \<longrightarrow> P s)"

lemma adm_fin_below: "adm (\<lambda>x . \<not> Fin n \<sqsubseteq> # x)"

lemma adm_fin_below2: "adm (\<lambda>x . \<not> Fin n \<le> # x)"

(*-----------------------------*)
sdom
(*-----------------------------*)
(* appending another stream xs can't shrink the domain of a stream x *)
lemma sdom_sconc[simp]: "sdom\<cdot>x \<subseteq> sdom\<cdot>(x \<bullet> xs)"

(* repeating a stream doesn't add elements to the domain *)
lemma sinftimes_sdom[simp]: "sdom\<cdot>(sinftimes s) \<subseteq> sdom\<cdot>s"

(* repeating a stream doesn't remove elements from the domain either *)
lemma sinf_sdom [simp]: "sdom\<cdot>(s\<infinity>) = sdom\<cdot>s"

(* sfilter doesn't add elements to the domain *)
lemma sbfilter_sbdom[simp]: "sdom\<cdot>(sfilter A\<cdot>s) \<subseteq> sdom\<cdot>s"

(* smap can only produce elements in the range of the mapped function f *)
lemma smap_sdom_range [simp]: "sdom\<cdot>(smap f\<cdot>s) \<subseteq> range f"

(* every element produced by (smap f) is in the image of the function f *)
lemma smap_sdom: "sdom\<cdot>(smap f\<cdot>s) =  f ` sdom\<cdot>s"

(* Lemmas für SB *)
(* if the stream a is a prefix of the stream b then a's domain is a subset of b's *)
lemma f1 [simp]: "a \<sqsubseteq> b \<Longrightarrow> sdom\<cdot>a \<subseteq> sdom\<cdot>b"

(* the lub of a chain of streams contains any elements contained in any stream in the chain *)
lemma l4: "chain S \<Longrightarrow> sdom\<cdot>(S i) \<subseteq> sdom\<cdot>(\<Squnion> j. S j)"

lemma l402: "chain S \<Longrightarrow> S i \<noteq> \<up>8 \<Longrightarrow> \<forall>i. S i \<sqsubseteq> s \<Longrightarrow> (\<Squnion> j. S j) \<sqsubseteq> s"

lemma l403: "chain S \<Longrightarrow> \<forall>i. S i \<sqsubseteq> s \<Longrightarrow> \<forall>i. sdom\<cdot>(S i) \<subseteq> sdom\<cdot>s"

lemma l404: "chain S \<Longrightarrow>  \<forall>i. S i \<sqsubseteq> s \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S j) \<subseteq> sdom\<cdot>s"

(* streams appearing later in the chain S contain the elements of preceding streams *)
lemma l405: "chain S \<Longrightarrow> i \<le> j \<Longrightarrow> sdom\<cdot>(S i) \<subseteq> sdom\<cdot>(S j)"

lemma l43: "chain S \<Longrightarrow> finite_chain S \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S j) \<subseteq> (\<Union>i. sdom\<cdot>(S i))"

(*wichtig*)
(* the lub doesn't have any elements that don't appear somewhere in the chain *)
lemma sdom_lub: "chain S \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S j) = (\<Union>i. sdom\<cdot>(S i))"

text {*Sei i in N ein index der Kette S von Strömen und B eine Menge von Nachrichten. *}
lemma l44: assumes "chain S" and "\<forall>i. sdom\<cdot>(S i) \<subseteq> B"
  shows "sdom\<cdot>(\<Squnion> j. S j) \<subseteq> B"

lemma l6: "chain S \<Longrightarrow> \<forall>i. sdom\<cdot>(S i) \<subseteq> B \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S (j + (SOME k. A))) \<subseteq> B"

(* dropping elements can't increase the domain *)
lemma sdrop_sdom[simp]: "sdom\<cdot>(sdrop n\<cdot>s)\<subseteq>sdom\<cdot>s"

(*-----------------------------*)
sfoot
(*-----------------------------*)

(* returns the last element of a stream *)
(* the stream must not be empty or infinitely long *)
definition sfoot :: "'a stream \<Rightarrow> 'a" where
"sfoot s = snth (THE a. lnsuc\<cdot>(Fin a) = #s) s"

(* appending the singleton stream \<up>a to a finite stream s causes sfoot to extract a again *)
lemma sfoot1[simp]: assumes "xs = s\<bullet>(\<up>a)" and "#xs < \<infinity>"
   shows "sfoot xs = a"

(* sfoot extracts the element a from any finite stream ending with \<up>a *)
lemma sfoot12 [simp]: assumes "#s<\<infinity>"
  shows "sfoot (s\<bullet>\<up>a) = a"

(* sfoot extracts a from the singleton stream \<up>a *)
lemma sfoot_one [simp]: "sfoot (\<up>a) = a"



(* if the foot of a non-empty stream xs is a, then xs consists of another stream s (possibly empty)
   concatenated with \<up>a *)
lemma sfoot2 [simp]: assumes "sfoot xs = a" and "xs\<noteq>\<epsilon>"
  shows "\<exists>s. xs = s \<bullet> \<up>a"

(* when sfoot is applied to the concatenation of two finite streams s and xs, and xs is not empty,
   then sfoot will produce the foot of xs *)
lemma sfoot_conc [simp]: assumes "#s<\<infinity>" and "#xs<\<infinity>" and "xs\<noteq>\<epsilon>"
  shows "sfoot (s\<bullet>xs) = sfoot xs"

(* if the finite stream s contains more than one element then the foot of s will be the foot of the
   rest of s *)
lemma sfoot_sdrop: assumes "Fin 1<#s" and "#s<\<infinity>"
  shows "sfoot (srt\<cdot>s) = sfoot s"

lemma [simp]: assumes "#xs < \<infinity>"
  shows "sfoot (\<up>a \<bullet> \<up>b \<bullet> xs) = sfoot (\<up>b \<bullet> xs)"

(* the foot of any stream s is the nth element of s for some natural number n *)
lemma sfoot_exists [simp]:"\<exists>n. snth n s = sfoot s"

(* if the stream s contains n+1 elements then the foot of s will be found at index n *)
lemma  sfoot_exists2: 
  shows "Fin (Suc n) = #s \<Longrightarrow> snth n s = sfoot s"

(*-----------------------------*)
sfilter
(*-----------------------------*)

(* if filtering the stream s2 with the set A produces infinitely many elements then prepending any
   finite stream s1 to s2 will still produce infinitely many elements *)
lemma sfilter_conc2[simp]: assumes "#(sfilter A\<cdot>s2) = \<infinity>" and "#s1 < \<infinity>"
  shows "#(sfilter A\<cdot>(s1\<bullet>s2)) = \<infinity>"

(* if the stream z is a prefix of another non-empty stream (y\<bullet>\<up>a) but isn't equal to it, then z is
   also a prefix of y *)
lemma below_conc: assumes "z \<sqsubseteq> (y\<bullet>\<up>a)" and "z\<noteq>(y\<bullet>\<up>a)"
  shows "z\<sqsubseteq>y"

(* for any set A and singleton stream \<up>a the following predicate over streams is admissible *)
lemma sfilter_conc_adm: "adm (\<lambda>b. #b<\<infinity> \<longrightarrow> #(A \<ominus> b) < #(A \<ominus> b \<bullet> \<up>a))" (is "adm ?F")

(* the element a is kept when filtering with A, so (x \<bullet> \<up>a) produces a larger result than just x,
   provided that x is finite *)
lemma sfilter_conc: assumes "a\<in>A" 
  shows "#x<\<infinity> \<Longrightarrow> #(A \<ominus> x) < #(A \<ominus> (x \<bullet> \<up>a))" (is "_ \<Longrightarrow> ?F x")

(* for any finite stream s and set A, if filtering s with A doesn't produce the empty stream, then
   filtering and infinite repetition are associative *)
lemma sfilter_sinf [simp]: assumes "#s<\<infinity>" and "(A \<ominus> s) \<noteq> \<epsilon>"
  shows "A \<ominus> (s\<infinity>) = (A \<ominus> s)\<infinity>"

(* if filtering the stream s with the set A produces infinitely many elements, then filtering the 
   rest of s with A also produces infinitely many elements *)
lemma sfilter_srt_sinf [simp]: assumes "#(A \<ominus> s) = \<infinity>" 
  shows  "#(A \<ominus> (srt\<cdot>s)) = \<infinity>"

text {* Streams can be split for filtering *}
lemma add_sfilter2: assumes "#x < \<infinity>" 
  shows "sfilter A\<cdot>(x \<bullet> y) = sfilter A\<cdot>x \<bullet> sfilter A\<cdot>y"

(* if none of the elements in the domain of the stream s are in the set A, then filtering s with A
   produces the empty stream *)
lemma sfilter_sdom_eps: "sdom\<cdot>s \<inter> A = {} \<Longrightarrow> (A \<ominus> s) = \<epsilon>"

(*-----------------------------*)
stakewhile
(*-----------------------------*)
(* stakewhile can't increase the length of a stream *)
lemma stakewhile_less [simp]: "#(stakewhile f\<cdot>s)\<le>#s"

(* stakewhile doesn't take elements past an element that fails the predicate f *)
lemma stakewhile_slen[simp]: "\<not>f (snth n s) \<Longrightarrow> #(stakewhile f\<cdot>s)\<le>Fin n"

(* the prefix of the constant stream of x's whose elements aren't equal to x is empty *)
lemma [simp]: "stakewhile (\<lambda>a. a \<noteq> x)\<cdot>\<up>x\<infinity> = \<epsilon>"

(* stakewhile produces a prefix of the input *)
lemma stakewhile_below[simp]: "stakewhile f\<cdot>s \<sqsubseteq> s"

(* stwbl produces a prefix of the input *)
lemma stwbl_below [simp]: "stwbl f\<cdot>s \<sqsubseteq> s"

(* stakewhile doesn't include the element a that failed the predicate f in the result *)
lemma stakewhile_dom[simp]:assumes "\<not>f a"
  shows "a\<notin>sdom\<cdot>(stakewhile f\<cdot>s)"

(* if stakewhile leaves a stream s unchanged, then every element must pass the predicate f *) 
lemma stakewhile_id_snth: assumes "stakewhile f\<cdot>s = s" and "Fin n < #s"
  shows "f (snth n s)"

(* if stakewhile produces a result of length n or greater, then the nth element in s must pass f *)
lemma stakewhile_snth[simp]: assumes  "Fin n < #(stakewhile f\<cdot>s)"
  shows "f (snth n s)"

(* if stakewhile changes the stream s, then there must be an element in s that fails the predicate f *)
lemma stakewhile_notin [simp]: 
  shows "stakewhile f\<cdot>s \<noteq> s \<Longrightarrow> #(stakewhile f\<cdot>s) = Fin n \<Longrightarrow> \<not> f (snth n s)"

(* if stakewhile changes the stream s, which is a prefix of the stream s', then stakewhile of s and s'
   produce the same result *)
lemma stakewhile_finite_below: 
  shows "stakewhile f\<cdot>s \<noteq> s \<Longrightarrow> s\<sqsubseteq>s' \<Longrightarrow> stakewhile f\<cdot>s = stakewhile f\<cdot>s'"

(* if there is an element in the stream s that fails the predicate f, then stakewhile will change s *)
lemma stakewhile_noteq[simp]: assumes "\<not>f (snth n s)" and "Fin n < #s"
  shows "stakewhile f\<cdot>s \<noteq> s"

(* if there's an element a in the domain of s which fails the predicate f, then stwbl will produce a
   finite result *)
lemma stwbl_fin [simp]: assumes "a\<in>sdom\<cdot>s" and "\<not> f a"
  shows "#(stwbl f\<cdot>s) < \<infinity>"

(* stwbl keeps at least all the elements that stakewhile keeps *)
lemma stakewhile_stwbl [simp]: "stakewhile f\<cdot>(stwbl f\<cdot>s) = stakewhile f\<cdot>s"

lemma sdom_sfilter1: assumes "x\<in>sdom\<cdot>(A\<ominus>s)" 
  shows "x\<in>A"

lemma sdom_subset: assumes "u\<noteq>\<bottom>"
  shows "sdom\<cdot>s\<subseteq>sdom\<cdot>(u && s)"

lemma sdom_sfilter_subset: assumes "u\<noteq>\<bottom>"
  shows "sdom\<cdot>(A\<ominus>s)\<subseteq>sdom\<cdot>(A \<ominus> (u && s))"

lemma sdom_sfilter2: assumes  "x\<in>A"
  shows "x\<in>sdom\<cdot>s \<Longrightarrow> x\<in>(sdom\<cdot>(A \<ominus> s))"

lemma sdom_sfilter[simp]: "sdom\<cdot>(A\<ominus>s) = sdom\<cdot>s \<inter> A"

lemma stwbl_id_help:
  shows "(\<forall>a\<in>sdom\<cdot>s. f a) \<longrightarrow> stwbl f\<cdot>s = s"

lemma stwbl_id [simp]: "(\<And> a. a\<in>sdom\<cdot>s \<Longrightarrow> f a) \<Longrightarrow> stwbl f\<cdot>s = s"

lemma stwbl_notEps: "s\<noteq>\<epsilon> \<Longrightarrow> (stwbl f\<cdot>s)\<noteq>\<epsilon>"

lemma stwbl2stakewhile: assumes "a\<in>sdom\<cdot>s" and "\<not>f a"
  shows "\<exists>x. (stwbl f\<cdot>s) = stakewhile f\<cdot>s \<bullet> \<up>x" 

lemma stwbl_sfoot: assumes "a\<in>sdom\<cdot>s" and "\<not>f a"
  shows "\<not> f (sfoot (stwbl f\<cdot>s))" 

lemma stwbl2stbl[simp]: "stwbl f\<cdot>(stwbl f\<cdot>s) = stwbl f\<cdot>s"

lemma stakewhileDropwhile[simp]: "stakewhile f\<cdot>s \<bullet> (sdropwhile f\<cdot>s) = s "

lemma stwbl_eps: "stwbl f\<cdot>s = \<epsilon> \<longleftrightarrow> s=\<epsilon>"

lemma srtdw_stwbl [simp]: "srtdw f\<cdot> (stwbl f\<cdot>s) = \<epsilon>" (is "?F s")

lemma sconc_neq_h: assumes "s1 \<noteq> s2"
  shows "#a < \<infinity> \<longrightarrow> a \<bullet> s1 \<noteq> a \<bullet> s2"

lemma sconc_neq: assumes "s1 \<noteq> s2" and "#a < \<infinity>"
  shows "a \<bullet> s1 \<noteq> a \<bullet> s2"

lemma adm_nsdom [simp]:  "adm (\<lambda>x. b \<notin> sdom\<cdot>x)"

lemma strdw_filter_h: "b\<in>sdom\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"

lemma strdw_filter: "b\<in>sdom\<cdot>s \<Longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"

lemma stwbl_filterlen[simp]: "b\<in>sdom\<cdot>ts \<longrightarrow> #({b} \<ominus> stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts) = Fin 1"

lemma srtdw_conc: "b\<in>sdom\<cdot>ts  \<Longrightarrow> (srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts \<bullet> as)) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts) \<bullet> as"

lemma stwbl_conc[simp]: "b\<in>sdom\<cdot>ts \<Longrightarrow>
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts \<bullet> xs)) =
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(ts))"

(*-----------------------------*)
merge
(*-----------------------------*)

definition merge:: "('a  \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a stream \<rightarrow> 'b stream \<rightarrow> 'c stream" where
"merge f \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. f (fst s3) (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"

lemma merge_unfold: "merge f\<cdot>(\<up>x \<bullet> xs)\<cdot>(\<up>y\<bullet> ys) = \<up>(f x y) \<bullet> merge f\<cdot>xs\<cdot>ys"

lemma merge_snth[simp]: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (merge f\<cdot>xs\<cdot>ys) = f (snth n xs) (snth n ys)"

lemma merge_eps1[simp]: "merge f\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"

lemma merge_eps2[simp]: "merge f\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"

lemma [simp]: "srt\<cdot>(merge f\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet> bs)) = merge f\<cdot>as\<cdot>bs"

lemma merge_len [simp]: "#(merge f\<cdot>as\<cdot>bs) = min (#as) (#bs)"

lemma merge_commutative: assumes "\<And> a b. f a b = f b a"

(*-----------------------------*)
sconc
(*-----------------------------*)



(* the lazy stream constructor and concatenation are associative *) 
lemma sconc_scons': "(updis a && as) \<bullet> s = updis a && (as \<bullet> s)"

(* the lazy stream constructor is equivalent to concatenation with a singleton stream *)
lemma lscons_conv: "updis a && s = \<up>a \<bullet> s"

(* concatenation with respect to singleton streams is associative *)
lemma sconc_scons[simp]: "(\<up>a \<bullet> as) \<bullet> s = \<up>a \<bullet> (as \<bullet> s)"

lemma scases: "\<And>x P. \<lbrakk>x = \<epsilon> \<Longrightarrow> P; \<And>a s. x = \<up>a \<bullet> s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"

(* Single element streams commute with the stake operation. *)
lemma stake_Suc[simp]: "stake (Suc n)\<cdot>(\<up>a \<bullet> as) = \<up>a \<bullet> stake n\<cdot>as"

(* shd is the inverse of prepending a singleton *)
lemma shd1[simp]: "shd (\<up>a \<bullet> s) = a"

(* srt is the inverse of appending to a singleton *)
lemma [simp]: "srt\<cdot>(\<up>a\<bullet>as) = as"

(* appending to a singleton is monotone *)
lemma [simp]: "\<up>a \<sqsubseteq> \<up>a \<bullet> s"
apply (subst sconc_snd_empty [of "\<up>a", THEN sym])

(* updis is a bijection *)
lemma updis_eq: "(updis a = updis b) = (a = b)"

(* the discrete order only considers equal elements to be ordered *)
lemma updis_eq2: "(updis a \<sqsubseteq> updis b) = (a = b)"

text {* Mapping a stream to head and rest is injective *}
lemma inject_scons: "\<up>a \<bullet> s1 = \<up>b \<bullet> s2 \<Longrightarrow> a = b \<and> s1 = s2"



(* appending a stream x to a singleton stream and producing another singleton stream implies that 
   the two singleton streams are equal and x was empty *)
lemma [simp]: "(\<up>a \<bullet> x = \<up>c) = (a = c \<and> x = \<epsilon>)"

lemma [simp]: "(\<up>c = \<up>a \<bullet> x) = (a = c \<and> x = \<epsilon>)"

lemma [simp]: "(\<up>a \<bullet> x \<sqsubseteq> \<up>b) = (a = b \<and> x = \<epsilon>)" 

(* if a singleton stream is the prefix of another stream then the heads of the two streams must match *)
lemma [simp]: "(\<up>a \<sqsubseteq> \<up>b \<bullet> x) = (a = b)" 

(* if x isn't empty then concatenating head and rest leaves the stream unchanged *)
lemma surj_scons: "x\<noteq>\<epsilon> \<Longrightarrow> \<up>(shd x) \<bullet> (srt\<cdot>x) = x"

(* any nonempty prefix of a stream y is still a prefix when ignoring the first element *)
lemma less_fst_sconsD: "\<up>a \<bullet> as \<sqsubseteq> y \<Longrightarrow> \<exists>ry. y = \<up>a \<bullet> ry \<and> as \<sqsubseteq> ry"

(* the prefix of any non-empty stream is either empty or shares the same first element *)
lemma less_snd_sconsD: 
  "x \<sqsubseteq> \<up>a\<bullet>as \<Longrightarrow> (x = \<epsilon>) \<or> (\<exists>rx. x = \<up>a\<bullet>rx \<and> rx \<sqsubseteq> as)"

(* semantically equivalent to less_fst_sconsD *)
lemma lessD: 
  "x \<sqsubseteq> y \<Longrightarrow> (x = \<epsilon>) \<or> (\<exists>a q w. x = \<up>a\<bullet>q \<and> y = \<up>a\<bullet>w \<and> q \<sqsubseteq> w)"

(*-----------------------------*)
slen
(*-----------------------------*)


text {* Streams with infinite prefixes are infinite *}
lemma mono_fst_infD: "\<lbrakk>#x = \<infinity>; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> #y = \<infinity> "

text {* For @{term "s \<sqsubseteq> t"} with @{term s} and @{term t} of
  equal length, all finite prefixes are identical *}
lemma stake_eq_slen_eq_and_less: 
  "\<forall>s t. #s = #t \<and> s \<sqsubseteq> t \<longrightarrow> stake n\<cdot>s = stake n\<cdot>t"

text {* For @{term "s \<sqsubseteq> t"} with @{term s} and @{term t} of
  equal length, @{term s} and @{term t} are identical *}
lemma eq_slen_eq_and_less: "\<lbrakk>#s = #t; s \<sqsubseteq> t\<rbrakk> \<Longrightarrow> s = t"

text {* Infinite prefixes are equal to the original stream *}
lemma eq_less_and_fst_inf: "\<lbrakk>s1 \<sqsubseteq> s2; #s1 = \<infinity>\<rbrakk> \<Longrightarrow> s1 = s2"

text {* For infinite streams, @{text "stake n"} returns @{text "n"} elements *}
lemma slen_stake_fst_inf[rule_format]: 
  "\<forall>x. #x = \<infinity> \<longrightarrow> #(stake n\<cdot>x) = Fin n"

(* mapping a stream to its length is a monotone function *)
lemma mono_slen: "x \<sqsubseteq> y \<Longrightarrow> #x \<le> #y"

text {* A stream is shorter than @{text "n+1"} iff its rest is shorter than @{text "n"} *}
lemma slen_rt_ile_eq: "(#x \<le> Fin (Suc n)) = (#(srt\<cdot>x) \<le> Fin n)"  

text {* If @{text "#x < #y"}, this also applies to the streams' rests (for nonempty, finite x) *}
lemma smono_slen_rt_lemma: 
  "#x = Fin k \<and> x \<noteq> \<epsilon> \<and> #x < #y \<longrightarrow> #(srt\<cdot>x) < #(srt\<cdot>y)"

text {* If @{text "#x < #y"}, this also applies to the streams' rests (for finite x) *}
lemma smono_slen_rt: "\<lbrakk>x \<noteq> \<epsilon>; #x < #y\<rbrakk> \<Longrightarrow> #(srt\<cdot>x) < #(srt\<cdot>y)"

text {* Infinite elements of a stream chain are equal to the LUB *}
lemma inf2max: "\<lbrakk>chain Y; #(Y k) = \<infinity>\<rbrakk> \<Longrightarrow> Y k = (\<Squnion>i. Y i)"

text {* @{text "stake n"} returns at most @{text "n"} elements *}
lemma ub_slen_stake[simp]: "#(stake n\<cdot>x) \<le> Fin n"

text {* @{text "stake"} always returns finite streams *}
lemma [simp]: "#(stake n\<cdot>x) \<noteq> \<infinity>"

text {* @{text "stake"}ing at least @{text "#x"} elements returns @{text "x"} again *}
lemma fin2stake_lemma: "\<forall>x k. #x = Fin k \<and> k\<le>i \<longrightarrow> stake i\<cdot>x = x"

text {* @{text "stake"}ing @{text "#x"} elements returns @{text "x"} again *}
lemma fin2stake:"#x = Fin n \<Longrightarrow> stake n\<cdot>x = x"

(*-----------------------------*)
induction
(*-----------------------------*)

lemma stakeind: 
  "\<forall>x. (P \<epsilon> \<and> (\<forall>a s. P s \<longrightarrow> P (\<up>a \<bullet> s))) \<longrightarrow> P (stake n\<cdot>x)"

text {* induction for finite streams *}
lemma finind:
  "\<lbrakk>#x = Fin n; P \<epsilon>; \<And>a s. P s \<Longrightarrow> P (\<up>a \<bullet> s)\<rbrakk> \<Longrightarrow> P x"

text {* induction for infinite streams and admissable predicates *}
lemma ind: 
  "\<lbrakk>adm P; P \<epsilon>; \<And>a s. P s  \<Longrightarrow> P (\<up>a \<bullet> s)\<rbrakk> \<Longrightarrow> P x"

(*-----------------------------*)
sdrop
(*-----------------------------*)

lemma sdrop_0[simp]: "sdrop 0\<cdot>s = s"

(* dropping an additional element is equivalent to calling srt *)
lemma sdrop_back_rt: "sdrop (Suc n)\<cdot>s = srt\<cdot>(sdrop n\<cdot>s)"

lemma sdrop_forw_rt: "sdrop (Suc n)\<cdot>s = sdrop n\<cdot>(srt\<cdot>s)"

(* dropping n + 1 elements from a non-empty stream is equivalent to dropping n items from the rest *)
lemma sdrop_scons[simp]: "sdrop (Suc n)\<cdot>(\<up>a \<bullet> as) = sdrop n\<cdot>as"

(* if dropping n items produces the empty stream then the stream contains n elements or less *)
lemma sdrop_stakel1: "\<forall>s. sdrop n\<cdot>s = \<epsilon> \<longrightarrow> stake n\<cdot>s = s"

text {* Dropping from infinite streams still returns infinite streams *}
lemma fair_sdrop[rule_format]: 
  "\<forall>x. #x = \<infinity> \<longrightarrow> #(sdrop n\<cdot>x) = \<infinity>"

text {* streams can be split by @{term stake} and @{term sdrop} *}
lemma split_streaml1[simp]: 
  "stake n\<cdot>s \<bullet> sdrop n\<cdot>s = s"

text {* @{term sdrop} may only create infinite outputs for infinite inputs *}
lemma fair_sdrop_rev:
  "#(sdrop k\<cdot>x) = \<infinity> \<Longrightarrow> #x = \<infinity>"

text {* construct @{term "sdrop j"} from @{term "sdrop k"} (with @{term "j \<le> k"}) *}
lemma sdropl5:
  "j \<le> k \<Longrightarrow> sdrop j\<cdot>(stake k\<cdot>x) \<bullet> sdrop k\<cdot>x = sdrop j\<cdot>x"

text {* Dropping as inverse of prepending a finite stream *}
lemma sdropl6:
  "#x = Fin k \<Longrightarrow> sdrop k\<cdot>(x \<bullet> y) = y"

(*-----------------------------*)
snth
(*-----------------------------*)

(* semantically equivalent to snth_rt *)
lemma snth_scons[simp]: "snth (Suc k) (\<up>a \<bullet> s) = snth k s"


(*-----------------------------*)
lemmas
(*-----------------------------*)


(*-----------------------------*)
approx, chains, cont
(*-----------------------------*)



text {* If @{term f} is monotone and for each @{term x} there is a finite prefix
  @{term y} such that @{term "f x = f y"}, @{term f} is continuous *}
lemma pr_contI: 
  "\<lbrakk>monofun f; \<forall>x.\<exists>n. (f x) = f (stake n\<cdot>x)\<rbrakk> \<Longrightarrow> cont f"

text {* For continuous functions, each finite prefix of @{term "f\<cdot>x"} only
  depends on a finite prefix of @{term "x"} *}
lemma fun_approxl1: 
  "\<exists>j. stake k\<cdot>(f\<cdot>x) = stake k\<cdot>(f\<cdot>(stake j\<cdot>x))"

text {* For continuous functions, any finite output for stream @{term "x"} can also be
  obtained by some finite prefix of @{term "x"} *}
lemma fun_approxl2: "#(f\<cdot>x) = Fin k \<Longrightarrow> \<exists>j. f\<cdot>x = f\<cdot>(stake j\<cdot>x)" 

(*-----------------------------*)
slookahd
(*-----------------------------*)

text {* @{term slookahd} is continuous *}
lemma cont_slookahd[simp]: "cont (\<lambda> s. if s=\<epsilon> then \<bottom> else eq (shd s))"

(* slookahd applied to the empty stream results in the bottom element for any function eq *)
lemma strict_slookahd[simp]: "slookahd\<cdot>\<epsilon>\<cdot>eq = \<bottom>"

(* if s isn't the empty stream, the function eq will be applied to the head of s *)
lemma slookahd_scons[simp]: "s\<noteq>\<epsilon> \<Longrightarrow> slookahd\<cdot>s\<cdot>eq = eq (shd s)"

(* the constant function that always returns the empty stream unifies the two cases of slookahd *)
lemma strict2_slookahd[simp]: "slookahd\<cdot>xs\<cdot>(\<lambda>y. \<epsilon>) = \<epsilon>"

(*-----------------------------*)
sinftimes
(*-----------------------------*)

text {* For nonempty @{term s}, @{term "sinftimes s"} is infinite *}
lemma slen_sinftimes: "s \<noteq> \<epsilon> \<Longrightarrow> #(sinftimes s) = \<infinity>"

lemma [simp]: "#(sinftimes (\<up>a)) = \<infinity>" 

(*-----------------------------*)
sprojfst
(*-----------------------------*)

(* sprojfst extracts the first element of the first tuple in any non-empty stream of tuples *)
lemma sprojfst_scons[simp]: "sprojfst\<cdot>(\<up>(x, y) \<bullet> s) = \<up>x \<bullet> sprojfst\<cdot>s"

(* sprojfst extracts the first element of any singleton tuple-stream *)
lemma [simp]: "sprojfst\<cdot>(\<up>(a,b)) = \<up>a"

(* sprojsnd extracts the second element of the first tuple in any non-empty stream of tuples *)
lemma sprojsnd_scons[simp]: "sprojsnd\<cdot>(\<up>(x,y) \<bullet> s) = \<up>y \<bullet> sprojsnd\<cdot>s"

(* sprojsnd extracts the second element of any singleton tuple-stream *)
lemma [simp]: "sprojsnd\<cdot>(\<up>(a,b)) = \<up>b"

lemma rt_Sproj_2_eq: "sprojsnd\<cdot>(srt\<cdot>x) = srt\<cdot>(sprojsnd\<cdot>x)"

lemma rt_Sproj_1_eq: "sprojfst\<cdot>(srt\<cdot>x) = srt\<cdot>(sprojfst\<cdot>x)"

text {* length of projections and the empty stream *}

(*-----------------------------*)
sfilter
(*-----------------------------*)

(* if the head of a stream is in M, then sfilter will keep the head *)
lemma sfilter_in[simp]: 
  "a \<in> M \<Longrightarrow> sfilter M\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> sfilter M\<cdot>s" 

(* if the head of a stream isn't in M, then sfilter will discard the head *)
lemma sfilter_nin[simp]: 
  "a \<notin> M \<Longrightarrow> sfilter M\<cdot>(\<up>a \<bullet> s) = sfilter M\<cdot>s" 

(* if the sole element in a singleton stream is in M then sfilter is a no-op *)
lemma [simp]: "a \<in> M \<Longrightarrow> sfilter M\<cdot>(\<up>a) = \<up>a"

(* if the sole element in a singleton stream is not in M then sfilter produces the empty stream *)
lemma [simp]: "a \<notin> M \<Longrightarrow> sfilter M\<cdot>(\<up>a) = \<epsilon>"

(* filtering all elements that aren't in {a} from a stream consisting only of the element a has no effect *)
lemma sfilter_sinftimes_in[simp]: 
  "sfilter {a}\<cdot>(sinftimes (\<up>a)) = sinftimes (\<up>a)"
 (subst sinftimes_unfold, simp)

(* if the element a isn't in the set F then filtering a stream of infinitely many a's using F will
   produce the empty stream *)
lemma sfilter_sinftimes_nin:
  "a \<notin> F \<Longrightarrow> (F \<ominus> (sinftimes (\<up>a))) = \<epsilon>"

text {* Filtering a postfix is at most as long as filtering the whole stream *}
lemma slen_sfilter_sdrop_ile: 
  "#(sfilter X\<cdot>(sdrop n\<cdot>p)) \<le> #(sfilter X\<cdot>p)"

text {* If the filtered stream is infinite, each filtered postfix is infinite *}
lemma slen_sfilter_sdrop: 
  "\<forall>p X. #(sfilter X\<cdot>p) = \<infinity> \<longrightarrow> #(sfilter X\<cdot>(sdrop n\<cdot>p)) = \<infinity>" 

text {* @{term sfilter} on @{term "stake n"} returns @{text "\<epsilon>"} if none of the first
  @{term n} elements is included in the filter *}
lemma sfilter_empty_snths_nin_lemma: 
  "\<forall>p. (\<forall>n. Fin n < #p \<longrightarrow> snth n p \<notin> X) \<longrightarrow> sfilter X\<cdot>(stake k\<cdot>p) = \<epsilon>"

text {* @{term sfilter} returns @{text "\<epsilon>"} if no element is included in the filter *}
lemma ex_snth_in_sfilter_nempty:
  "(\<forall>n. Fin n < #p \<longrightarrow> snth n p \<notin> X) \<Longrightarrow> sfilter X\<cdot>p = \<epsilon>"

text {* Prepending to the original stream never shortens the filtered result *}
lemma sfilterl2: 
  "\<forall>z. #(sfilter X\<cdot>s) \<le> #(sfilter X\<cdot>((stake n\<cdot>z) \<bullet> s))"

text {* The filtered result is not changed by concatenating streams which are
  filtered to @{text "\<epsilon>"} *}
lemma sfilterl3:
  "\<forall>s. #s = Fin k \<and> sfilter S\<cdot>s = \<epsilon> \<longrightarrow> 
       sfilter S\<cdot>(s\<bullet>Z) = sfilter S\<cdot>Z" 

text {* A stream can be split by @{term stake} and @{term sdrop} for filtering *}
lemma split_sfilter: "sfilter X\<cdot>x = sfilter X\<cdot>(stake n\<cdot>x) \<bullet> sfilter X\<cdot>(sdrop n\<cdot>x)"

text {* double filtering *}
lemma int_sfilterl1[simp]: "sfilter S\<cdot>(sfilter M\<cdot>s) = sfilter (S \<inter> M)\<cdot>s"

text {* Streams can be split for filtering *}
lemma add_sfilter:
  "#x = Fin k \<Longrightarrow> sfilter t\<cdot>(x \<bullet> y) = sfilter t\<cdot>x \<bullet> sfilter t\<cdot>y"

text {* After applying @{term "smap f"}, all elements are in the range of @{term f} *}
lemma sfilter_smap_nrange: 
  "m \<notin> range f \<Longrightarrow> sfilter {m}\<cdot>(smap f\<cdot>x) = \<epsilon>"

(*-----------------------------*)
stakewhile
(*-----------------------------*)

lemma strict_stakewhile[simp]: "stakewhile f\<cdot>\<epsilon> = \<epsilon>"

(* if the head a passes the predicate f, then the result of stakewhile will start with \<up>a *)
lemma stakewhile_t[simp]: "f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> stakewhile f\<cdot>s"

(* if the head a fails the predicate f, then stakewhile will produce the empty stream *)
lemma stakewhile_f[simp]: "\<not>f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a \<bullet> s) = \<epsilon>"

(* if the element a passes the predicate f, then stakewhile applied to \<up>a is a no-op *)
lemma [simp]: "f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a) = \<up>a"

(* if the element a fails the predicate f, then stakewhile applied to \<up>a will produce the empty stream *)
lemma [simp]: "\<not>f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a) = \<epsilon>"

lemma strict_stwbl[simp]: "stwbl f\<cdot>\<epsilon> = \<epsilon>"

(* if the head a passes the predicate f, then the result of stwbl will start with \<up>a *)
lemma stwbl_t[simp]: "f a \<Longrightarrow> stwbl f\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> stwbl f\<cdot>s"

(* if the head a fails the predicate f, then stwbl will produce only \<up>a *)
lemma stwbl_f[simp]: "\<not> f a \<Longrightarrow> stwbl f\<cdot>(\<up>a \<bullet> s) = \<up>a"

text {* @{term sfilter} after @{term stakewhile}: produce the empty stream *}
lemma sfilter_twl1[simp]: 
  "sfilter X\<cdot>(stakewhile (\<lambda>x. x\<notin>X)\<cdot>p) = \<epsilon>"

text {* @{term sfilter} after @{term stakewhile}: redundant filtering *}
lemma sfilter_twl2[simp]: 
  "sfilter X\<cdot>(stakewhile (\<lambda>x. x\<in>X)\<cdot>p) = stakewhile (\<lambda>x. x\<in>X)\<cdot>p"

text {* If @{term "stakewhile (\<lambda>p. p = t)"} returns an infinite stream, all prefixes
  of the original stream only consist of "@{term t}"s *}
lemma stakewhile_sinftimes_lemma: 
  "\<forall>z. #(stakewhile (\<lambda>p. p = t)\<cdot>z) = \<infinity> \<longrightarrow> stake n\<cdot>z = stake n\<cdot>(sinftimes (\<up>t))"

text {* If @{term "stakewhile (\<lambda>p. p = t)"} returns an infinite stream, the original stream
  is an infinite "@{term t}"-stream *}
lemma stakewhile_sinftimesup: 
  "#(stakewhile (\<lambda>p. p = t)\<cdot>z) = \<infinity> \<Longrightarrow> z = sinftimes (\<up>t)"


(*-----------------------------*)
sdropwhile
(*-----------------------------*)

lemma strict_sdropwhile[simp]: "sdropwhile f\<cdot>\<epsilon> = \<epsilon>"

(* if the head a passes the predicate f, then the result of sdropwhile will drop the head *)
lemma sdropwhile_t[simp]: "f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a \<bullet> s) = sdropwhile f\<cdot>s"

(* if the head a fails the predicate f, then the result of sdropwhile will start with \<up>a *)
lemma sdropwhile_f[simp]: "\<not>f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> s"

(* if the only element in a singleton stream passes the predicate f, then sdropwhile will produce
   the empty stream *)
lemma [simp]: "f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a) = \<epsilon>"

(* if the only element in a singleton stream fails the predicate f, then sdropwhile will be a no-op *)
lemma [simp]: "\<not>f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a) = \<up>a"

(* the elements removed by sdropwhile are a subset of the elements removed by sfilter *)
lemma sfilter_dwl1[simp]: 
  "sfilter X\<cdot>(sdropwhile (\<lambda>x. x\<notin>X)\<cdot>p) = sfilter X\<cdot>p"

(* the elements kept by sfilter are a subset of the elements kept by sdropwhile *)
lemma sfilter_dwl2:
  "sfilter T\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> sdropwhile (\<lambda>a. a \<notin> T)\<cdot>s \<noteq> \<epsilon>"

text {* Construct @{term stwbl} from @{term stakewhile}, @{term stake} and @{term sdropwhile} *}
lemma stwbl_stakewhile: "stwbl f\<cdot>s = stakewhile f\<cdot>s \<bullet> (stake (Suc 0)\<cdot>(sdropwhile f\<cdot>s))"

text {* Constructing @{term sdropwhile} from @{term stakewhile} and @{term sdrop} *}
lemma stakewhile_sdropwhilel1:
  "\<forall>x. #(stakewhile f\<cdot>x) = Fin n \<longrightarrow> sdropwhile f\<cdot>x = sdrop n\<cdot>x"  

text {* @{term sdropwhile} is idempotent *}
lemma sdropwhile_idem: "sdropwhile f\<cdot>(sdropwhile f\<cdot>x) = sdropwhile f\<cdot>x"

text {* @{term stakewhile} after @{term sdropwhile} gives the empty stream *}
lemma tdw[simp]: "stakewhile f\<cdot>(sdropwhile f\<cdot>s) = \<epsilon>"

text {* For the head of @{term "sdropwhile f\<cdot>x"}, @{term f} does not hold *}
lemma sdropwhile_resup: "sdropwhile f\<cdot>x = \<up>a \<bullet> s \<Longrightarrow> \<not> f a"

text {* elimination rule for @{term sfilter} after @{term sdropwhile} *}
lemma sfilter_srtdwl3[simp]: 
  "sfilter X\<cdot>(srt\<cdot>(sdropwhile (\<lambda>x. x\<notin>X)\<cdot>p)) = srt\<cdot>(sfilter X\<cdot>p)"

text {* After filtering by filter @{term T}, the head of the result is in @{term T}
  (for non-empty results) *}
lemma sfilter_ne_resup: "sfilter T\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> shd (sfilter T\<cdot>s) \<in> T"

text {* same result for @{term sconc} syntax *}
lemma sfilter_resl2:
  "sfilter T\<cdot>s = \<up>a \<bullet> as \<Longrightarrow> a \<in> T"

text {* After filtering with filter @{term T}, each element is in @{term T} *}
lemma sfilterl7:
  "\<lbrakk>Fin n < #x; sfilter T\<cdot>s = x\<rbrakk> \<Longrightarrow> snth n x \<in> T"

(*-----------------------------*)
srtdw
(*-----------------------------*)

lemma [simp]: "srtdw f\<cdot>\<epsilon> = \<epsilon>"

(* the rest of any singleton stream is the empty stream, regardless of whether the only element in
   the stream was dropped *)
lemma [simp]: "srtdw f\<cdot>(\<up>a) = \<epsilon>"

(* if the head a passes the predicate f, srtdw will drop the head *)
lemma [simp]: "f a \<Longrightarrow> srtdw f\<cdot>(\<up>a\<bullet>as) = srtdw f\<cdot>as"

(* if the head a fails the predicate f, srtdw will produce the rest of the stream *)
lemma [simp]: "\<not> f a \<Longrightarrow> srtdw f\<cdot>(\<up>a\<bullet>as) = as"

text {* @{term "sfilter M"} after @{term "srtdw (\<lambda>x. x \<notin> M)"} almost behaves
  like @{term "sfilter M"} alone *}
lemma sfilterl8:
  "sfilter M\<cdot>x \<noteq> \<epsilon> \<Longrightarrow>
    #(sfilter M\<cdot>x) = lnsuc\<cdot>(#(sfilter M\<cdot>(srtdw (\<lambda>x. x \<notin> M)\<cdot>x)))"

text {* similar result for infinite streams *}
lemma sfilter_srtdwl2:
  "#(sfilter X\<cdot>s) = \<infinity> \<Longrightarrow> #(sfilter X\<cdot>(srtdw (\<lambda>a. a \<notin> X)\<cdot>s)) = \<infinity>"

text {* streams can be split by @{term stwbl} and @{term srtdw} *}
lemma stwbl_srtdw: "stwbl f\<cdot>s \<bullet> srtdw f\<cdot>s = s"

lemma slen_srtdw: "#(srtdw f\<cdot>x) \<le> #x"

(*-----------------------------*)
srcdups
(*-----------------------------*)

lemma strict_srcdups[simp]: "srcdups\<cdot>\<epsilon> = \<epsilon>" 

(* a singleton stream can't possibly contain duplicates *)
lemma [simp]: "srcdups\<cdot>(\<up>a) = \<up>a"

(* if the head a of a stream is followed by a duplicate, only one of the two elements will be kept by srcdups *)
lemma srcdups_eq[simp]: "srcdups\<cdot>(\<up>a\<bullet>\<up>a\<bullet>s) = srcdups\<cdot>(\<up>a\<bullet>s)" 

(* if the head a of a stream is followed by a distinct element, both elements will be keypt by srcdups *)
lemma srcdups_neq[simp]: 
  "a\<noteq>b \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s) = \<up>a \<bullet>  srcdups\<cdot>(\<up>b \<bullet> s)" 

(*-----------------------------*)
szip
(*-----------------------------*)

lemma strict_szip_fst[simp]: "szip\<cdot>\<epsilon>\<cdot>s = \<epsilon>"

lemma strict_szip_snd[simp]: "szip\<cdot>s\<cdot>\<epsilon> = \<epsilon>"

lemma szip_scons[simp]: "szip\<cdot>(\<up>a\<bullet>s1)\<cdot>(\<up>b\<bullet>s2) = \<up>(a,b) \<bullet> (szip\<cdot>s1\<cdot>s2)"

lemma [simp]: "szip\<cdot>(\<up>a)\<cdot>(\<up>b \<bullet> y) = \<up>(a,b)"

lemma [simp]: "szip\<cdot>(\<up>a \<bullet> x)\<cdot>(\<up>b) = \<up>(a,b)"

lemma [simp]: "szip\<cdot>(\<up>a)\<cdot>(\<up>b) = \<up>(a,b)"

text {* If @{term szip} returns an empty stream, an input stream was empty *}
lemma strict_rev_szip: "szip\<cdot>x\<cdot>y = \<epsilon> \<Longrightarrow> x = \<epsilon> \<or> y = \<epsilon>"

lemma sprojfst_szipl1[rule_format]: 
  "\<forall>x. #x = \<infinity> \<longrightarrow> sprojfst\<cdot>(szip\<cdot>i\<cdot>x) = i"

lemma sprojsnd_szipl1[rule_format]: 
  "\<forall>x. #x = \<infinity> \<longrightarrow> sprojsnd\<cdot>(szip\<cdot>x\<cdot>i) = i"

(*-----------------------------*)
siterate
(*-----------------------------*)

text {* @{term siterate} is defined by running @{term sscanl} on an arbitrary
  infinite stream. Only the stream length is relevant for the result *}
lemma siterate_inv_lemma:
  "\<forall>x z a. #z = #x 
     \<longrightarrow> stake n\<cdot>(sscanl (\<lambda>a b. f a) a\<cdot>x) = 
        stake n\<cdot>(sscanl (\<lambda>a b. f a) a\<cdot>z)"

text {* @{term siterate} is well-defined (because it is independent of
  the infinite stream on which @{term sscanl} is applied) *}
lemma siterate_def2:
  "#x = \<infinity> \<Longrightarrow> siterate f a = \<up>a \<bullet> sscanl (\<lambda>a b. f a) a\<cdot>x"

text {* unfolding of @{term siterate} definition *}
lemma siterate_scons: "siterate f a = \<up>a \<bullet> siterate f (f a)"

lemma snth_siterate_Suc: "snth k (siterate Suc j) = k + j"

lemma snth_siterate_Suc_0[simp]: "snth k (siterate Suc 0) = k"

lemma sdrop_siterate:
  "sdrop k\<cdot>(siterate Suc j) = siterate Suc (j + k)"

text {* @{term siterate} only creates infinite outputs *}
lemma [simp]: "#(siterate f k) = \<infinity>"

(*-----------------------------*)
sdom
(*-----------------------------*)

text {* A stream and its prefix agree on their first elements *}
lemma snth_less: "\<lbrakk>Fin n < #x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> snth n x = snth n y"

text {* monotonicity of @{term sdom} *}
lemma sdom_mono: "monofun (\<lambda>x. {z. \<exists>n. Fin n < #x \<and> z = snth n x})"

text {* In infinite chains, the length of the streams is unbounded *}
lemma inf_chainl3rf:
  "\<lbrakk>chain Y; \<not>finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>k. Fin n \<le> #(Y k)"

text {* @{term sdom} is a continuous function *}
lemma sdom_cont: "cont (\<lambda>s. {z. \<exists>n. Fin n < #s \<and> z = snth n s})"

text {* @{term sdom} is a continuous function *}
lemma sdom_def2: "sdom\<cdot>s = {z. \<exists>n. Fin n < #s \<and> z = snth n s}"

lemma sdom_cont2: "\<forall>Y. chain Y \<longrightarrow> sdom\<cdot>(\<Squnion> i. Y i) = (\<Squnion> i. sdom\<cdot>(Y i))"


(* the head of any stream is always an element of the domain *)
lemma sdom2un[simp]: "sdom\<cdot>(\<up>z \<bullet> s) = {z} \<union> sdom\<cdot>s"

(* only the empty stream has no elements in its domain *)
lemma strict_sdom_rev: "sdom\<cdot>s = {} \<Longrightarrow> s = \<epsilon>"

(* the infinite repetition of a only has a in its domain *)
lemma [simp]: "sdom\<cdot>(sinftimes (\<up>a)) = {a}"

(* any singleton stream of z only has z in its domain *)
lemma [simp]: "sdom\<cdot>(\<up>z) = {z}"

(* if an element z is in the domain of a stream s, then z is the n'th element of s for some n *)
lemma sdom2snth: "z \<in> sdom\<cdot>s \<Longrightarrow> \<exists>n. snth n s = z"

(* if the natural number n is less than the length of the stream s, then snth n s is in the domain of s *)
lemma snth2sdom: "Fin n < #s \<Longrightarrow> snth n s \<in> sdom\<cdot>s"

(* checking if the domain of a stream x isn't a subset of another set M is an admissible predicate *)
lemma [simp]: "adm (\<lambda>x. \<not> sdom\<cdot>x \<subseteq> M)"

text {* filtering with a superset of the stream's domain does not change the stream *}
lemma sfilter_sdoml3:
  "sdom\<cdot>s \<subseteq> X \<longrightarrow> sfilter X\<cdot>s = s"

text {* filtering with the stream's domain does not change the stream *}
lemma sfilter_sdoml4 [simp]:
  "sfilter (sdom\<cdot>s)\<cdot>s = s"

text {* The domain of a concatenated stream is the union of the single domains *}
lemma sdom_sconc2un:
  "#x = Fin k \<Longrightarrow> sdom\<cdot>(x \<bullet> y) = sdom\<cdot>x \<union> sdom\<cdot>y"

(* if filtering everything except z from the stream x doesn't produce the empty stream, then z must
   be an element of the domain of x *)
lemma sfilter2dom:
  "sfilter {z}\<cdot>x \<noteq> \<epsilon> \<Longrightarrow> z \<in> sdom\<cdot>x"

text {* For injective functions @{term f} with @{term "f(y) = x"}, @{term x} can only
  be contained in @{term "smap f\<cdot>s"} if the original stream contained @{term y} *}
lemma sdom_smapl1: "\<lbrakk>x \<in> sdom\<cdot>(smap f\<cdot>s); inj f; f y = x\<rbrakk> \<Longrightarrow> y \<in> sdom\<cdot>s" 

(*-----------------------------*)
silivespfI
(*-----------------------------*)

lemma sislivespfI:
  "(\<And>x. #(f\<cdot>x) = \<infinity> \<Longrightarrow> #x = \<infinity>) \<Longrightarrow> sislivespf f"

lemma sislivespfI2:
  "(\<And>k. \<forall>x. #x = Fin k \<longrightarrow> #(f\<cdot>x) \<noteq> \<infinity>) \<Longrightarrow> sislivespf f"

lemma sislivespfD1:
  "\<lbrakk>sislivespf f; #x = Fin k\<rbrakk> \<Longrightarrow> #(f\<cdot>x) \<noteq> \<infinity>"

lemma sislivespfD2:
  "\<lbrakk>sislivespf f; #(f\<cdot>x) = \<infinity>\<rbrakk> \<Longrightarrow> #x = \<infinity>"

(*-----------------------------*)
list2s
(*-----------------------------*)

(* consing onto a list is equivalent to prepending an element to a stream *)
lemma [simp]: "list2s (a#as) = \<up>a \<bullet> list2s as"

(* infinite lists don't exist *)
lemma [simp]: "#(list2s x) \<noteq> \<infinity>"

text {* Every finite stream can be converted to a list *}
lemma s2list_ex: 
  "#s = Fin k \<Longrightarrow> \<exists>l. list2s l = s"

(* the empty stream corresponds to the empty list *)
lemma [simp]: "s2list \<epsilon> = []"

(* the singleton stream corresponds to the singleton list *)
lemma [simp]: "s2list (\<up>a) = [a]"

(* the empty list is the bottom element for lists *)
lemma [simp]: "[] \<sqsubseteq> l"

text {* The prefix relation translates from lists to streams *}
lemma list2s_emb: "\<lbrakk>#s \<noteq> \<infinity>; #s' \<noteq> \<infinity>\<rbrakk> \<Longrightarrow> (s2list s \<sqsubseteq> s2list s') = (s \<sqsubseteq> s')"

text {* @{term list2s} is monotone *}
lemma list2s_mono: "l \<sqsubseteq> l' \<Longrightarrow> list2s l \<sqsubseteq> list2s l'"

text {* Prepending a fixed element to a list is a monotone function *}
lemma monofun_lcons: "monofun (\<lambda>l. a # l)"

text {* Head and rest on streams translate to head and rest on lists *}
lemma s2list2lcons: "#s \<noteq> \<infinity> \<Longrightarrow> s2list (\<up>a \<bullet> s) = a # (s2list s)"

text {* @{term s2list} is left-inverse to @{term list2s} *}
lemma [simp]: "s2list (list2s l) = l"

text {* Evaluation of @{term list2s} from right to left *}
lemma slistl5[simp]: "list2s (l @ [m]) = list2s l \<bullet> \<up>m"

(*-----------------------------*)
functions
(*-----------------------------*)
text {* Monotone list-processing functions induce monotone stream-processing functions
  by applying them to the stream's k-element prefix *}
lemma mono_slpf2spf:
  "monofun f \<Longrightarrow> monofun (\<lambda>s. list2s (f (s2list (stake k\<cdot>s))))"

text {* Applying a monotone list-processing function to the @{term k}-element prefix of a stream
  is monotone with respect to @{term k} *}
lemma chain_slpf2spf:
  "monofun f \<Longrightarrow> list2s (f (s2list (stake i\<cdot>x))) \<sqsubseteq> list2s (f (s2list (stake (Suc i)\<cdot>x)))"

text {* Now, a list-processing function is converted to a stream-processing one by building
  the LUB of applying the function to all prefixes of the stream *}
lemma slpf2spfl_contl:
  "monofun f \<Longrightarrow> 
  cont (\<lambda>s. (\<Squnion>k. list2s (f (s2list (stake k\<cdot>s)))))"

text {* The output function of @{term slpf2spf} is continuous *}
lemma slpf2spf_cont:
  "monofun f \<Longrightarrow> 
     (\<Lambda> s. (\<Squnion>k. list2s (f (s2list (stake k\<cdot>s)))))\<cdot>s = (\<Squnion>k. list2s (f (s2list (stake k\<cdot>s))))"

text {* Applying @{term "slpf2spf f"} to an element @{term x} *}
lemma slpf2spf_def2:
  "monofun f \<Longrightarrow> slpf2spf f\<cdot>x = (\<Squnion>k. list2s (f (s2list (stake k\<cdot>x))))"

text {* The output of @{term slpf2spf} is live *}
lemma sislivespf_slpf2spf:
  "monofun f \<Longrightarrow> sislivespf (slpf2spf f)"

text {* Any live stream-processing function can be converted to a monotone
  list-processing function *}
lemma sspf2lpf_mono: 
  "sislivespf f \<Longrightarrow> monofun (sspf2lpf f)"

text {* The result of applying continuous functions to infinite inputs
  does not change on even longer inputs *}
lemma monofun_spf_ubl[simp]:
  "#(f\<cdot>x) = \<infinity> \<Longrightarrow> f\<cdot>(x \<bullet> y) = f\<cdot>x"

text {* Some special results about @{term smap} and injective functions
  on streams of natural successors *}

lemma inj_sfilter_smap_siteratel1:
  "inj f \<Longrightarrow> sfilter {f j}\<cdot>(smap f\<cdot>(siterate Suc (Suc (k + j)))) = \<epsilon>"

(* an element m can't appear infinitely often in a stream produced by mapping an injective function f
   over the natural numbers *)
lemma inj_sfilter_smap_siteratel2[simp]:
  "inj f \<Longrightarrow> #(sfilter {m}\<cdot>(smap f\<cdot>(siterate Suc j))) \<noteq> \<infinity>"

*)



(* TODO : StreamCaseStudy.thy Lemmas


(*smap*)

lemma l5: "smap g\<cdot>\<up>x\<infinity> = \<up>(g x)\<infinity>"
  by simp

(*siterate*)

lemma "sdrop i\<cdot>(siterate id x) = siterate id x"
  by (smt sdrops_sinf siter2sinf)

(*snth *)

lemma siter_snth2[simp]: "snth n (siterate (op + x) a) = a+ (n * x)"
  apply(induction n arbitrary: x)
   apply (simp)
  by (simp add: snth_snth_siter)


lemma [simp]: "#as \<sqsubseteq> #(as \<bullet> ys)"
  by (metis minimal monofun_cfun_arg sconc_snd_empty)

(*slen*)

lemma [simp]: "Fin n < #as \<Longrightarrow> Fin n < lnsuc\<cdot>(#as)"
  by (smt below_antisym below_trans less_lnsuc lnle_def lnless_def)

(*stake*)

lemma stake_suc: "stake (Suc n)\<cdot>s = (stake 1\<cdot>s) \<bullet> stake n\<cdot>(srt\<cdot>s)"
by (metis One_nat_def Suc2plus sdrop_0 sdrop_back_rt stake_add)

(* sfoot *)

lemma sfoot_dom: assumes "#s = Fin (Suc n)" and "sdom\<cdot>s\<subseteq>A"
  shows "sfoot s\<in>A"
by (metis Suc_n_not_le_n assms(1) assms(2) contra_subsetD leI less2nat_lemma sfoot_exists2 snth2sdom)

lemma sfood_id: assumes"#s = Fin (Suc n)"
  shows "(stake n\<cdot>s) \<bullet> \<up>(sfoot s) = s"
  using assms apply(induction n arbitrary: s)
   apply simp
   apply (metis Fin_02bot Fin_Suc lnat.sel_rews(2) lnsuc_neq_0_rev lnzero_def lscons_conv sfoot_exists2 slen_scons snth_shd strict_slen sup'_def surj_scons)
  apply (subst stake_suc)
  apply simp
  by (smt Fin_02bot Fin_Suc One_nat_def Rep_cfun_strict1 Zero_not_Suc leI lnat.sel_rews(2) lnle_Fin_0 lnzero_def notinfI3 sconc_snd_empty sfoot_sdrop slen_rt_ile_eq slen_scons stake_Suc stream.take_0 strict_slen surj_scons)

(*stake*)

lemma stakeind2: 
  "\<forall>x. (P \<epsilon> \<and> (\<forall>a s. P s \<longrightarrow> P (s \<bullet> \<up>a))) \<longrightarrow> P (stake n\<cdot>x)"
  apply(induction n)
   apply simp
  apply auto
  apply (subst stake_suc)
  by (metis (no_types, lifting) sconc_snd_empty sdrop_back_rt sdropostake split_streaml1 stake_suc surj_scons)


lemma ind2: assumes "adm P" and "P \<epsilon>"  and "\<And>a s. P s  \<Longrightarrow> P (s \<bullet> \<up>a)"
  shows "P x"
by (metis assms(1) assms(2) assms(3) stakeind2 stream.take_induct)

(*sfilter*)

lemma sfilterEq2sdom_h: "sfilter A\<cdot>s = s \<longrightarrow> sdom\<cdot>s \<subseteq> A"
  apply(rule ind [of _s])
    apply (smt admI inf.orderI sdom_sfilter)
   apply(simp)
  apply(rule)
  by (smt mem_Collect_eq sdom_def2 sfilterl7 subsetI)

lemma sfilterEq2sdom: "sfilter A\<cdot>s = s \<Longrightarrow> sdom\<cdot>s \<subseteq> A"
  by (simp add: sfilterEq2sdom_h) 


(* Compact Stuff *)

lemma finChainapprox: assumes "chain Y" and "# (\<Squnion>i. Y i) =Fin  k" 
  shows "\<exists>i. Y i = (\<Squnion>i. Y i)"
  using assms(1) assms(2) inf_chainl4 lub_eqI lub_finch2 by fastforce

lemma finCompact: assumes "#s = Fin k"
  shows "compact s"
  proof (rule compactI2)
  fix Y assume as1: "chain Y" and as2: "s \<sqsubseteq> (\<Squnion>i. Y i)"
  show "\<exists>i. s \<sqsubseteq> Y i" by (metis approxl2 as1 as2 assms finChainapprox lub_approx stream.take_below)
qed

lemma "compact \<epsilon>"
  by simp

lemma "compact (\<up>x)"
  by (simp add: sup'_def)

lemma "compact (<[1,2,3,4,5]>)"
  proof (rule finCompact)
  show "#(<[1, 2, 3, 4, 5]>) = Fin 5" by simp
qed


(* nicht so compactes Zeug *)
lemma nCompact: assumes "chain Y" and "\<forall>i. (Y i \<sqsubseteq> x)" and "\<forall>i.  (Y i \<noteq> x)" and "x \<sqsubseteq> (\<Squnion>i. Y i)"
  shows "\<not>(compact x)"
  by (meson assms below_antisym compactD2)

lemma infNCompact: assumes "#s = \<infinity>"
  shows"\<not> (compact s)"
  proof (rule nCompact)
     show "chain (\<lambda>i. stake i\<cdot>s)" by simp
    show "\<forall>i. stake i\<cdot>s \<sqsubseteq> s" by simp
   show "\<forall>i. stake i\<cdot>s \<noteq> s" by (metis Inf'_neq_0 assms fair_sdrop sdropostake strict_slen)
  show "s \<sqsubseteq> (\<Squnion> i. stake i\<cdot>s)" by (simp add: reach_stream)
qed

lemma "\<not> (compact (sinftimes (\<up>x)))"
  by (simp add: infNCompact slen_sinftimes)


(* add function *)

definition add:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"add \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) + (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"

lemma "add = merge plus"
by(simp add: add_def merge_def)

lemma add_unfold: "add\<cdot>(\<up>x \<bullet> xs)\<cdot>(\<up>y\<bullet> ys) = \<up>(x+y) \<bullet> add\<cdot>xs\<cdot>ys"
  by(simp add: add_def)

lemma add_snth: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (add\<cdot>xs\<cdot>ys) = snth n xs + snth n ys"
  apply(induction n arbitrary: xs ys)
   apply (metis Fin_02bot add_unfold lnless_def lnzero_def shd1 slen_empty_eq snth_shd surj_scons)
  by (smt Fin_Suc Fin_leq_Suc_leq Suc_eq_plus1_left add_unfold inject_lnsuc less2eq less2lnleD lnle_conv lnless_def lnsuc_lnle_emb sconc_snd_empty sdropostake shd1 slen_scons snth_rt snth_scons split_streaml1 stream.take_strict surj_scons ub_slen_stake)

lemma add_eps1[simp]: "add\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"
  by(simp add: add_def)

lemma add_eps2[simp]: "add\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: add_def)

lemma [simp]: "srt\<cdot>(add\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet> bs)) = add\<cdot>as\<cdot>bs"
  by (simp add: add_unfold)

lemma add_commu_helper: assumes "\<And>y. add\<cdot>x\<cdot>y = add\<cdot>y\<cdot>x"
  shows "add\<cdot>(\<up>a \<bullet> x)\<cdot>y = add\<cdot>y\<cdot>(\<up>a \<bullet> x)"
  apply(cases "y = \<epsilon>")
   apply auto[1]
  by (metis (no_types, lifting) Groups.add_ac(2) assms add_unfold surj_scons)

lemma add_commutative: "add\<cdot>x\<cdot>y = add\<cdot>y\<cdot>x"
  apply(induction x arbitrary: y)
    apply(simp_all)
  by (metis add_commu_helper stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma add_len: assumes "xs\<noteq>\<bottom>" and "u\<noteq>\<bottom>"
  shows "#(add\<cdot>xs\<cdot>(u && ys)) = lnsuc\<cdot>(#(add\<cdot>(srt\<cdot>xs)\<cdot>ys))"
  by (metis (no_types, lifting) add_unfold assms(1) assms(2) slen_scons stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma add_slen_help [simp]: "#xs \<sqsubseteq> #ys \<Longrightarrow> #(add\<cdot>xs\<cdot>ys) = #xs"
  apply(induction xs arbitrary: ys)
    apply(rule admI)
    apply rule+
    apply (smt ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun lub_below_iff lub_eq)
   apply(simp)
  proof -
  fix u
  fix xs ys :: "nat stream"
  assume as1: "u \<noteq> \<bottom>" and as2: "(\<And>ys. #xs \<sqsubseteq> #ys \<Longrightarrow> #(add\<cdot>xs\<cdot>ys) = #xs)" and as3: " #(u && xs) \<sqsubseteq> #ys"
  obtain a where a_def: "updis a = u" by (metis as1 discr.exhaust upE)
  show "#(add\<cdot>(u && xs)\<cdot>ys) = #(u && xs)"
  proof (cases "ys = \<epsilon>")
   case True thus ?thesis using add_eps2 as3 bot_is_0 bottomI strict_slen by auto
  next
  case False
  hence "#(add\<cdot>xs\<cdot>(srt\<cdot>ys)) = #xs" by (metis a_def as2 as3 lnat.inverts lscons_conv slen_scons surj_scons)
  thus ?thesis by (metis False \<open>updis a = u\<close> add_unfold lscons_conv slen_scons surj_scons)
  qed
qed

lemma add_slen [simp]: "#(add\<cdot>x\<cdot>y) = min (#x) (#y)"
  apply(cases "#x\<le>#y")
   apply (metis add_slen_help lnle_def min.commute min_absorb2)
  by (metis add_commutative add_slen_help linear lnle_def min.absorb2)

lemma add_slen_sinf [simp]: 
  shows " #xs = \<infinity> \<Longrightarrow> #(add\<cdot>xs\<cdot>ys) =(#ys)"
  by (simp add: min.absorb2)

lemma snth_add: "Fin n < #ys \<Longrightarrow> snth n (add\<cdot>\<up>x\<infinity>\<cdot>ys) = snth n (smap (\<lambda>z. z + x)\<cdot>ys)"
  apply(induction n arbitrary: ys)
   apply (smt Fin_02bot add.commute add_unfold lnless_def lnzero_def shd1 sinftimes_unfold slen_empty_eq smap_snth_lemma snth_shd surj_scons)
  by (smt Fin_Suc add_slen_sinf add_unfold lnle_conv lnless_def lnsuc_lnle_emb sinftimes_unfold slen_empty_eq slen_scons slen_sinftimes slen_smap smap_snth_lemma snth_scons strict_icycle surj_scons)

lemma add2smap: "add\<cdot>(\<up>x\<infinity>)\<cdot>ys = smap (\<lambda>z. z+x)\<cdot>ys"
  apply(rule snths_eq)
   apply auto[1]
  by (metis add_slen_sinf lnat.con_rews lnzero_def lscons_conv slen_empty_eq slen_scons slen_sinftimes snth_add sup'_def)


*)

end
