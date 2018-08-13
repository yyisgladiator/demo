(*  Title:        Components.thy
    Author:       Dennis Slotboom, Annika Savelsberg
    E-Mail:       dennis.slotboom@rwth-aachen.de, annika.savelsberg@rwth-aachen.de

    Description:  Theory for ABP Component Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for ABP Component Lemmata on Time-synchronous Streams *}

theory Components
imports "../AutomatonPrelude" "../../../UBundle_Induction"

begin

(* ----------------------------------------------------------------------- *)
  section {* Datatype Conversion *}
(* ----------------------------------------------------------------------- *)

text {* Inverse of a Pair. *}
fun invPair :: "abpMessage \<Rightarrow> (nat \<times> bool)" where
  "invPair (Pair_nat_bool (n,b)) = (n,b)" |
  "invPair n = undefined"

text {* Conversion of a pair (nat,bool) stream into an equivalent receiver stream. *}
definition natbool2abp :: "(nat \<times> bool) tsyn stream \<rightarrow> abpMessage tsyn stream" where
  "natbool2abp \<equiv> tsynMap Pair_nat_bool"

text {* Conversion of a receiver stream into an equivalent pair (nat,bool) stream. *}
definition abp2natbool :: "abpMessage tsyn stream \<rightarrow> (nat \<times> bool) tsyn stream" where
  "abp2natbool \<equiv> tsynMap invPair"

text {* Inverse of a Bool. *}
fun invBool :: "abpMessage \<Rightarrow> bool" where
  "invBool (Bool x) = x" |
  "invBool x = undefined"

text {* Conversion of a bool stream into an equivalent receiver stream. *}
definition bool2abp :: "bool tsyn stream \<rightarrow> abpMessage tsyn stream" where
  "bool2abp \<equiv> tsynMap Bool"

text {* Conversion of a receiver stream into an equivalent bool stream. *}
definition abp2bool :: "abpMessage tsyn stream \<rightarrow> bool tsyn stream" where
  "abp2bool \<equiv> tsynMap invBool"

text {* Inverse of a Nat. *}
fun invNat :: "abpMessage \<Rightarrow> nat" where
  "invNat (Nat x) = x" |
  "invNat x = undefined"

text {* Conversion of a nat stream into an equivalent receiver stream. *}
definition nat2abp :: "nat tsyn stream \<rightarrow> abpMessage tsyn stream" where
  "nat2abp \<equiv> tsynMap Nat"

text {* Conversion of a receiver stream into an equivalent nat stream. *}
definition abp2nat :: "abpMessage tsyn stream \<rightarrow> nat tsyn stream" where
  "abp2nat \<equiv> tsynMap invNat"

(* ----------------------------------------------------------------------- *)
  section {* Datatype Conversion Lemmata *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions and move to tsynStream. *)

lemma tsynmap_tsynmap: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (\<lambda> x. f (g x))\<cdot>s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_null)

lemma tsynmap_id: "tsynMap (\<lambda>x. x)\<cdot>s = s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_null)

(* ToDo: add descriptions and inverse lemmata. *)

lemma pair_invpair_inv: "invPair (Pair_nat_bool m) = m"
  by (metis invPair.simps(1) surj_pair)

lemma natbool2abp_abp2natbool_inv: "abp2natbool\<cdot>(natbool2abp\<cdot>s) = s"
  by (simp add: abp2natbool_def natbool2abp_def tsynmap_tsynmap pair_invpair_inv tsynmap_id)

lemma nat2abp_abp2nat_inv: "abp2nat\<cdot>(nat2abp\<cdot>s) = s"
  by (simp add: abp2nat_def nat2abp_def tsynmap_tsynmap tsynmap_id)

lemma bool2abp_abp2bool_inv: "abp2bool\<cdot>(bool2abp\<cdot>s) = s"
  by (simp add: abp2bool_def bool2abp_def tsynmap_tsynmap tsynmap_id)

(* ToDo: add descriptions and move to Streams. *)

lemma len_one_stream: "#s = Fin 1 \<Longrightarrow> \<exists>m. s = \<up>m"
  proof -
    assume a0: "#s = Fin 1"
    show "\<exists>m::'a. s = \<up>m"
      proof -
        have empty_or_long: "\<nexists>m::'a. s = \<up>m \<Longrightarrow> s = \<epsilon> \<or> (\<exists> as a. s = \<up>a \<bullet> as)"
          by (metis surj_scons)
        have not_eq_one: "\<nexists>m::'a. s = \<up>m \<Longrightarrow> #s = Fin 0 \<or> #s > Fin 1" 
          using empty_or_long 
          by (metis Fin_02bot Fin_Suc One_nat_def a0 leI lnzero_def notinfI3 only_empty_has_length_0 
              sconc_snd_empty slen_conc slen_scons)
        have not_eq_one2: "\<exists>m. s = \<up>m" using a0 
          using not_eq_one by auto
        show ?thesis 
          using not_eq_one2 by simp
      qed
  qed

(* ToDo: move to tsynBundle. *)

text {* Cases rule for simple time-synchronous bundles. *}
lemma tsynb_cases [case_names max_len not_ubleast numb_channel msg null]:
  assumes max_len: "ubMaxLen (Fin (1 :: nat)) x"
    and not_ubleast: "x \<noteq> ubLeast (ubDom\<cdot>x)"
    and numb_channel: "(ubDom\<cdot>x) = {c}"
    and msg: "\<And>m. (Msg m) \<in> ctype c \<Longrightarrow> P (createBundle (Msg m) c)"
    and null: "P (tsynbNull c)"
  shows "P x"
  proof -
    have x_not_empty: "x . c \<noteq> \<epsilon>" 
       by (metis not_ubleast numb_channel singletonD ubDom_ubLeast ubgetchI ubleast_ubgetch) 
    have x_dom_eq_createbundle: "\<And>m. ubDom\<cdot>x = ubDom\<cdot>(createBundle (Msg m) c)" 
      by (simp add: numb_channel)
    have x_dom_eq_tsynbnull: "ubDom\<cdot>x = ubDom\<cdot>(tsynbNull c)"
      by (simp add: numb_channel)
    have createbundle_stream_eq: 
      "\<And>m. (Msg m) \<in> ctype c \<Longrightarrow> (createBundle (Msg m) c) . c = \<up>(Msg m)"
      by (metis createBundle.rep_eq fun_upd_same option.sel ubgetch_insert)
    have tsynbnull_stream_eq: "(tsynbNull c) . c =  \<up>null"
      by simp
    have x_singleton: "usclLen\<cdot>(x . c) = Fin 1"
      proof - 
        have x_smaller: "usclLen\<cdot>(x . c) \<le> Fin 1" 
          using max_len by (simp add: numb_channel ubMaxLen_def)
        have empty_zero: "usclLen\<cdot>(\<epsilon> :: 'a tsyn stream) = Fin 0" 
          by (simp add: usclLen_stream_def)
        hence x_not_zero: "usclLen\<cdot>(x . c) \<noteq> Fin 0" 
          using x_not_empty by (simp add: usclLen_stream_def)
        thus ?thesis
          using x_smaller by (simp add: antisym_conv neq02Suclnle)
      qed
    obtain s where s_def: "x . c = s" 
      using assms by metis
    have s_ubundle_eq_x: "x = Abs_ubundle ([c \<mapsto> s])"
      by (metis (mono_tags, lifting) dom_eq_singleton_conv fun_upd_same numb_channel s_def 
          singletonI ubWell_single_channel ubdom_insert ubgetchE ubgetchI ubgetch_insert 
          ubrep_ubabs)
    have len_one_cases: "usclLen\<cdot>s = Fin 1 \<Longrightarrow> (\<exists>m. s = (\<up>(Msg m))) \<or>  (s = (\<up>null))"
      using tsyn.exhaust One_nat_def len_one_stream usclLen_stream_def by metis
    have s_cases: "(\<exists>m. s = \<up>(Msg m)) \<or> (s = \<up>null)"
      using s_def assms x_singleton x_not_empty len_one_cases by blast
    have s_eq: "(\<exists>m. s = (createBundle (Msg m) c) . c ) \<or> (s = (tsynbNull c) . c)"
      proof (case_tac "\<exists>m. s = \<up>(Msg m)")
        show "\<exists>m::'a. s = \<up>(\<M> m) 
                \<Longrightarrow> (\<exists>m :: 'a. s = createBundle (\<M> m) c  .  c) \<or> s = tsynbNull c  .  c"
          by (metis contra_subsetD createbundle_stream_eq insertI1 insert_is_Un lscons_conv 
              numb_channel s_def sdom2un sup'_def ubdom_channel_usokay ubgetch_insert 
              usclOkay_stream_def)
        show "\<nexists>m::'a. s = \<up>(\<M> m) 
                \<Longrightarrow> (\<exists>m::'a. s = createBundle (\<M> m) c  .  c) \<or> s = tsynbNull c  .  c" 
          using s_cases by simp
      qed
    have x_eq: "(\<exists>m. x = (createBundle (Msg m) c)) \<or> (x = (tsynbNull c))" 
      using s_cases s_def assms s_eq 
      by (metis singletonD ubgetchI x_dom_eq_createbundle x_dom_eq_tsynbnull)
    show ?thesis using x_eq msg null
      by (metis createBundle.rep_eq fun_upd_same option.sel ubgetch_insert x_not_empty)
  qed

text {* Cases rule for simple time-synchronous bundles with two non-empty channels. *}
lemma tsynb_cases_ext [case_names max_len_2c not_ubleast_2c two_channel msg_msg null_msg msg_null null_null]:
  assumes max_len_2c: "ubMaxLen (Fin (1::nat)) x" 
    and not_ubleast_2c: "\<And>c. c\<in>ubDom\<cdot>x \<Longrightarrow> x . c \<noteq> ubLeast (ubDom\<cdot>x) . c" 
    and two_channel: "(ubDom\<cdot>x) = {c,cc}"
    and msg_msg: "\<And>m1 m2. (Msg m1) \<in> ctype c \<Longrightarrow> (Msg m2) \<in> ctype cc \<Longrightarrow> 
                           P ((createBundle (Msg m1) c) \<uplus> (createBundle (Msg m2) cc))"
    and null_msg: "\<And>m2. (Msg m2) \<in> ctype cc \<Longrightarrow> P ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
    and msg_null: "\<And>m2. (Msg m2) \<in> ctype c \<Longrightarrow> P ((createBundle (Msg m2) c) \<uplus> (tsynbNull cc))"
    and null_null: "P ((tsynbNull c) \<uplus> (tsynbNull cc))"
  shows "P x"
proof- 
  have x_c_not_empty: "x . c \<noteq> \<epsilon>"
    using not_ubleast_2c by (simp add: two_channel)
  have x_cc_not_empty: "x . cc \<noteq> \<epsilon>" 
    using not_ubleast_2c by (simp add: two_channel)
  have x_c_singleton: "usclLen\<cdot>(x . c) = Fin 1" 
    proof - 
      have x_smaller: "usclLen\<cdot>(x . c) \<le> Fin 1" using max_len_2c
        by (simp add: two_channel ubMaxLen_def)
      have empty_zero: "usclLen\<cdot>(\<epsilon>::'a tsyn stream) = Fin 0" 
        by (simp add: usclLen_stream_def)
      hence x_not_zero: "usclLen\<cdot>(x . c) \<noteq> Fin 0" using x_c_not_empty
        by (simp add: usclLen_stream_def)
      thus ?thesis using x_smaller
        by (simp add: One_nat_def antisym_conv neq02Suclnle)
    qed
  have x_cc_singleton: "usclLen\<cdot>(x . cc) = Fin 1" 
    proof - 
      have x_smaller: "usclLen\<cdot>(x . cc) \<le> Fin 1" using max_len_2c
        by (simp add: two_channel ubMaxLen_def)
      have empty_zero: "usclLen\<cdot>(\<epsilon>::'a tsyn stream) = Fin 0" 
        by (simp add: usclLen_stream_def)
      hence x_not_zero: "usclLen\<cdot>(x . cc) \<noteq> Fin 0" using x_cc_not_empty
        by (simp add: usclLen_stream_def)
      thus ?thesis using x_smaller
        by (simp add: One_nat_def antisym_conv neq02Suclnle)
    qed
  have x_dom_eq_msg_msg: "\<And>m1 m2. ubDom\<cdot>x = ubDom\<cdot>((createBundle (Msg m1) c) \<uplus> (createBundle (Msg m2) cc))"
    by (metis createBundle_dom insert_is_Un two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have x_dom_eq_null_msg: "\<And>m2. ubDom\<cdot>x = ubDom\<cdot> ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
    by (metis createBundle_dom insert_is_Un tsynbnull_ubdom two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have x_dom_eq_msg_null: "\<And>m2. ubDom\<cdot>x = ubDom\<cdot> ((createBundle (Msg m2) c)  \<uplus> (tsynbNull cc))"
    by (metis createBundle_dom insert_is_Un tsynbnull_ubdom two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have x_dom_eq_null_null: "ubDom\<cdot>x = ubDom\<cdot> ((tsynbNull c)  \<uplus> (tsynbNull cc))"
    by (metis insert_is_Un tsynbnull_ubdom two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  obtain s1 where s1_def: "x . c = s1" using assms
   by metis
  obtain s2 where s2_def: "x . cc = s2" using assms
    by metis
  have s1_ubundle_eq_x: "x = Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])"
    proof- 
      have dom_eq: "ubDom\<cdot>x = ubDom\<cdot>(Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2]))"
        by (metis (mono_tags, lifting) dom_empty dom_fun_upd insertI1 insert_commute option.discI 
           s1_def s2_def two_channel ubWell_single_channel ubdom_channel_usokay ubdom_insert 
           ubgetch_insert ubrep_ubabs ubsetch_well)
      hence "\<And>ccc. ccc\<in>ubDom\<cdot>x \<Longrightarrow> x . ccc = (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . ccc"
        proof- 
          have f1: "x . cc = (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . cc" 
            by (metis (mono_tags, lifting) fun_upd_same insertI1 insert_commute s1_def s2_def two_channel 
               ubWell_single_channel ubdom_channel_usokay ubgetchE ubgetch_insert ubrep_ubabs ubsetch_well)
          have f0: "(Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . c = s1" 
            by (metis fun_upd_same fun_upd_twist insert_iff s1_def s2_def two_channel ubWell_single_channel 
               ubdom_channel_usokay ubgetchE ubgetch_insert ubrep_ubabs ubsetch_well)
          have f2: "x . c = (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . c"
            using f1 f0 
            by (simp add: s1_def) 
          show "\<And>ccc::channel. ccc \<in> ubDom\<cdot>x \<Longrightarrow> ubDom\<cdot>x = ubDom\<cdot>(Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2]) \<Longrightarrow> 
                               x . ccc = Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2] . ccc"
            using f1 f2 two_channel by fastforce
        qed
      thus ?thesis using ubgetchI dom_eq by blast
    qed
  have len_one_cases_c: "usclLen\<cdot>s1 = Fin 1 \<Longrightarrow> (\<exists>m. s1 = (\<up>(Msg m))) \<or>  (s1 = (\<up>null))" 
    using One_nat_def len_one_stream tsyn.exhaust usclLen_stream_def by metis 
  have len_one_cases_cc: "usclLen\<cdot>s2 = Fin 1 \<Longrightarrow> (\<exists>m. s2 = (\<up>(Msg m))) \<or>  (s2 = (\<up>null))" 
    using One_nat_def len_one_stream tsyn.exhaust usclLen_stream_def by metis 
  have s1_cases: "(\<exists>m. s1 = \<up>(Msg m)) \<or> (s1 = \<up>null)"
    using s1_def assms x_c_singleton x_c_not_empty len_one_cases_c by blast
  have s2_cases: "(\<exists>m. s2 = \<up>(Msg m)) \<or> (s2 = \<up>null)"
    using s2_def assms x_cc_singleton x_cc_not_empty len_one_cases_cc by blast
  have s1_eq: "(\<exists>m. s1 = (createBundle (Msg m) c) . c ) \<or> (s1 = (tsynbNull c) . c)" 
    proof(case_tac "\<exists>m. s1 = \<up>(Msg m)")
      show "\<exists>m::'a. s1 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s1 = createBundle (\<M> m) c  .  c) \<or> s1 = tsynbNull c . c"
        by (metis contra_subsetD createBundle.rep_eq fun_upd_same insertI1 insert_is_Un lscons_conv 
           option.sel s1_def sdom2un sup'_def two_channel ubdom_channel_usokay ubgetch_insert 
           usclOkay_stream_def)
      show "\<nexists>m::'a. s1 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s1 = createBundle (\<M> m) c  .  c) \<or> s1 = tsynbNull c . c" 
        using s1_cases by auto
    qed
  have s2_eq: "(\<exists>m. s2 = (createBundle (Msg m) cc) . cc ) \<or> (s2 = (tsynbNull cc) . cc)" 
    proof(case_tac "\<exists>m. s2 = \<up>(Msg m)")
      show "\<exists>m::'a. s2 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s2 = createBundle (\<M> m) cc  .  cc) \<or> s2 = tsynbNull cc . cc"
        by (metis contra_subsetD createBundle.rep_eq fun_upd_same insertI1 insert_is_Un lscons_conv 
           option.sel s2_def sdom2un sup'_def two_channel ubdom_channel_usokay ubgetch_insert 
           usclOkay_stream_def insert_commute)
      show "\<nexists>m::'a. s2 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s2 = createBundle (\<M> m) cc  .  cc) \<or> s2 = tsynbNull cc . cc" 
        using s2_cases by auto
    qed
  have x_cases: "(\<exists>m1 m2. x = Abs_ubundle ([c \<mapsto> \<up>(Msg m1), cc \<mapsto> \<up>(Msg m2)])) \<or> 
                 (\<exists>m1. x = Abs_ubundle ([c \<mapsto> \<up>(Msg m1), cc \<mapsto> \<up>-])) \<or> 
                 (\<exists>m2. x = Abs_ubundle ([c \<mapsto> \<up>-, cc \<mapsto> \<up>(Msg m2)])) \<or>
                 (x = Abs_ubundle ([c \<mapsto> \<up>-, cc \<mapsto> \<up>-]))" 
    using s1_eq s2_eq s1_cases s2_cases s1_def s2_def s1_ubundle_eq_x by metis
  have x_case_msg_msg: "\<exists>m1. s1 = \<up>(Msg m1) \<Longrightarrow> \<exists>m2.  s2 = \<up>(Msg m2) \<Longrightarrow> 
                        \<exists>m1 m2. x =  ((createBundle (Msg m1) c) \<uplus> (createBundle (Msg m2) cc))"
    proof -
      assume a0:  "\<exists>m1::'a. s1 = \<up>(\<M> m1)"
      assume a1:  "\<exists>m2::'a. s2 = \<up>(\<M> m2)"
      show "\<exists>(m1::'a) m2::'a. x = createBundle (\<M> m1) c \<uplus> createBundle (\<M> m2) cc"
        proof - 
          obtain m1 where m1_def: "s1 = \<up>(\<M> m1)" using a0 by blast
          obtain m2 where m2_def: "s2 = \<up>(\<M> m2)" using  a1
             by blast
          have m1_shd: "(\<M> m1) = shd (x . c)" using m1_def s1_def 
             by auto
          have m1_ctype: "(Msg m1) \<in> ctype c"
            by (metis createBundle.rep_eq createBundle_dom fun_upd_same m1_def option.sel s1_def 
               s1_eq shd1 singletonI tsyn.distinct(1) tsynbnull_ubgetch ubgetchE x_c_not_empty)
          have m2_shd: "(\<M> m2) = shd (x . cc)" using m2_def s2_def 
             by auto
          have m2_ctype: "(Msg m2) \<in> ctype cc"
            by (metis createBundle.rep_eq createBundle_dom fun_upd_same m2_def option.sel s2_def 
               s2_eq shd1 singletonI tsyn.distinct(1) tsynbnull_ubgetch ubgetchE x_cc_not_empty)
          have create_c: "(createBundle (\<M> m1) c) . c = \<up>(Msg m1)"
            by (metis createBundle.rep_eq fun_upd_same m1_ctype option.sel ubgetch_insert)
          have create_cc: "(createBundle (\<M> m2) cc) . cc = \<up>(Msg m2)"
            by (metis createBundle.rep_eq fun_upd_same m2_ctype option.sel ubgetch_insert)
          have domc: "c\<in>ubDom\<cdot>(createBundle (\<M> m1) c)"
            by simp       
          have domcc: "cc\<in>ubDom\<cdot>(createBundle (\<M> m2) cc)"
            by simp
          have create_eq_c: "(createBundle (\<M> m1) c) . c = s1"
            using create_c m1_def by blast
          have create_eq_cc: "(createBundle (\<M> m2) cc) . cc = s2"
            using create_cc m2_def by blast
          have ubunion_create_eq_c: "((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)) . c = \<up>(Msg m1)"
            by (metis createBundle_dom create_c create_cc m1_def m2_def  ubunion_getchL s1_def s2_def 
               singletonD ubclUnion_ubundle_def ubunion_getchR)
          have ubunion_create_eq_cc: "((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)) . cc = \<up>(Msg m2)"
             using ubunion_getchR by (simp add: create_cc ubclUnion_ubundle_def)
          thus ?thesis 
            by (metis (no_types, lifting) ubunion_create_eq_c insert_iff m1_def m2_def s1_def s2_def 
               singletonD two_channel ubgetchI x_dom_eq_msg_msg)
        qed
     qed
  have x_case_msg_null: "\<exists>m1. s1 = \<up>(Msg m1) \<Longrightarrow> s2 = \<up>- \<Longrightarrow> 
                          \<exists>m1 . x =  ((createBundle (Msg m1) c) \<uplus> (tsynbNull cc))"
    proof -
       assume a0:  "\<exists>m1::'a. s1 = \<up>(\<M> m1)"
       assume a1:  "s2 = \<up>-"
       show "\<exists>m1::'a. x = createBundle (\<M> m1) c \<uplus> tsynbNull cc"
         proof - 
           obtain m1 where m1_def: "s1 = \<up>(\<M> m1)" using a0 by blast
           have m1_shd: "(\<M> m1) = shd (x . c)" using m1_def s1_def 
             by auto
           have m1_ctype: "(Msg m1) \<in> ctype c"
             by (metis createBundle.rep_eq createBundle_dom fun_upd_same m1_def option.sel s1_def 
                s1_eq shd1 singletonI tsyn.distinct(1) tsynbnull_ubgetch ubgetchE x_c_not_empty)
           have create_c: "(createBundle (\<M> m1) c) . c = \<up>(Msg m1)"
              by (metis createBundle.rep_eq fun_upd_same m1_ctype option.sel ubgetch_insert)
           have create_cc: "(tsynbNull cc) . cc = \<up>-"
             by simp
           have domc: "c\<in>ubDom\<cdot>(createBundle (\<M> m1) c)"
              by simp       
           have domcc: "cc\<in>ubDom\<cdot>(tsynbNull cc)"
              by simp
           have create_eq_c: "(createBundle (\<M> m1) c) . c = s1"
             using create_c m1_def by blast
           have create_eq_cc: "(tsynbNull cc) . cc = s2"
             using create_cc a1 by blast
           have ubunion_create_eq_c: "((createBundle (\<M> m1) c) \<uplus> ((tsynbNull cc))) . c = \<up>(Msg m1)"
             by (metis create_eq_cc tsynbnull_ubdom ubunion_getchL  create_c  m1_def  s1_def s2_def 
                singletonD ubclUnion_ubundle_def ubunion_getchR )
           have ubunion_create_eq_cc: "((createBundle (\<M> m1) c) \<uplus> ((tsynbNull cc))) . cc = \<up>-"
             by (simp add: ubclUnion_ubundle_def)
           thus ?thesis 
             by (metis (no_types, lifting) create_cc create_eq_cc insert_iff m1_def s1_def s2_def 
                singletonD two_channel ubgetchI ubunion_create_eq_c x_dom_eq_msg_null)  
          qed
      qed
  have x_case_null_msg:  "s1 = \<up>- \<Longrightarrow> \<exists>m2.  s2 = \<up>(Msg m2) \<Longrightarrow> 
                          \<exists>m2. x =  ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
    proof -
     assume a0:  "s1 = \<up>-"
     assume a1:  "\<exists>m2::'a. s2 = \<up>(\<M> m2)"
     show "\<exists>m2::'a. x = tsynbNull c \<uplus> createBundle (\<M> m2) cc"
       proof - 
         obtain m2 where m2_def: "s2 = \<up>(\<M> m2)" using a1 by blast
         have m2_shd: "(\<M> m2) = shd (x . cc)" using m2_def s2_def 
           by auto
         have m2_ctype: "(\<M> m2) \<in> ctype cc"
           by (metis createBundle.rep_eq createBundle_dom fun_upd_same m2_def option.sel s2_def 
              s2_eq shd1 singletonI tsyn.distinct(1) tsynbnull_ubgetch ubgetchE x_cc_not_empty)
         have create_c: "(tsynbNull c) . c = \<up>-"
           by simp
         have create_cc: "(createBundle (\<M> m2) cc) . cc = \<up>(\<M> m2)"
           by (metis createBundle.rep_eq fun_upd_same m2_ctype option.sel ubgetch_insert)
         have domc: "c\<in>ubDom\<cdot>(tsynbNull c)"
            by simp       
         have domcc: "cc\<in>ubDom\<cdot>(createBundle (\<M> m2) cc)"
            by simp
         have create_eq_c: "(tsynbNull c) . c = s1"
           by (simp add: a0)
         have create_eq_cc: "(createBundle (\<M> m2) cc) . cc = s2"
           using a1 by (metis createBundle.rep_eq fun_upd_same m2_ctype m2_def option.sel ubgetch_insert)
         have ubunion_create_eq_c: "((tsynbNull c) \<uplus> ((createBundle (\<M> m2) cc))) . c = \<up>-"
           by (metis a0 createBundle_dom create_c inject_scons insert_absorb insert_iff insert_not_empty 
               m2_def s1_def s2_def tsyn.distinct(1) ubclUnion_ubundle_def ubunion_getchL)
         have ubunion_create_eq_cc: "((tsynbNull c) \<uplus> ((createBundle (\<M> m2) cc))) . cc = \<up>(\<M> m2)"
           by (simp add: create_eq_cc m2_def ubclUnion_ubundle_def)
         show ?thesis 
           by (metis (no_types, lifting) create_c  create_eq_c insert_iff m2_def s1_def s2_def 
               singletonD two_channel ubgetchI ubunion_create_eq_c ubunion_create_eq_cc x_dom_eq_null_msg)
        qed
     qed
  have x_case_null_null: "s1 = \<up>-  \<Longrightarrow>  s2 = \<up>- \<Longrightarrow> x =  ((tsynbNull c) \<uplus> (tsynbNull cc))"
    proof -
     assume a0:  "s1 = \<up>-"
     assume a1:  "s2 = \<up>-"
     show "s1 = \<up>- \<Longrightarrow> s2 = \<up>- \<Longrightarrow> x = tsynbNull c \<uplus> tsynbNull cc"
       proof - 
         have create_c: "(tsynbNull c) . c = \<up>-"
           by simp
         have create_cc: "(tsynbNull cc) . cc = \<up>-"
           by simp
         have domc: "c\<in>ubDom\<cdot>(tsynbNull c)"
            by simp       
         have domcc: "cc\<in>ubDom\<cdot>(tsynbNull cc)"
            by simp       
         have create_eq_c: "(tsynbNull c) . c = s1"
           by (simp add: a0)
         have create_eq_cc: "(tsynbNull cc) . cc = s2"
           by (simp add: a1)
         have ubunion_create_eq_c: "((tsynbNull c) \<uplus> (tsynbNull cc)) . c = \<up>-"
           by (metis create_c singletonD tsynbnull_ubdom ubclUnion_ubundle_def ubunion_getchL ubunion_getchR)
         have ubunion_create_eq_cc: "((tsynbNull c) \<uplus> (tsynbNull cc)) . cc = \<up>-"
           by (simp add: ubclUnion_ubundle_def)
         show ?thesis   
           by (metis (no_types, lifting) create_c create_cc create_eq_cc create_eq_c insert_iff s1_def s2_def 
               singletonD two_channel ubgetchI ubunion_create_eq_c ubunion_create_eq_cc x_dom_eq_null_null)
       qed
    qed
  have px: "P (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2]))"
    proof(case_tac "\<exists>m1. s1 = \<up>(\<M> m1)")
      show "\<exists>m1. s1 = \<up>(\<M> m1) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
        proof(case_tac "\<exists>m2. s2 = \<up>(\<M> m2)")
          show "\<exists>m1. s1 = \<up>(\<M> m1) \<Longrightarrow> \<exists>m2. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])" 
            proof- 
              assume a0: "\<exists>m1. s1 = \<up>(\<M> m1)"
              assume a1: " \<exists>m2. s2 = \<up>(\<M> m2)" 
              show " P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
                proof -
                  obtain m1 where m1_def: "s1 = \<up>( \<M> m1)" using a0 by blast
                  obtain m2 where m2_def: "s2 = \<up>(\<M> m2)" using a1 by blast
                  have f1: "P (((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)))"
                    by (metis createBundle.rep_eq fun_upd_same inject_scons m1_def m2_def msg_msg 
                       option.sel s1_def s1_eq s2_def s2_eq tsyn.distinct(1) tsynbnull_ubgetch 
                       ubgetch_insert x_c_not_empty x_cc_not_empty)
                  have f2: "x = ((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc))"
                    proof- 
                      have m1_shd: "(\<M> m1) = shd (x . c)" 
                        using m1_def s1_def by auto
                      have m1_ctype: "(Msg m1) \<in> ctype c"
                        by (metis createBundle.rep_eq createBundle_dom fun_upd_same m1_def option.sel 
                            s1_def s1_eq shd1 singletonI tsyn.distinct(1) tsynbnull_ubgetch ubgetchE 
                            x_c_not_empty)
                      have m2_shd: "(\<M> m2) = shd (x . cc)" using m2_def s2_def 
                        by auto
                      have m2_ctype: "(Msg m2) \<in> ctype cc"
                        by (metis createBundle.rep_eq createBundle_dom fun_upd_same m2_def option.sel 
                            s2_def s2_eq shd1 singletonI tsyn.distinct(1) tsynbnull_ubgetch ubgetchE 
                            x_cc_not_empty)
                      have create_c: "(createBundle (\<M> m1) c) . c = \<up>(Msg m1)"
                        by (metis createBundle.rep_eq fun_upd_same m1_ctype option.sel ubgetch_insert)
                      have create_cc: "(createBundle (\<M> m2) cc) . cc = \<up>(Msg m2)"
                        by (metis createBundle.rep_eq fun_upd_same m2_ctype option.sel ubgetch_insert)
                      have domc: "c\<in>ubDom\<cdot>(createBundle (\<M> m1) c)"
                        by simp       
                      have domcc: "cc\<in>ubDom\<cdot>(createBundle (\<M> m2) cc)"
                        by simp
                      have create_eq_c: "(createBundle (\<M> m1) c) . c = s1"
                        using create_c m1_def by blast
                      have create_eq_cc: "(createBundle (\<M> m2) cc) . cc = s2"
                        using create_cc m2_def by blast
                      have ubunion_create_eq_c: "((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)) . c = 
                                                 \<up>(Msg m1)"
                        by (metis createBundle_dom create_c create_cc m1_def m2_def s1_def s2_def 
                            singletonD ubclUnion_ubundle_def ubunion_getchR ubunion_getchL)
                      have ubunion_create_eq_cc: "((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)) . cc =
                                                  \<up>(Msg m2)"
                        using ubunion_getchR by (simp add: create_cc ubclUnion_ubundle_def)
                      have dom3: "ubDom\<cdot>x = ubDom\<cdot>(((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)))" 
                        by (simp add: x_dom_eq_msg_msg)
                      have "\<And>ccc. ccc\<in>(ubDom\<cdot>x) \<Longrightarrow> 
                            x . ccc = ((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)) . ccc"
                        using m1_def m2_def s1_def s2_def two_channel ubunion_create_eq_c 
                        ubunion_create_eq_cc by auto
                      thus ?thesis using m1_def m2_def dom3 ubgetchI 
                        by blast
                    qed
                thus ?thesis
                  using f1 s1_ubundle_eq_x by auto
              qed
           qed
           show "\<exists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> \<nexists>m2::'a. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])" 
             by (metis createBundle.rep_eq fun_upd_same msg_null option.sel s1_def s1_ubundle_eq_x 
                 s2_cases s2_def singletonD tsynbnull_ubdom ubclUnion_ubundle_def ubgetch_insert 
                 ubunion_getchL x_c_not_empty x_case_msg_null)
        qed
        show "\<nexists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
          proof(case_tac "\<exists>m2. s2 = \<up>(Msg m2)")
            show "\<nexists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> \<exists>m2::'a. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
              by (metis (mono_tags, lifting) createBundle.rep_eq createBundle_dom insertI1 
                  map_upd_Some_unfold null_msg s1_cases s1_ubundle_eq_x ubclUnion_ubundle_def 
                  ubgetchE ubunion_getchR x_case_null_msg x_cc_not_empty)
            show " \<nexists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> \<nexists>m2::'a. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
              using null_null s1_cases s1_ubundle_eq_x s2_cases x_case_null_null by auto
          qed
        qed
  show ?thesis
    by (simp add: px s1_ubundle_eq_x)
qed

end