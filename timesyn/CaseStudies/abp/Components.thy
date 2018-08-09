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

end