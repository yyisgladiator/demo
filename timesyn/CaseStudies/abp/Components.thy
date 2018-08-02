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

(* should probably be stated in Streams.thy *)
lemma len_one_stream: "#s = Fin 1 \<Longrightarrow> \<exists>m. s = \<up>m"
proof-
  assume a0: "#s = Fin 1"
  show "\<exists>m::'a. s = \<up>m"
  proof-
    have empty_or_long: "\<nexists>m::'a. s = \<up>m \<Longrightarrow> s = \<epsilon> \<or> (\<exists> as a. s = \<up>a \<bullet> as)"
      by (metis surj_scons)
    have not_eq_one: "\<nexists>m::'a. s = \<up>m \<Longrightarrow> #s = Fin 0 \<or> #s > Fin 1" 
      using empty_or_long 
      by (metis Fin_02bot Fin_Suc One_nat_def a0 leI lnzero_def notinfI3 only_empty_has_length_0 sconc_snd_empty slen_conc slen_scons)
    have not_eq_one2: "\<exists>m. s = \<up>m" using a0 
      using not_eq_one by auto
    show ?thesis using not_eq_one2 
      by simp
  qed
qed

text {* Cases rule for simple time-synchronous bundles. *}
lemma tsynb_cases [case_names max_len not_ubleast numb_channel msg null]:
  assumes max_len: "ubMaxLen (Fin (1::nat)) x" 
    and not_ubleast: "x \<noteq> ubLeast (ubDom\<cdot>x)"
    and numb_channel: "(ubDom\<cdot>x) = {c}"
    and msg: "\<And>m. P (createBundle (Msg m) c)"
    and null: "P (tsynbNull c)"
  shows "P x"
proof - 
  have x_not_empty: "x . c \<noteq> \<epsilon>" 
     by (metis not_ubleast numb_channel singletonD ubDom_ubLeast ubgetchI ubleast_ubgetch) 
  have x_dom_eq_createbundle: "\<And>m. ubDom\<cdot>x = ubDom\<cdot>(createBundle (Msg m) c)" 
    by (simp add: numb_channel)
  have x_dom_eq_tsynbnull: "ubDom\<cdot>x = ubDom\<cdot>(tsynbNull c)" 
    by (simp add: numb_channel)
  have createbundle_stream_eq: "\<And>m.  (Msg m) \<in> ctype c \<Longrightarrow> (createBundle (Msg m) c) . c = \<up>(Msg m)" 
    by (metis createBundle.rep_eq fun_upd_same option.sel ubgetch_insert) 
  have tsynbnull_stream_eq: "(tsynbNull c) . c =  \<up>null"
    by simp
  have x_singleton: "usclLen\<cdot>(x . c) = Fin 1" 
  proof - 
    have x_smaller: "usclLen\<cdot>(x . c) \<le> Fin 1" using max_len 
      by (simp add: numb_channel ubMaxLen_def)
    have empty_zero: "usclLen\<cdot>(\<epsilon>::'a tsyn stream) = Fin 0" 
      by (simp add: usclLen_stream_def)
    hence x_not_zero: "usclLen\<cdot>(x . c) \<noteq> Fin 0" using x_not_empty
      by (simp add: usclLen_stream_def)
    thus ?thesis using x_smaller
      by (simp add: One_nat_def antisym_conv neq02Suclnle)
  qed
  obtain s where s_def: "x . c = s" using assms 
    by metis
  have s_ubundle_eq_x: "x = Abs_ubundle ([c \<mapsto> s])"
    by (metis (mono_tags, lifting) dom_eq_singleton_conv fun_upd_same numb_channel s_def singletonI ubWell_single_channel ubdom_insert ubgetchE ubgetchI ubgetch_insert ubrep_ubabs)
  have len_one_cases: "usclLen\<cdot>s = Fin 1 \<Longrightarrow> (\<exists>m. s = (\<up>(Msg m))) \<or>  (s = (\<up>null))" apply (simp add: usclLen_stream_def)
  proof - 
    assume len_one: "#s = Fin (Suc (0::nat))"
    show "(\<exists>m. s = (\<up>(Msg m))) \<or>  (s = (\<up>null))"
    proof - 
      show ?thesis using tsyn.exhaust len_one len_one_stream
        by (metis One_nat_def)
    qed
  qed
  have s_cases: "(\<exists>m. s = \<up>(Msg m)) \<or> (s = \<up>null)"
    using s_def assms x_singleton x_not_empty len_one_cases by blast
  have s_eq: "(\<exists>m. s = (createBundle (Msg m) c) . c ) \<or> (s = (tsynbNull c) . c)" 
    apply (case_tac "\<exists>m. s = \<up>(Msg m)")
     defer 
    using s_cases apply auto[1]
  proof - 
    assume a0: " \<exists>m::'a. s = \<up>(\<M> m)"
    show " (\<exists>m::'a. s = createBundle (\<M> m) c  .  c) \<or> s = tsynbNull c  .  c"
    proof - 
      obtain m where m_def: "s = \<up>(\<M> m)" 
        using a0 by blast
      have m_shd: "(\<M> m) = shd (x . c)"
        by (simp add: m_def s_def)
      have m_in_ctype: "(\<M> m) \<in> ctype c" 
        using numb_channel usclOkay_stream_def UnI1 contra_subsetD s_ubundle_eq_x sdom2un singletonI surj_scons ubdom_channel_usokay ubgetch_insert x_not_empty
        by (metis (no_types, lifting) m_shd)
      have s4: "s = (createBundle (\<M> m) c) . c " 
        using createbundle_stream_eq m_def m_in_ctype by force
      show ?thesis using s4 
        by blast
    qed 
  qed
  have x_eq: "(\<exists>m. x = (createBundle (Msg m) c)) \<or> (x = (tsynbNull c))" using s_cases s_def assms s_eq by (metis singletonD ubgetchI x_dom_eq_createbundle x_dom_eq_tsynbnull)
  show ?thesis using x_eq msg null by blast
qed


end