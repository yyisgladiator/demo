(*  Title:        Composition.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory Composition
imports Medium Receiver Prop0_DS

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition of the set of sender *}
(* ----------------------------------------------------------------------- *)

type_synonym 'a sender = "('a tstream \<rightarrow> bool tstream  \<rightarrow> ('a \<times> bool) tstream)"

definition tsSender :: "('a sender) set" where
"tsSender = {send :: 'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream.
  \<forall>i as.
  #\<surd>i = \<infinity> \<and>
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i \<and>
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<and>
  (#\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))
                   = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))) \<and>
  (#\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>) \<and>
  (min (#\<surd>i) (#\<surd>as) < \<infinity> \<longrightarrow> min (#\<surd>i) (#\<surd>as) < #\<surd>(send\<cdot>i\<cdot>as))
}"

lemma set2tssnd_strcausal: assumes "send \<in> tsSender"
  shows "min (#\<surd>i) (#\<surd>as) < \<infinity> \<longrightarrow> min (#\<surd>i) (#\<surd>as) < #\<surd>(send\<cdot>i\<cdot>as)"
  using assms tsSender_def by auto

(* 1st axiom *)
lemma set2tssnd_prefix_inp: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i"
  using assms tsSender_def by auto

lemma set2tssnd_alt_bit: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  using assms tsSender_def by auto

lemma tstickcount_inp2acks:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "#\<surd>i \<le> #\<surd>as"
  by (metis ar_def as_def dr_def ds_def inf_ub le_less min_def neq_iff p1_def p2_def send_def 
      set2tssnd_strcausal sfilterl4 tsmed_tstickcount tsprojsnd_tstickcount)

lemma tstickcount_inp2acks_inf:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "#\<surd>as = \<infinity>"
proof -
  have "#\<surd>i = \<infinity>"
    using send_def tsSender_def by auto
  thus "#\<surd>as = \<infinity>"
    by (metis ar_def as_def dr_def ds_def inf_less_eq p1_def p2_def send_def tstickcount_inp2acks)
qed

(* 5th axiom *)     
lemma set2tssnd_ack2trans: assumes "send \<in> tsSender"
  shows "#\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  using assms tsSender_def by auto

(* 4th axiom *)
lemma set2tssnd_nack2inftrans: assumes "send \<in> tsSender"
  shows "#\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>"
  using assms tsSender_def by auto

(* ----------------------------------------------------------------------- *)
subsection {* additional lemmata *}
(* ----------------------------------------------------------------------- *)

(* property 0 *)
lemma prop0: assumes "#({True} \<ominus> p) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>ts))"
  apply (simp add: tsremdups_tsabs)
  using prop0_h3 assms sfilterl4 by fastforce

(* property 1 *)
lemma prop1: assumes p1_def: "#({True} \<ominus> p1) = \<infinity>" and p2_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
proof -
  have "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1)))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
    by (metis (no_types) p1_def prop0 sfilterl4 tsProjSnd_def tsmed_map)
  thus "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
    using p2_def prop0 trans_lnle by blast
  qed

lemma set2tssnd_alt_bit_tsabs: assumes "send \<in> tsSender"
  shows "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as)))) 
    = (sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as))))"
  by (metis assms set2tssnd_alt_bit tsprojsnd_tsabs tsremdups_tsabs)

(* replaced property 2 #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts))) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) *)
lemma tssnd_tsprojsnd_tsremdups: 
  assumes send_def: "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  apply (simp add: tsprojsnd_tsabs tsremdups_tsabs sprojsnd_def)
  by (metis eta_cfun send_def set2tssnd_alt_bit_tsabs sprojsnd_def srcdups_smap_com)

(* property 3 *)
lemma prop3: assumes p1_def: "#({True} \<ominus> p1) = \<infinity>" and p2_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "#(tsAbs\<cdot>ts) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2)) = \<infinity>"
  by (simp add: p1_def p2_def)

(* property 4 *)
lemma prop4: assumes "#({True} \<ominus> p) = \<infinity>"
  shows (* removed #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) \<noteq> \<infinity> *)
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))
  \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p))))
  \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p)))"
  sorry

(* lnat auxiliary lemmata *)
lemma lnle2le: "m < lnsuc\<cdot>n \<Longrightarrow> m \<le> n"
  apply (case_tac "m=\<infinity>", auto)
  by (metis Fin_Suc less2lnleD lncases lnsuc_lnle_emb)

lemma le2lnle: "m < \<infinity> \<Longrightarrow> lnsuc\<cdot>m \<le> n \<Longrightarrow> m < n"
  by (metis dual_order.strict_iff_order dual_order.trans leD ln_less)

(* ----------------------------------------------------------------------- *)
subsection {* sender and receiver composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream
   ds = output stream 
*}
    
lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and as_def: "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have i_inf: "#\<surd>i = \<infinity>"
    using send_def tsSender_def by auto
  have i_leq_as: "#\<surd>i \<le> #\<surd>as"
    by (metis (no_types, lifting) as_def ds_def dual_order.strict_trans2 inf_ub min_def neq_iff 
        send_def set2tssnd_strcausal tsprojsnd_tstickcount)
  hence as_inf: "#\<surd>as = \<infinity>"
    by (simp add: i_inf)
  have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))"
    by (metis as_def ds_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
        tssnd_tsprojsnd_tsremdups send_def)
  thus "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis as_inf ds_def eq_slen_eq_and_less min_rek send_def set2tssnd_ack2trans
        set2tssnd_prefix_inp tsrecsnd_insert)
  qed

lemma tsaltbitpro_inp2out_nmed2:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = ds"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = ar"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    have i_inf: "#\<surd>i = \<infinity>"
      using send_def tsSender_def by auto
    have i_leq_as: "#\<surd>i \<le> #\<surd>as"
      by (metis ar_def as_def dr_def ds_def i_inf le_less_linear min_def neq_iff send_def
          set2tssnd_strcausal tsprojsnd_tstickcount)
    hence as_inf: "#\<surd>as = \<infinity>"
      by (simp add: i_inf)
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def)
    hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence leq: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis ar_def as_def dr_def ds_def mono_slen send_def set2tssnd_prefix_inp 
          tsprojfst_tsabs_slen tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis as_inf ds_def le_less_linear min.absorb2 send_def set2tssnd_ack2trans)
    hence geq: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis ar_def as_def dr_def ds_def lnat_po_eq_conv lnle2le min_def min_rek send_def 
          tsprojfst_tsabs_slen tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
    (* equalities *)
    have eq: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym geq leq)
    (* property 6 *)
    have prop6: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis ar_def as_def dr_def ds_def eq send_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
          tssnd_tsprojsnd_tsremdups)
    (* property 7 *)
    have prop7: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have prop8: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (simp add: dr_def)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have h4: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      by (simp add: dr_def)
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (simp add: ds_def eq_slen_eq_and_less prop6 send_def set2tssnd_prefix_inp)      
  qed

(* ----------------------------------------------------------------------- *)
subsection {* sender, receiver and second medium composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   dr = output stream (in receiver)
   p1/p2 = oracle stream
*}

lemma tsaltbitpro_inp2out_sndmed:
  assumes send_def: "send \<in> tsSender"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = ds"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    have i_inf: "#\<surd>i = \<infinity>"
      using send_def tsSender_def by auto
    have i_leq_as: "#\<surd>i \<le> #\<surd>as"
      by (metis ar_def as_def dr_def ds_def i_inf le_less_linear min_def neq_iff p2_def send_def
          set2tssnd_strcausal sfilterl4 tsmed_tstickcount tsprojsnd_tstickcount)
    hence as_inf: "#\<surd>as = \<infinity>"
      by (simp add: i_inf)
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def p2_def prop0)
    hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence leq: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis (no_types, lifting) ds_def min.coboundedI2 min_def mono_slen send_def 
          set2tssnd_prefix_inp)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      using as_inf ds_def leI min_absorb2 send_def set2tssnd_ack2trans by fastforce
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      proof -
        have "\<forall>t ta. #\<surd> t = \<infinity> \<and> tsAbs\<cdot> (tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta))) \<sqsubseteq> tsAbs\<cdot>t 
              \<and> tsAbs\<cdot> (tsRemDups\<cdot> (tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta)))) 
                = tsAbs\<cdot> (tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta))) 
              \<and> (#\<surd> ta = \<infinity> \<longrightarrow> #(tsAbs\<cdot> (tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta)))) 
                 = min (#(tsAbs\<cdot>t)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>ta))))) 
              \<and> (#\<surd> ta = \<infinity> \<and> #(tsAbs\<cdot>(tsRemDups\<cdot>ta)) < #(tsAbs\<cdot>t) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>t\<cdot>ta)) = \<infinity>) 
              \<and> (min (#\<surd> t) (#\<surd> ta) < \<infinity> \<longrightarrow> min (#\<surd> t) (#\<surd> ta) < #\<surd> send\<cdot>t\<cdot>ta)"
          using send_def tsSender_def by auto
        then show ?thesis
          by (metis (no_types) Inf'_neq_0 strict_tstickcount)
      qed
    hence geq: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis inf_ub leD leI less2eq ln_less lnle2le h3 tsprojfst_tsabs_slen)
    (* equalities *)
    have eq: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym geq leq)
    (* property 6 *)
    have prop6: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis ds_def dual_order.antisym eq h2 mono_slen send_def set2tssnd_prefix_inp)
    (* property 7 *)
    have prop7: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have prop8: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (simp add: dr_def)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have h4: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      by (simp add: dr_def)
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (simp add: ds_def eq_slen_eq_and_less prop6 send_def set2tssnd_prefix_inp)      
  qed

(* ----------------------------------------------------------------------- *)
subsection {* sender, receiver and first medium composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   dr = output stream (in receiver)
   p1/p2 = oracle stream
*}

lemma tsaltbitpro_inp2out_fstmed:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = ar"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    have i_inf: "#\<surd>i = \<infinity>"
      using send_def tsSender_def by auto
    have i_leq_as: "#\<surd>i \<le> #\<surd>as"
      by (metis ar_def as_def dr_def ds_def dual_order.irrefl i_inf le_less_linear min_def p1_def 
          send_def set2tssnd_strcausal sfilterl4 tsmed_tstickcount tsprojsnd_tstickcount)
    hence as_inf: "#\<surd>as = \<infinity>"
      by (simp add: i_inf)
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have ora_inf: "#p1 = \<infinity>"
      using p1_def sfilterl4 by auto
    hence tsmed_tsprojsnd: "tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p1 = tsProjSnd\<cdot>(tsMed\<cdot>ds\<cdot>p1)"
      by (simp add: tsprojsnd_insert tsmed_map)
    have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (metis ar_def as_def dr_def p1_def prop0 tsmed_tsprojsnd)
    hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence leq: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis (no_types, lifting) ds_def min.coboundedI2 min_def mono_slen send_def 
          set2tssnd_prefix_inp)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis as_inf ds_def le_less_linear min.absorb2 send_def set2tssnd_ack2trans)
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      proof -
        have "\<forall>t ta. #\<surd> t = \<infinity> \<and> tsAbs\<cdot> (tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta))) \<sqsubseteq> tsAbs\<cdot>t 
              \<and> tsAbs\<cdot> (tsRemDups\<cdot> (tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta)))) 
                = tsAbs\<cdot> (tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta))) 
              \<and> (#\<surd> ta = \<infinity> \<longrightarrow> #(tsAbs\<cdot> (tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta)))) 
                 = min (#(tsAbs\<cdot>t)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>ta))))) 
              \<and> (#\<surd> ta = \<infinity> \<and> #(tsAbs\<cdot>(tsRemDups\<cdot>ta)) < #(tsAbs\<cdot>t) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>t\<cdot>ta)) = \<infinity>) 
              \<and> (min (#\<surd> t) (#\<surd> ta) < \<infinity> \<longrightarrow> min (#\<surd> t) (#\<surd> ta) < #\<surd> send\<cdot>t\<cdot>ta)"
          using send_def tsSender_def by auto
        then show ?thesis
          by (metis (no_types) Inf'_neq_0 strict_tstickcount)
      qed
    hence geq: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis h2 less2eq lnle2le h3 min_def min_rek tsprojfst_tsabs_slen)
    (* equalities *)
    have eq: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym geq leq)
    (* property 6 *)
    have prop6: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis ds_def dual_order.antisym eq h2 mono_slen send_def set2tssnd_prefix_inp)
    (* property 7 *)
    have prop7: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have prop8: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      using ar_def as_def eq prop6 prop7 by auto
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have h4: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      using ar_def as_def dr_def eq p1_def prop4 prop6 prop7 by fastforce
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (simp add: ds_def eq_slen_eq_and_less prop6 send_def set2tssnd_prefix_inp)      
  qed

(* ----------------------------------------------------------------------- *)
subsection {* complete composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   dr = output stream (in receiver)
   p1/p2 = oracle stream
*}

lemma tsaltbitpro_inp2out:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def p1_def p2_def prop1)
    hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence leq: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis (no_types, lifting) ds_def min.coboundedI2 min.orderE mono_slen send_def
          set2tssnd_prefix_inp)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis ar_def as_def dr_def ds_def le_less_linear min.absorb2 p1_def p2_def send_def 
          set2tssnd_ack2trans tstickcount_inp2acks_inf)
    have hh1: "#(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      proof -
        have "\<forall>t ta. #\<surd> t = \<infinity> \<and> tsAbs\<cdot> (tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta))) \<sqsubseteq> tsAbs\<cdot>t 
              \<and> tsAbs\<cdot> (tsRemDups\<cdot> (tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta)))) 
                = tsAbs\<cdot> (tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta))) 
              \<and> (#\<surd> ta = \<infinity> \<longrightarrow> #(tsAbs\<cdot> (tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>t\<cdot>ta)))) 
                 = min (#(tsAbs\<cdot>t)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>ta))))) 
              \<and> (#\<surd> ta = \<infinity> \<and> #(tsAbs\<cdot>(tsRemDups\<cdot>ta)) < #(tsAbs\<cdot>t) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>t\<cdot>ta)) = \<infinity>) 
              \<and> (min (#\<surd> t) (#\<surd> ta) < \<infinity> \<longrightarrow> min (#\<surd> t) (#\<surd> ta) < #\<surd> send\<cdot>t\<cdot>ta)"
          using send_def tsSender_def by auto
        then show ?thesis
          by (metis (no_types) Inf'_neq_0 strict_tstickcount)
      qed
    hence geq: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis h2 leq lnle2le h3 min.absorb2 min_absorb1 min_rek tsprojfst_tsabs_slen)
    (* equalities *)
    have eq: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym geq leq)
    (* property 6 *)
    have prop6: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      using eq h2 hh1 by auto
    (* property 7 *)
    have prop7: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have prop8: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (metis ar_def as_def dr_def dual_order.antisym eq p1_def p2_def prop0 prop6 prop7
          sfilterl4 tsmed_map tsprojsnd_insert)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have h4: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      using dr_def p1_def prop4 prop6 prop7 prop8 by force  
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (simp add: ds_def eq_slen_eq_and_less prop6 send_def set2tssnd_prefix_inp)      
  qed

end