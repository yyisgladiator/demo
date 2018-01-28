(*  Title:        Composition.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory Composition
imports Medium Receiver

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition of the set of sender *}
(* ----------------------------------------------------------------------- *)

type_synonym 'a sender = "('a tstream \<rightarrow> bool tstream  \<rightarrow> ('a \<times> bool) tstream)"

definition tsSender :: "('a sender) set" where
"tsSender = {send :: 'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream.
  \<forall>i as.
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i \<and>
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<and>
  (tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) \<longrightarrow> 
   #\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))
                   = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))) \<and>
  (#\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>) \<and>
(*
  (#(tsAbs\<cdot>as) = \<infinity> \<longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<and>
*)
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> lnsuc\<cdot>(#\<surd>as) \<le> #\<surd>(send\<cdot>i\<cdot>as)) \<and>
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

lemma set2tssnd_as_inftick: assumes "send \<in> tsSender"
  shows "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> lnsuc\<cdot>(#\<surd>as) \<le> #\<surd>(send\<cdot>i\<cdot>as)"
  using assms tsSender_def by auto

lemma tstickcount_inp2infacks:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
    and i2as: "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
  shows "#\<surd>as = \<infinity>"
  by (metis ar_def as_def dr_def ds_def i2as inf_less_eq leD le_less_linear ln_less p1_def p2_def 
      send_def set2tssnd_as_inftick sfilterl4 tsmed_tstickcount tsprojsnd_tstickcount)

(* 5th axiom *)     
lemma set2tssnd_ack2trans: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) \<longrightarrow> #\<surd>as = \<infinity> \<longrightarrow>
         #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))
                        = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  using assms tsSender_def by auto

(* 4th axiom *)
lemma set2tssnd_nack2inftrans: assumes "send \<in> tsSender"
  shows "#\<surd>as = \<infinity> \<longrightarrow> #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>"
  using assms tsSender_def by auto

(*
(* 3rd axiom *)
lemma set2tssnd_infacks2inpack: assumes "send \<in> tsSender"
  shows "#(tsAbs\<cdot>as) = \<infinity> \<longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
  using assms tsSender_def by auto
*)

(* ----------------------------------------------------------------------- *)
subsection {* additional lemmata *}
(* ----------------------------------------------------------------------- *)

(* property 0 *)
lemma tsmed_tsremdups_tsabs_slen: assumes "#({True} \<ominus> p) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>ts))"
  apply (simp add: tsremdups_tsabs)
  using prop0_h3 assms sfilterl4 by fastforce

(* property 1 *)
lemma tsmed2_tsremdups_tsabs_slen:
  assumes p1_def: "#({True} \<ominus> p1) = \<infinity>" and p2_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
proof -
  have "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1)))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
    by (metis (no_types) p1_def tsmed_tsremdups_tsabs_slen sfilterl4 tsProjSnd_def tsmed_tsmap)
  thus "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
    using p2_def tsmed_tsremdups_tsabs_slen trans_lnle by blast
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
lemma tsmed2_tsabs_slen_inf: 
  assumes p1_def: "#({True} \<ominus> p1) = \<infinity>" and p2_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "#(tsAbs\<cdot>ts) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2)) = \<infinity>"
  by (simp add: p1_def p2_def)

(* property 4 *)
lemma tsmed_tsabs_slen2tsmed_tsabs: 
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> p) = \<infinity> 
  \<Longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))
  \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p))))
  \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p)))"
  apply (simp add: tsprojfst_tsabs tsprojsnd_tsabs tsremdups_tsabs tsmed_tsabs ora_inf)
  using smed_slen2smed by auto

(* ----------------------------------------------------------------------- *)
subsection {* sender and receiver composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream
   ds = output stream 
*}

lemma tstickcount_inp2infacks_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and as_def: "as = tsProjSnd\<cdot>ds"
    and i2as: "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
  shows "#\<surd>as = \<infinity>"
  by (metis as_def ds_def i2as inf_ub less_lnsuc min.absorb2 min.orderE min_rek send_def
      set2tssnd_as_inftick tsprojsnd_tstickcount)

lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and as_def: "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
  proof -
  have slen_as: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))"
    by (metis as_def ds_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
        tssnd_tsprojsnd_tsremdups send_def)
  thus "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis (no_types, lifting) as_def below_refl ds_def eq_slen_eq_and_less le_neq_trans 
        min_rek mono_slen send_def set2tssnd_ack2trans set2tssnd_prefix_inp tsrecsnd_insert 
        tstickcount_inp2infacks_nmed)
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
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def)
    hence as_leq_ds: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence as_leq_i: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis ar_def as_def dr_def ds_def mono_slen send_def set2tssnd_prefix_inp 
          tsprojfst_tsabs_slen tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have as_inf: "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #\<surd>as = \<infinity>"
      using ar_def as_def dr_def ds_def send_def tstickcount_inp2infacks_nmed by blast
    have "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis ar_def as_def as_inf as_leq_i below_refl dr_def ds_def less_le less_lnsuc min_rek 
          send_def set2tssnd_ack2trans tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
          tssnd_tsprojsnd_tsremdups)
    hence i_geq_as: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis ar_def as_def dr_def ds_def dual_order.strict_iff_order inf_ub ln_less lnle2le 
          send_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
    (* property 6 *)
    have i_eq_ds: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis ar_def as_def as_leq_i dr_def ds_def i_geq_as min_absorb2 min_def send_def 
          tsprojfst_tsabs_slen tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
    (* property 7 *)
    have projfst2projsnd: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have ds_eq_dr: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (simp add: dr_def)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      by (simp add: dr_def)
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (simp add: ds_def eq_slen_eq_and_less i_eq_ds send_def set2tssnd_prefix_inp)
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

lemma tsaltbitpro_inp2out_ninf:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
    and i_ninf: "#(tsAbs\<cdot>i) \<noteq> \<infinity>"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def p1_def p2_def tsmed2_tsremdups_tsabs_slen)
    hence as_leq_ds: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence as_leq_i: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis (mono_tags, lifting) ds_def min.coboundedI1 min_absorb2 mono_slen send_def
          set2tssnd_prefix_inp)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      sorry
(* adjustments for set2tssnd_ack2trans and set2tssnd_infacks2inpack needed
      by (metis ar_def as_def as_leq_ds as_leq_i dr_def ds_def dual_order.order_iff_strict less2eq 
          less_lnsuc min_absorb2 min_rek p1_def p2_def send_def set2tssnd_ack2trans 
          set2tssnd_infacks2inpack set2tssnd_nack2inftrans tsmed2_tsabs_slen_inf 
          tsprojfst_tsabs_slen tstickcount_inp2infacks)
*)
    hence i_geq_as: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      sorry
(* adjustments for set2tssnd_ack2trans and set2tssnd_infacks2inpack needed
      by (metis ar_def as_def as_leq_ds dr_def ds_def leD le_less_linear le_neq_trans min_rek 
          p1_def p2_def send_def set2tssnd_ack2trans set2tssnd_infacks2inpack 
          set2tssnd_nack2inftrans tsmed2_tsabs_slen_inf tsprojfst_tsabs_slen 
          tstickcount_inp2infacks)
*)
    (* equalities *)
    have i_eq_as: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym i_geq_as as_leq_i)
    (* property 6 *)
    have i_eq_ds: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis as_leq_ds ds_def i_eq_as less2eq mono_slen send_def set2tssnd_prefix_inp)
    (* property 7 *)
    have projfst2projsnd: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have ds_eq_dr: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (metis ar_def as_def dr_def dual_order.antisym i_eq_as p1_def p2_def 
          tsmed_tsremdups_tsabs_slen i_eq_ds projfst2projsnd sfilterl4 tsmed_tsmap tsprojsnd_insert)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have "#(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      using dr_def p1_def tsmed_tsabs_slen2tsmed_tsabs i_eq_ds projfst2projsnd ds_eq_dr by force
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (metis ds_def eq_slen_eq_and_less i_ninf i_eq_ds send_def set2tssnd_prefix_inp)
  oops

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
  oops

(* ----------------------------------------------------------------------- *)
subsection {* complete composition workspace *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   dr = output stream (in receiver)
   p1/p2 = oracle stream
*}

lemma tsmed_tsprojsnd:"#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>(tsProjSnd\<cdot>ts)\<cdot>ora = tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>ora)"
  by (simp add: tsProjSnd_def tsmed_tsmap)

lemma sprojsnd_smed: "sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p) = sMed\<cdot>(sprojsnd\<cdot>s)\<cdot>p"
  apply (induction s arbitrary: p rule:ind, simp_all)
  apply (case_tac a)
  by (rule_tac ts=p in oracases,simp_all)

lemma srcdups_lshd: "lshd\<cdot>(srcdups\<cdot>s) = lshd\<cdot>s"
  apply (rule_tac x=s in scases,simp_all)
  by (simp add: srcdups_step)
                               
lemma tsaltbitpro_inp2out:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
    and i_ninf: "#(tsAbs\<cdot>i) \<noteq> \<infinity>"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    (* auxiliary properties *)
    have p1_inf: "#p1 = \<infinity>"
      using p1_def sfilterl4 by auto
    have p2_inf: "#p2 = \<infinity>"
      using p2_def sfilterl4 by auto
    have "lshd\<cdot>(tsAbs\<cdot>as) = lshd\<cdot>(tsAbs\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as)))" 

      sorry
    then have ack2trans_pre_lshd: 
      "lshd\<cdot>(srcdups\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1))\<cdot>p2)) = lshd\<cdot>(srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds)))"
      by (metis ar_def as_def dr_def ds_def p1_inf p2_inf srcdups_lshd tsmed_tsabs tsprojsnd_tsabs)
    have ack2trans_pre_leq: 
      "#(srcdups\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1))\<cdot>p2)) \<le> #(srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds)))"
      by (smt dual_order.trans p1_inf srcdups_smed_h tsmed_tsabs tsmed_tsprojsnd tsprojsnd_tsabs)
    have "srcdups\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1))\<cdot>p2) \<sqsubseteq> srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds))"
      using ack2trans_pre_leq ack2trans_pre_lshd srcdups_bool_prefix by auto
    hence ack2trans_pre: "tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))"
      by (simp add: ar_def as_def dr_def p1_inf p2_inf tsmed_tsabs tsprojsnd_tsabs tsremdups_tsabs)
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def p1_def p2_def tsmed2_tsremdups_tsabs_slen)
    hence as_leq_ds: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence as_leq_i: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis (mono_tags, lifting) ds_def min.coboundedI1 min_absorb2 mono_slen send_def
          set2tssnd_prefix_inp)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have ack2trans_post: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis ack2trans_pre ar_def as_def as_leq_i dr_def ds_def dual_order.strict_iff_order 
          i_ninf inf_ub ln_less min_def p1_def p2_def send_def set2tssnd_ack2trans 
          tstickcount_inp2infacks)
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<noteq> \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      apply (simp add: as_def ar_def dr_def)
      apply (simp add: tsremdups_tsabs tsmed_tsabs tsprojsnd_tsabs p1_inf p2_inf)
      
      sorry
    have h1:"#\<surd>as = #\<surd>(send\<cdot>i\<cdot>as)" 
    apply (subst as_def)
    apply (simp add: ar_def dr_def ds_def)
      by (simp add: p1_inf p2_inf)

  (*  have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<noteq> \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      apply (simp add: tsremdups_tsabs)
      proof (rule ccontr)
        assume a1: "#(srcdups\<cdot>(tsAbs\<cdot>as)) \<noteq> \<infinity>"
        assume a2: "\<not> #(srcdups\<cdot>(tsAbs\<cdot>ds)) \<le> #(srcdups\<cdot>(tsAbs\<cdot>as))"
        hence q1: "#(srcdups\<cdot>(tsAbs\<cdot>as)) \<le> #(srcdups\<cdot>(tsAbs\<cdot>ds))"
          by auto
        hence q2: "#(srcdups\<cdot>(tsAbs\<cdot>as)) < #(tsAbs\<cdot>i)"
          by (metis (no_types, lifting) a2 antisym_conv as_leq_i ds_def leI lnle_def 
              monofun_cfun_arg send_def set2tssnd_prefix_inp tsprojfst_tsabs_slen tsremdups_tsabs)
        hence q3: "#(tsAbs\<cdot>ds) = \<infinity>"
          by (metis ar_def as_def dr_def ds_def p1_def p2_def send_def set2tssnd_nack2inftrans 
              tsremdups_tsabs tstickcount_inp2infacks)
        hence q4: "#(tsAbs\<cdot>as) = \<infinity>"
          using ar_def as_def dr_def ds_def p1_def p2_def by force

        have q5: "#(srcdups\<cdot>(tsAbs\<cdot>ds)) \<noteq> \<infinity>"
          by (metis (no_types, lifting) ds_def i_ninf mono_fst_infD send_def set2tssnd_prefix_inp 
              tsprojfst_tsabs_slen tsremdups_tsabs)
        
        have q6: "#(srcdups\<cdot>(tsAbs\<cdot>ds)) = lnsuc\<cdot>(#(srcdups\<cdot>(tsAbs\<cdot>as)))"
          by (metis ack2trans_post dual_order.strict_iff_order less2eq lnle2le q2 
              tsprojfst_tsabs_slen tsremdups_tsabs)

        obtain n where q7: "tsAbs\<cdot>ds = (stake n\<cdot>(tsAbs\<cdot>ds)) \<bullet> (\<up>(snth n (tsAbs\<cdot>ds))\<infinity>)"
          using srcdups_split inf_less_eq leI q3 q5 by blast
        obtain m where q8: "tsAbs\<cdot>as = (stake m\<cdot>(tsAbs\<cdot>as)) \<bullet> (\<up>(snth m (tsAbs\<cdot>as))\<infinity>)"
          using a1 srcdups_split inf_less_eq leI q4 by blast

        have q9: "#(\<up>(snth n (tsAbs\<cdot>ds))\<infinity>) = \<infinity>"
          by auto
       
    qed *)
    have h2:"lnsuc\<cdot>(#\<surd>as) > #\<surd>(send\<cdot>i\<cdot>as) \<Longrightarrow> #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (meson leD le_less_linear send_def set2tssnd_as_inftick)
    have h3:"#(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) \<noteq> \<infinity> \<Longrightarrow> #\<surd>as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (meson leI send_def set2tssnd_nack2inftrans)
    have h45:"#\<surd>as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow>  #(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as))) \<noteq> \<infinity>"
      by (metis (no_types, lifting) mono_fst_infD send_def set2tssnd_prefix_inp tsprojfst_tsabs_slen tsremdups_tsabs)
    have h4:"#(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) \<noteq> \<infinity>"
      apply (erule contrapos_pp,simp)
      apply (simp add: as_def ar_def dr_def)
      apply (simp add: ds_def)
      apply (simp add: p1_inf p2_inf tsmed_tsprojsnd tsmed2med)
      sorry
    have h4_v2:"#(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as))) \<noteq> \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) \<noteq> \<infinity>"
      apply (erule contrapos_pp,simp)
      sorry
    have h5: "#(tsAbs\<cdot>i) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as)))"
      by (metis ar_def as_def as_leq_ds as_leq_i dr_def ds_def dual_order.antisym i_ninf leI local.h3 local.h4 p1_def p2_def send_def tsprojfst_tsabs_slen tsremdups_tsabs tstickcount_inp2infacks)
    have h6: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      using lnle2le by blast
    have h7: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis ar_def as_def dr_def ds_def i_ninf leI local.h3 local.h4 p1_def p2_def send_def tstickcount_inp2infacks)
      
  have i_geq_as: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
    using ack2trans_post h6 h7 by blast
      apply (case_tac "#\<surd>as =\<infinity>")
      apply (rule h3,simp_all)
      apply (simp add: i_ninf local.h4)
      apply (rule h2)
      apply (fold h1)
      using inf_less_eq linorder_le_less_linear ln_less by blast
      
     (* apply (simp add: as_def ar_def dr_def)
      apply (subst ds_def)
      apply (simp add: tsremdups_tsabs p1_inf p2_inf tsmed_tsabs tsprojsnd_tsabs)
      apply (simp add: sprojsnd_def smed_smap smed2med)
          
by (meti ack2trans_post as_leq_ds dual_order.antisym inf_ub lnle2le min_def min_rek 
          tsprojfst_tsabs_slen) *)
    (* equalities *)
    have i_eq_as: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym i_geq_as as_leq_i)
    (* property 6 *)
    have i_eq_ds: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis as_leq_ds ds_def i_eq_as less2eq mono_slen send_def set2tssnd_prefix_inp)
    (* property 7 *)
    have projfst2projsnd: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have ds_eq_dr: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (metis ar_def as_def dr_def dual_order.antisym i_eq_as p1_def p2_def 
          tsmed_tsremdups_tsabs_slen i_eq_ds projfst2projsnd sfilterl4 tsmed_tsmap tsprojsnd_insert)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have "#(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      using dr_def p1_def tsmed_tsabs_slen2tsmed_tsabs i_eq_ds projfst2projsnd ds_eq_dr by force
    thus "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      by (metis ds_def eq_slen_eq_and_less i_ninf i_eq_ds send_def set2tssnd_prefix_inp)
  oops

end