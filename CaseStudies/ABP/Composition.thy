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

lemma srcdups_lshd1: "lshd\<cdot>(srcdups\<cdot>s) = lshd\<cdot>s"
  apply (rule_tac x=s in scases,simp_all)
  by (simp add: srcdups_step)
    
lemma srcdups_lshd:"srcdups\<cdot>a = srcdups\<cdot>b \<Longrightarrow> lshd\<cdot>a = lshd\<cdot>b"
  by (metis lshd_updis srcdups_nbot srcdups_shd2 strict_srcdups surj_scons)
    
lemma srcdups_sprojsnd_lshd:"lshd\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>a)) = lshd\<cdot>(srcdups\<cdot>(sprojsnd\<cdot>a))"
  apply(rule_tac x=a in scases,simp_all)
  apply(simp add: srcdups_lshd1)
  by (smt eta_cfun lshd_updis smap_hd_rst smap_scons sprojsnd_def srcdups_lshd srcdups_shd stream.sel_rews(1) strict_srcdups up_defined)

lemma smed_shd_t:"p1 \<noteq> \<epsilon> \<Longrightarrow> shd p1 = True \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>ds) = lshd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1)"
  apply(rule_tac x = p1 in scases,simp_all)  
  apply(induction ds arbitrary: s,simp_all)
  by(simp add: tsabs_mlscons lscons_conv smed_t)
    
lemma tsmed_tsabs_slen2tsmed_tsabs2: 
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> p) = \<infinity> 
  \<Longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))
  \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p))))
  \<Longrightarrow> tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>ts)) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p)))"
  apply (simp add: tsprojfst_tsabs tsprojsnd_tsabs tsremdups_tsabs tsmed_tsabs ora_inf)
  by (metis (no_types, lifting) slen_sprojs_eq slen_sprojsnd smed_slen2smed2)
  
lemma lshd_smed_t:"lshd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>(\<up>True \<bullet> p11)) = lshd\<cdot>(tsAbs\<cdot>ds)"
  by (metis shd1 smed_shd_t srcdupsimposs2_h2 strictI strict_srcdups)

lemma sdropwhile_sdom_bool:"sdom\<cdot>p1 \<subseteq> {True} \<Longrightarrow> p1 \<noteq> \<epsilon> \<Longrightarrow> shd(sdropwhile (\<lambda>x. x = False)\<cdot>p1) = True"
  apply(induction p1,simp_all)
  apply(rule adm_imp,simp)+
  apply(rule admI)
  apply (smt ch2ch_Rep_cfunR contlub_cfun_arg lub_eq_bottom_iff tsmed_shd_adm_h2)
  apply(case_tac "u = lshd\<cdot>(\<up>True)",simp_all)
  apply (metis inject_scons lscons_conv sdropwhile_f stream.con_rews(2) stream.sel_rews(4) sup'_def surj_scons up_defined)
  by (metis lshd_updis sfilter_ne_resup sfilter_sdoml4 singletonD stream.sel_rews(1) stream.sel_rews(4) strict_sdom_rev subset_singleton_iff sup'_def surj_scons)
  
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
    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def p1_def p2_def tsmed2_tsremdups_tsabs_slen)
    hence as_leq_ds: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence as_leq_i: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      by (metis (mono_tags, lifting) ds_def min.coboundedI1 min_absorb2 mono_slen send_def
          set2tssnd_prefix_inp)
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
   (* have "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
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
*)*)
    (* equalities *)
    (*have i_eq_as: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      apply (simp add: dual_order.antisym  as_leq_i)
      sorry
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
    have "#(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>ds))"
      apply(simp add: dr_def)
      using dr_def ds_eq_dr i_eq_ds p1_def projfst2projsnd tsmed_tsabs_slen2tsmed_tsabs2 by force*)
    have h01:"snth n p1 = False \<Longrightarrow> snth n (tsAbs\<cdot>ds) = snth (n+1) (tsAbs\<cdot>ds)"
      apply(insert snths_eq)
      sorry
    have h0:"lshd\<cdot>(tsAbs\<cdot>ds) = lshd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1)"
    proof(case_tac "shd p1 = True")
      assume a0:"shd p1 = True"
      have "p1 \<noteq> \<epsilon>"
        using p1_inf by auto
      then show ?thesis
        by (simp add: a0 smed_shd_t)
    next
      assume a0:"shd p1 \<noteq> True"
      have h0:"\<exists>n. sdrop n\<cdot>p1 = sdropwhile (\<lambda>x. x = False)\<cdot>p1"
      proof-
        have h01:"\<exists>n. #(stakewhile(\<lambda>x. x = False)\<cdot>p1) = Fin n"
          by (metis Inf'_neq_0_rev approxl2 ex_snth_in_sfilter_nempty p1_def singletonD slen_empty_eq stakewhile_below stakewhile_noteq)
        then show ?thesis
          using stakewhile_sdropwhilel1 by fastforce
      qed   
      obtain n where "sdrop n\<cdot>p1 = sdropwhile (\<lambda>x. x = False)\<cdot>p1"
        using h0 by blast
      have h1:" shd(sdropwhile (\<lambda>x. x = False)\<cdot>p1) = True"
        by (metis Inf'_neq_0_rev \<open>sdrop n\<cdot>p1 = sdropwhile (\<lambda>x. x = False)\<cdot>p1\<close> fair_sdrop only_empty_has_length_0 p1_inf sdropwhile_resup surj_scons)
      have h2:" shd(sdrop n\<cdot>p1) = True"
        using \<open>sdrop n\<cdot>p1 = sdropwhile (\<lambda>x. x = False)\<cdot>p1\<close> h1 by auto
      have h31:"\<forall>t. t\<le>n+1 --> snth t (tsAbs\<cdot>ds) = shd(tsAbs\<cdot>ds)"
        sorry
      have h3:"lshd\<cdot>(tsAbs\<cdot>ds) = lshd\<cdot>(sdrop n\<cdot>(tsAbs\<cdot>ds))"
      proof-
        have h32:"shd (sdrop n\<cdot>(tsAbs\<cdot>ds)) = snth (n+1)(tsAbs\<cdot>ds)"
          by (metis eq_iff h31 le_add1 snth_def)
        have h33:"snth (n+1)(tsAbs\<cdot>ds) = shd (tsAbs\<cdot>ds)"
          by (simp add: h31)
        then show ?thesis
          sorry
      qed
      have h4:"lshd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1) = lshd\<cdot>(sMed\<cdot>(sdrop n\<cdot>(tsAbs\<cdot>ds))\<cdot>(sdrop n\<cdot>p1))"
        sorry
      have h5:"lshd\<cdot>(tsAbs\<cdot>ds) = lshd\<cdot>(sMed\<cdot>(sdrop n\<cdot>(tsAbs\<cdot>ds))\<cdot>(sdrop n\<cdot>p1))"
      proof -
          have "sdrop n\<cdot>p1 = \<epsilon> \<or> \<up>True \<bullet> srt\<cdot>(sdrop n\<cdot>p1) = sdrop n\<cdot>p1"
            by (metis (full_types) h2 surj_scons)
          then show ?thesis
            by (metis (no_types) Inf'_neq_0_rev fair_sdrop local.h3 lshd_updis only_empty_has_length_0 p1_inf smed_bot1 smed_t surj_scons)
        qed
      then show ?thesis
        by (simp add: local.h4)
    qed
    have h1:"lshd\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>ds))) = lshd\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1)))"
      sorry
      (*by (metis \<open>#(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>ds))\<close> dr_def i_ninf p1_inf tsmed_tsabs tsprojsnd_tsabs tsremdups_tsabs)*)
    have h11:"(sMed\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds))\<cdot>(newOracle\<cdot>p1\<cdot>p2)) = sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>(newOracle\<cdot>p1\<cdot>p2))"
      by (simp add: sprojsnd_smed)
    have h12:"lshd\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>(newOracle\<cdot>p1\<cdot>p2)))) = lshd\<cdot>(srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds)))"   
      (*by (smt ar_def as_def dr_def ds_def ds_eq_dr i_eq_as i_eq_ds i_ninf p1_def p1_inf p2_def p2_inf projfst2projsnd send_def smed2med tsmed_tsabs tsmed_tsabs_slen2tsmed_tsabs tsmed_tsabs_slen2tsmed_tsabs2 tsmed_tsprojsnd tsprojsnd_tsabs tsremdups_tsabs tssnd_tsprojsnd_tsremdups)*)
      sorry
    have h13:"lshd\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>(newOracle\<cdot>p1\<cdot>p2)))) = lshd\<cdot>(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>(newOracle\<cdot>p1\<cdot>p2))))"
      using srcdups_sprojsnd_lshd by auto 
    have ack2trans_pre_lshd: 
      "lshd\<cdot>(srcdups\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1))\<cdot>p2)) = lshd\<cdot>(srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds)))"
      apply(simp add: sprojsnd_smed smed2med)
      apply(simp add: h11)
      using h13 h12 by auto
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

    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<noteq> \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      apply (simp add: as_def ar_def dr_def)
      apply (simp add: tsremdups_tsabs tsmed_tsabs tsprojsnd_tsabs p1_inf p2_inf)
      sorry

    have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<noteq> \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>ds)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
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
        thus "False"
          sorry
    qed

    hence i_geq_as: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis ack2trans_post as_leq_ds dual_order.antisym inf_ub lnle2le min_def min_rek 
          tsprojfst_tsabs_slen)
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