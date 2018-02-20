(*  Title:        Composition.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory Composition
imports Medium Receiver Sender Sender_OZ Sender_JM

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

lemma tssnd_in_tssender: "tsSnd \<in> tsSender"
proof-
  have prefix_inp: "\<And>i as. tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i"
    by (metis (no_types, lifting) tsabs_delayfun tsprojfst_tsabs tsremdups_tsabs tssnd_insert 
        tssnd_prefix_inp)
  have alt_bit: "\<And>i as. tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as)))) 
                    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as)))"
    by (metis tssnd_alt_bit tssnd_h_delayfun tssnd_insert)
  have ack2trans: "\<And>i as. tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd\<cdot>i\<cdot>as))) \<Longrightarrow>
                    #\<surd> as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as))) 
                    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
    by (metis (no_types, lifting) tsabs_delayfun tsprojfst_tsabs_slen tsprojsnd_tsabs 
        tsremdups_tsabs tssnd_ack2trans tssnd_insert)
  have nack2inftrans: "\<And>i as. #\<surd> as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) 
                        \<Longrightarrow> #(tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as)) = \<infinity>"
    by (simp add: tssnd_insert tssnd_nack2inftrans)
  have as_inftick: "\<And>i as. #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> lnsuc\<cdot>(#\<surd> as) \<le> #\<surd> tsSnd\<cdot>i\<cdot>as"
    by (simp add: tssnd_as_inftick)
  have tstickcount: " \<And>i as. min (#\<surd> i) (#\<surd> as) < \<infinity> \<Longrightarrow> min (#\<surd> i) (#\<surd> as) < #\<surd> tsSnd\<cdot>i\<cdot>as"
    by (simp add: tssnd_tstickcount)
  show ?thesis
    by (simp add: ack2trans alt_bit as_inftick nack2inftrans prefix_inp tstickcount tsSender_def)
qed

lemma tssendernempty: "tsSender \<noteq> {}"
  using tssnd_in_tssender by blast

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

lemma smed_sprojsnd: "sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p) = sMed\<cdot>(sprojsnd\<cdot>s)\<cdot>p"
  apply (induction s arbitrary: p rule: ind, simp_all)
  apply (case_tac a)
  by (rule_tac ts=p in oracases, simp_all)

lemma tsmed_tsprojsnd: "#ora = \<infinity> \<Longrightarrow> tsMed\<cdot>(tsProjSnd\<cdot>msg)\<cdot>ora = tsProjSnd\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  by (simp add: tsProjSnd_def tsmed_tsmap)

lemma srcdups_lshd: "lshd\<cdot>(srcdups\<cdot>s) = lshd\<cdot>s"
  apply (rule_tac x=s in scases ,simp_all)
  by (simp add: srcdups_step)

lemma smed2infmed: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "sMed\<cdot>(sMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = sMed\<cdot>msg\<cdot>ora3" and "#({True} \<ominus> ora3)=\<infinity>"
  by (simp add: assms(1) assms(2) newora_fair smed2med)

lemma smed_shd_true:"p1 \<noteq> \<epsilon> \<Longrightarrow> shd p1 = True \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>ds) = lshd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1)"
  apply(induction ds, simp_all)
  apply(cases rule: oracases [of p1], simp_all)
  by (simp add: lscons_conv tsabs_mlscons)

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
    obtain p3 where smed2med_app: "sMed\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds))\<cdot>p1)\<cdot>p2 = sMed\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds))\<cdot>p3" 
                and p3_inf: "#({True} \<ominus> p3)=\<infinity>"
      using p1_def p2_def smed2infmed by blast
    have ack2trans_pre_lshd:
      "lshd\<cdot>(srcdups\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1))\<cdot>p2)) = lshd\<cdot>(srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds)))"
      apply (simp add: smed_sprojsnd smed2med_app srcdups_lshd)
      apply (cases rule: oracases [of p3])
      using p3_inf apply auto[1]
      apply (metis Inf'_neq_0_rev only_empty_has_length_0 p3_inf sfilterl4 shd1 smed_shd_true 
             tsprojsnd_tsabs)
      sorry
    have ack2trans_pre_leq: 
      "#(srcdups\<cdot>(sMed\<cdot>(sprojsnd\<cdot>(sMed\<cdot>(tsAbs\<cdot>ds)\<cdot>p1))\<cdot>p2)) \<le> #(srcdups\<cdot>(sprojsnd\<cdot>(tsAbs\<cdot>ds)))"
      by (smt as_def ds_def le_cases min.orderE order.trans send_def slen_sprojsnd 
          sprojsnd_srcdups_slen srcdups_smed_h tsprojsnd_tsabs tsremdups_tsabs 
          tssnd_tsprojsnd_tsremdups)
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
    
    have i_as_le2lnle: 
      "#(tsAbs\<cdot>i) \<ge> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> #(tsAbs\<cdot>i) > (#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis as_leq_i i_ninf inf_ub leD le_neq_trans ln_less)
    
    have i_as_lnle2le: 
      "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      using lnle2le by blast

    have ds_ninf:"#(tsAbs\<cdot>i) \<ge> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> 
      #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> #(tsAbs\<cdot>ds) \<noteq> \<infinity>"
      proof (rule ccontr)
        assume as_leq_i: "lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<le> #(tsAbs\<cdot>i)"
        assume ds_eq_as: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
        have "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) \<noteq> \<infinity>"
          using as_leq_i ds_eq_as i_ninf by auto
        hence ds_srcdups_ninf: "#(srcdups\<cdot>(tsAbs\<cdot>ds)) \<noteq> \<infinity>"
          by (simp add: tsremdups_tsabs)
        have ds_inf: "#(tsAbs\<cdot>ds) = \<infinity>"
          using ar_def as_def as_leq_i dr_def ds_def i_as_le2lnle p1_def p2_def send_def 
                set2tssnd_nack2inftrans tstickcount_inp2infacks by blast
        obtain n where ds_split: "tsAbs\<cdot>ds = (stake n\<cdot>(tsAbs\<cdot>ds)) \<bullet> (\<up>(snth n (tsAbs\<cdot>ds))\<infinity>)"
          using srcdups_split ds_inf ds_srcdups_ninf inf_less_eq leI by blast
        thus "\<not> #(tsAbs\<cdot>ds) \<noteq> \<infinity> \<Longrightarrow> False"      
          sorry
      qed
      
    hence i_geq_as: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis ack2trans_post ar_def as_def dr_def ds_def i_as_lnle2le le_less_linear p1_def 
          p2_def send_def set2tssnd_nack2inftrans tstickcount_inp2infacks)
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