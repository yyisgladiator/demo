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
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<and>
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) \<and>
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)
}"

lemma set2tssnd_prefix_inp: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i"
  using assms tsSender_def by auto

lemma set2tssnd_alt_bit: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  using assms tsSender_def by auto

lemma set2tssnd_alt_bit_tabs: assumes "send \<in> tsSender"
  shows "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as)))) 
    = (sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as))))"
  by (metis assms set2tssnd_alt_bit tsprojsnd_tsabs tsremdups_tsabs)
    
lemma set2tssnd_ack2trans: assumes "send \<in> tsSender"
  shows "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  using assms tsSender_def by auto

lemma set2tssnd_nack2inftrans: assumes "send \<in> tsSender"
  shows "(#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)"
  using assms tsSender_def by auto

(* ----------------------------------------------------------------------- *)
subsection {* sender and receiver composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream
   ds = output stream 
*}

lemma srcdups_eq2:"a=b \<Longrightarrow> srcdups\<cdot>(\<up>a\<bullet>\<up>b\<bullet>s) = srcdups\<cdot>(\<up>b\<bullet>s)"
  by simp
    
lemma srcdups_ex:"\<exists>y. srcdups\<cdot>(\<up>a\<bullet>s) = \<up>a\<bullet>y"
  by(subst srcdups_def [THEN fix_eq2], auto)
    
lemma srcdups_shd[simp]:"shd (srcdups\<cdot>(\<up>a\<bullet>s)) = a"
  by(subst srcdups_def [THEN fix_eq2],auto)

lemma srcdups_srt:"srt\<cdot>(srcdups\<cdot>(\<up>a\<bullet>s)) = (srcdups\<cdot>(sdropwhile (\<lambda>z. z = a)\<cdot>s))"
  by(subst srcdups_def [THEN fix_eq2], auto)
    
lemma srcdups_shd2[simp]:"s\<noteq>\<epsilon> \<Longrightarrow> shd (srcdups\<cdot>s) = shd s"
  by(subst srcdups_def [THEN fix_eq2],auto)

lemma srcdups_srt2:"s\<noteq>\<epsilon> \<Longrightarrow> srt\<cdot>(srcdups\<cdot>s) = (srcdups\<cdot>(sdropwhile (\<lambda>z. z = shd s)\<cdot>(srt\<cdot>s)))"
  by(subst srcdups_def [THEN fix_eq2],auto)

lemma srcdups2srcdups: "srcdups\<cdot>(srcdups\<cdot>s) = srcdups\<cdot>s"
proof(induction rule: ind [of _ s])
  case 1
  then show ?case 
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 a s)
  have f1:"a = shd s \<Longrightarrow> s\<noteq>\<epsilon>\<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = srcdups\<cdot>s"
    using srcdups_eq[of "shd s" "srt\<cdot>s"] surj_scons[of s] by auto
  have f2:"a=shd s \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> srcdups\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)) = srcdups\<cdot>(\<up>a \<bullet> s)"
    using f1 "3.IH" by auto
  moreover have"a\<noteq>shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a\<bullet>srcdups\<cdot>s"
    by (metis lscons_conv srcdups_neq strict_srcdups surj_scons tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)
  ultimately have f3:"a\<noteq> shd s \<Longrightarrow>srcdups\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)) = srcdups\<cdot>(\<up>a \<bullet> s)"
  proof -
    assume a1: "a \<noteq> shd s"
    then have f2: "srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>s"
      by (metis \<open>a \<noteq> shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>s\<close>)
    obtain ss :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      f3: "\<forall>a s. srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> ss s a"
      by (meson srcdups_ex)
    then have f4: "\<up>(shd s) \<bullet> srt\<cdot>s = s \<longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> \<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s)"
      using f2 by metis
    have f5: "\<up>(shd s) \<bullet> srt\<cdot>s = s \<longrightarrow> srcdups\<cdot>(\<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s)) = srcdups\<cdot>s"
      using f3 by (metis "3.IH")
    { assume "\<up>a \<bullet> s \<noteq> srcdups\<cdot>(\<up>a \<bullet> s)"
      then have "s \<noteq> \<epsilon>"
        by force
      then have ?thesis
        using f5 f4 f2 a1 by (simp add: surj_scons) }
    then show ?thesis
      by fastforce
  qed
  then show ?case
    using f2 by fastforce
qed

lemma srcdups_imposs_h:"Fin 1 < #(srcdups\<cdot>s) \<Longrightarrow> shd(srcdups\<cdot>s)\<noteq>shd(srt\<cdot>(srcdups\<cdot>s))"
  apply (cases "s=\<epsilon>", simp)
  apply (subst srcdups_srt2,auto)
  apply (subgoal_tac "srcdups\<cdot>(sdropwhile (\<lambda>z. z = shd s)\<cdot>(srt\<cdot>s))\<noteq>\<epsilon>")
  apply (metis (mono_tags, lifting) sdropwhile_resup srcdups_shd2 strict_srcdups surj_scons)
proof -
  assume a1: "s \<noteq> \<epsilon>"
  assume a2: "Fin (Suc 0) < #(srcdups\<cdot>s)"
  have "Fin 0 = 0"
    using Fin_02bot bot_is_0 by presburger
  then have "lnsuc\<cdot>0 = Fin (Suc 0)"
    by (metis Fin_Suc)
  then show "srcdups\<cdot> (sdropwhile (\<lambda>a. a = shd s)\<cdot>(srt\<cdot>s)) \<noteq> \<epsilon>"
    using a2 a1 by (metis (no_types) lnless_def lscons_conv scases slen_empty_eq slen_scons srcdups_ex srcdups_srt2 stream.sel_rews(5) up_defined)
qed

lemma srcdups_imposs:"srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> y"
  apply(cases "#(srcdups\<cdot>(\<up>a \<bullet>s)) < Fin 1 ")  
  apply (metis One_nat_def bot_is_0 lnat.con_rews neq02Suclnle not_less slen_scons)
  apply(insert srcdups_imposs_h[of "\<up>a\<bullet> s"])
  by (metis Fin_02bot Fin_Suc One_nat_def lnat.con_rews lnat.sel_rews(2) lscons_conv neq_iff shd1 
      slen_scons stream.sel_rews(5) up_defined)  
  
lemma srcdupsimposs: "srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> srcdups\<cdot>s"
  by (simp add: srcdups_imposs)
   
lemma srcdupsimposs2_h2:"\<forall>x. srcdups\<cdot>(\<up>a \<bullet> s)\<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
  by (simp add: srcdups_imposs)
 
lemma srcdupsimposs2: "srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> s"
  by(simp add: srcdups_imposs) 
    
lemma srcdups_anotb_h:"srcdups\<cdot>(\<up>a\<bullet>\<up>b) = \<up>a \<bullet> \<up>b \<Longrightarrow> a \<noteq> b"
  by (metis lscons_conv srcdups_eq2 stream.con_rews(2) stream.sel_rews(5) sup'_def tsabs_bot 
     tsremdups_h_strict tsremdups_h_tsabs up_defined)
  
lemma srcdups_anotb:"srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s) = \<up>a \<bullet> \<up>b \<bullet> s \<Longrightarrow> a\<noteq> b"
  using srcdupsimposs2_h2 by auto


lemma srcdups_prefix_neq:"x \<sqsubseteq> y \<Longrightarrow> srcdups\<cdot>x \<noteq>x \<Longrightarrow> srcdups\<cdot>y \<noteq> y"
proof(induction arbitrary: y rule: ind [of _ x])
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case
      by simp
  next
    case (3 a s)
    have f1:"a=shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = srcdups\<cdot>s"
      by (metis "3.prems"(2) srcdups_eq2 srcdups_shd srcdups_srt strict_sdropwhile strict_srcdups surj_scons)
    have f2:"a\<noteq>shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>s"
      by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
    then have f3:"a\<noteq>shd s\<Longrightarrow> srcdups\<cdot>s \<noteq> s"
      using "3.prems" by auto
    show ?case
      by (smt "3.IH" "3.prems"(1) f1 f2 f3 less_fst_sconsD lscons_conv scases srcdups2srcdups 
         srcdups_eq srcdups_ex srcdups_srt srcdupsimposs2 stream.con_rews(2) stream.sel_rews(5) 
         sup'_def surj_scons)
qed

lemma srcdups_smap_adm [simp]: 
  "adm (\<lambda>a. srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>a)) = smap f\<cdot>(srcdups\<cdot>a) 
    \<longrightarrow> srcdups\<cdot>(smap f\<cdot>a) = smap f\<cdot>(srcdups\<cdot>a))"
  apply (rule adm_imp, auto)
  apply(rule adm_upward)
  apply rule+
  using srcdups_prefix_neq
  by (metis monofun_cfun_arg)
    
lemma srcdups_smap_com_h:"s\<noteq>\<epsilon> \<Longrightarrow> a \<noteq> shd s \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s))) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)) \<Longrightarrow>f (shd s) \<noteq> f a"
  apply(cases "shd(srt\<cdot>s) \<noteq> shd s")
  apply (insert srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s], simp)
  apply (metis smap_scons srcdups_ex srcdupsimposs2_h2)
  apply (insert srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s], simp)
  apply(insert srcdups_ex[of "shd s" "srt\<cdot>s"],auto)
  by (simp add: srcdupsimposs2_h2)

declare [[show_types]]
(* ToDo: Move to Streams.thy after done *)
lemma srcdups_smap_com:
  shows "srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>s)) = smap f\<cdot>(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>s)= smap f\<cdot>(srcdups\<cdot>s)"
  proof(induction rule: ind [of _ s])
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    have s_eps: "s = \<bottom> \<Longrightarrow>  srcdups\<cdot>(\<up>(f a) \<bullet> smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s))" by simp
    hence f1: "shd s = a \<Longrightarrow> ?case"  
      by (metis "3.IH" "3.prems" smap_scons srcdups_eq surj_scons)
    have h1: "s\<noteq>\<bottom> \<Longrightarrow> s = (\<up>(shd s) \<bullet> srt\<cdot>s)" by (simp add: surj_scons)
    have h2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>(\<up>a \<bullet> (\<up>(shd s) \<bullet> srt\<cdot>s))) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet>  (\<up>(shd s) \<bullet> srt\<cdot>s)))"
    proof -
      assume a1: "f (shd s) \<noteq> f a"
      assume a2: "s \<noteq> \<epsilon>"
      assume a3: "shd s \<noteq> a"
      have f4: "s = \<up>(shd s) \<bullet> srt\<cdot>s"
        using a2 by (metis h1)
      obtain ss :: "'b stream \<Rightarrow> 'b \<Rightarrow> 'b stream" where
        f5: "\<forall>b s. srcdups\<cdot>(\<up>b \<bullet> s) = \<up>b \<bullet> ss s b"
        by (meson srcdups_ex)
      then have f6: "\<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s) = srcdups\<cdot>s"
        using f4 by metis
      have f7: "srcdups\<cdot> (\<up>(f a) \<bullet> \<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s))) = \<up>(f a) \<bullet> srcdups\<cdot> (\<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s)))"
        using a1 by auto
      have f8: "\<up>a \<bullet> \<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s) = srcdups\<cdot>(\<up>a \<bullet> \<up>(shd s) \<bullet> srt\<cdot>s)"
        using f5 a3 by (metis (no_types) srcdups_neq)
      then have f9: "\<up>(f a) \<bullet> \<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s)) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s))"
        using f4 by (metis (no_types) smap_scons)
      then obtain ssa :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
        f10: "\<up>(f a) \<bullet> ssa (\<up>(f (shd s)) \<bullet> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)))"
        by (simp add: "3.prems")
      then have f11: "\<up>(f a) \<bullet> ssa (\<up>(f (shd s)) \<bullet> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = srcdups\<cdot> (\<up>(f a) \<bullet> \<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s)))"
        using f9 by presburger
      have "\<up>(f a) \<bullet> ssa (\<up>(f (shd s)) \<bullet> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = \<up>(f a) \<bullet> smap f\<cdot>(srcdups\<cdot>s)"
        using f10 f8 f6 f4 by (metis (no_types) "3.prems" smap_scons)
      then have "srcdups\<cdot>(smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>s)"
        using f11 f7 f6 by (metis (no_types) "3.IH" inject_scons smap_scons)
      then have "srcdups\<cdot> (smap f\<cdot>(\<up>a \<bullet> \<up>(shd s) \<bullet> srt\<cdot>s)) = smap f\<cdot> (\<up>a \<bullet> \<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s))"
        using f6 f4 a1 by (metis (no_types) smap_scons srcdups_neq)
      then show ?thesis
        using f8 by presburger
    qed
    have f2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> ?case"
      using h1 h2 by auto
    have f3: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) = f a \<Longrightarrow> ?case"
      by (simp add: "3.prems" srcdups_smap_com_h)
    then show ?case using f1 f2 by fastforce
  qed
    
lemma tssnd_tsprojsnd_tsremdups: 
  assumes send_def: "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  apply (simp add: tsprojsnd_tsabs tsremdups_tsabs sprojsnd_def)
  by (metis eta_cfun send_def set2tssnd_alt_bit_tabs sprojsnd_def srcdups_smap_com)
    
lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks_def: "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))"
    by (metis acks_def out_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
        tssnd_tsprojsnd_tsremdups send_def)
  thus "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis eq_slen_eq_and_less min_rek out_def send_def set2tssnd_ack2trans 
        set2tssnd_prefix_inp tsrecsnd_insert)
  qed

(* ----------------------------------------------------------------------- *)
subsection {* sender, receiver and second medium composition *}
(* ----------------------------------------------------------------------- *)

lemma tsaltbitpro_inp2out_sndmed_shd:
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "shd (tsAbs\<cdot>(tsRecSnd\<cdot>ds)) = shd (tsAbs\<cdot>i)"
  by (metis below_shd bot_is_0 eq_slen_eq_and_less lnat.con_rews min_def out_def send_def 
      set2tssnd_ack2trans set2tssnd_prefix_inp strict_slen tsrecsnd_insert)

text {*
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   p2 = oracle stream
*}

lemma tsaltbitpro_inp2out_nmed2:
  assumes send_def: "send \<in> tsSender"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks_def: "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRecSnd\<cdot>ds))"
    by (metis acks_def eq_iff out_def send_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
        tsrecsnd_insert tssnd_tsprojsnd_tsremdups)
  hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
    by (metis le_less less_imp_le min_less_iff_conj min_rek out_def send_def set2tssnd_ack2trans
        tsrecsnd_insert)
  have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) 
              \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
    by (metis le_less_linear min_absorb2 send_def set2tssnd_ack2trans)
  hence h4: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> (#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>)"
    by (metis acks_def eq_iff min_rek out_def send_def set2tssnd_ack2trans tsprojfst_tsabs_slen 
        tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
  hence h5: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>"
    by (metis acks_def leI neq_iff out_def send_def set2tssnd_nack2inftrans tsprojsnd_tsabs_slen)
  hence h6: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<ge> #(tsAbs\<cdot>i)"
    by auto
  show "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis dual_order.antisym eq_slen_eq_and_less h2 h6 less_lnsuc min.absorb1 out_def send_def
        set2tssnd_ack2trans set2tssnd_prefix_inp tsrecsnd_insert)
  qed

lemma tsaltbitpro_inp2out_sndmed_assm:
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
    and "#(tsAbs\<cdot>ds) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>"
proof -
  have ora_inf: "#p2 = \<infinity>"
    using ora_def sfilterl4 by auto
  hence tsmed_tsprojsnd: "tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p2 = tsProjSnd\<cdot>(tsMed\<cdot>ds\<cdot>p2)"
    by (simp add: tsprojsnd_insert tsmed_map)
  thus "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>"
    apply (simp add: acks2snd_def acks2med_def)
    sorry
  qed

lemma tssnd_tsprojsnd_tsremdups_med: 
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>(send\<cdot>i\<cdot>as)\<cdot>p2))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(send\<cdot>i\<cdot>as)\<cdot>p2)))"
  sorry

(* oops-Lemmata in Medium *)
text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  sorry

lemma tsaltbitpro_inp2out_sndmed:
  assumes send_def: "send \<in> tsSender"
(*
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)
*)
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have ora_inf: "#p2 = \<infinity>"
    using ora_def sfilterl4 by auto
  hence tsmed_tsprojsnd: "tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p2 = tsProjSnd\<cdot>(tsMed\<cdot>ds\<cdot>p2)"
    by (simp add: tsprojsnd_insert tsmed_map)
  have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRecSnd\<cdot>ds))"
    apply (simp add: acks2med_def acks2snd_def tsmed_tsprojsnd tsrecsnd_insert)
    apply (subst out_def)
    apply (subst tssnd_tsprojsnd_tsremdups_med)
    apply (simp_all add: send_def ora_def)
    apply (subst out_def)
    sorry
  hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
    by (metis le_less less_imp_le min_less_iff_conj min_rek out_def send_def set2tssnd_ack2trans
        tsrecsnd_insert)
  
  have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) 
              \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
    by (metis le_less_linear min_absorb2 send_def set2tssnd_ack2trans)
  hence h4: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> (#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>)"
    by (metis acks2med_def acks2snd_def leI ora_def out_def send_def set2tssnd_nack2inftrans 
        tsaltbitpro_inp2out_sndmed_assm)
  hence h5: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>"
    using acks2med_def acks2snd_def le_less_linear neq_iff ora_def out_def send_def set2tssnd_nack2inftrans by fastforce
  hence h6: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<ge> #(tsAbs\<cdot>i)"
    by auto
  show "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis dual_order.antisym eq_slen_eq_and_less h2 h6 less_lnsuc min.absorb1 out_def send_def
        set2tssnd_ack2trans set2tssnd_prefix_inp tsrecsnd_insert)
  oops
    
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
  assumes "send \<in> tsSender"
    and "#({True} \<ominus> p1) = \<infinity>"
    and "#({True} \<ominus> p2) = \<infinity>"
    and "ds = send\<cdot>i\<cdot>as"
    and "dr = tsMed\<cdot>ds\<cdot>p1"
    and "ar = tsProjSnd\<cdot>dr"
    and "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>dr) = tsAbs\<cdot>i"
  oops
    
end