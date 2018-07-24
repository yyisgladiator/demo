(*  Title:        Receiver.thy
    Author:       Marlene Lutz, Dennis Slotboom
    E-Mail:       marlene.lutz@rwth-aachen.de, dennis.slotboom@rwth-aachen.de

    Description:  Theory for Receiver Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for Receiver Lemmata on Time-synchronous Streams *}

theory Receiver_2ndMedLoses
imports Receiver

begin

lemma natbool2abp2natbool: "abp2natbool\<cdot>(natbool2abp\<cdot>recTestInputStreamLoseAck) = recTestInputStreamLoseAck"
  apply (simp add: recTestInputStreamLoseAck_def)
  apply (simp add: abp2natbool_def natbool2abp_def)
  by (simp add: tsynmap_sconc_msg tsynmap_singleton_msg)

lemma tsynrec_ar: "bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(recTestInputUbundleLoseAck  .  \<C> ''dr''))) = bool2abp\<cdot>recTestOutputStreamArLoseAck"
  sorry

lemma secondMedLoses_Stream: "tsynRec\<cdot>recTestInputStreamLoseAck = recTestOutputStreamOLoseAck"
  apply (simp add: recTestInputStreamLoseAck_def recTestOutputStreamOLoseAck_def)
  apply (simp add: tsynrec_sconc_msg_t)
  done

lemma tsynrec_nat: "nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(recTestInputUbundleLoseAck  .  \<C> ''dr''))) = nat2abp\<cdot>recTestOutputStreamOLoseAck"
  proof -
    have h0: "recTestInputUbundleLoseAck  .  \<C> ''dr'' = natbool2abp\<cdot>recTestInputStreamLoseAck"
      by (metis fun_upd_same option.sel recTestInputUbundleLoseAck.rep_eq ubgetch_insert)
    have h1: "abp2natbool\<cdot>(recTestInputUbundleLoseAck  .  \<C> ''dr'') = recTestInputStreamLoseAck"
      using abp2natbool_def natbool2abp2natbool h0 recTestInputStreamLoseAck_def recTestInputUbundleLoseAck_def by auto
    then show ?thesis
      by (simp add: secondMedLoses_Stream)
  qed

lemma secondMedLoses_SB: "tsynbRec\<cdot>recTestInputUbundleLoseAck = Some recTestOutputUbundleLoseAck"
  apply (simp add: tsynbrec_insert)
  by (simp add: fun_upd_twist recTestInputUbundleLoseAck.rep_eq recTestOutputUbundleLoseAck_def tsynrec_ar tsynrec_nat ubdom_insert)

lemma secondMedLoses_SPF: "RecSPF \<rightleftharpoons> recTestInputUbundleLoseAck = recTestOutputUbundleLoseAck"
  by (simp add: RecSPF_def secondMedLoses_SB)

end
