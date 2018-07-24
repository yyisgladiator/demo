(*  Title:        Receiver_2ndMedLoses.thy
    Author:       Shi Chen Niu
    E-Mail:       shi.chen.niu@rwth-aachen.de, dennis.slotboom@rwth-aachen.de

    Description:  CaseStudy for Receiver; case: The second medium loses the first acknowledgement.
*)

theory Receiver_2ndMedLoses
imports Receiver

begin

lemma natbool2abp2natbool: "abp2natbool\<cdot>(natbool2abp\<cdot>recTestInputStreamLoseAck) = recTestInputStreamLoseAck"
  apply (simp add: recTestInputStreamLoseAck_def)
  apply (simp add: abp2natbool_def natbool2abp_def)
  by (simp add: tsynmap_sconc_msg tsynmap_singleton_msg)

lemma abp_inputChannel: "abp2natbool\<cdot>(recTestInputUbundleLoseAck  .  \<C> ''dr'') = recTestInputStreamLoseAck"
  proof -
    have h1: "recTestInputUbundleLoseAck  .  \<C> ''dr'' = natbool2abp\<cdot>recTestInputStreamLoseAck"
      by (metis fun_upd_same option.sel recTestInputUbundleLoseAck.rep_eq ubgetch_insert)
    then show ?thesis
      using abp2natbool_def natbool2abp2natbool h1 recTestInputStreamLoseAck_def recTestInputUbundleLoseAck_def by auto
  qed

lemma secondMedLoses_StreamO: "tsynRec\<cdot>recTestInputStreamLoseAck = recTestOutputStreamOLoseAck"
  apply (simp add: recTestInputStreamLoseAck_def recTestOutputStreamOLoseAck_def)
  apply (simp add: tsynrec_sconc_msg_t)
  done

lemma tsynrec_O: "nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(recTestInputUbundleLoseAck  .  \<C> ''dr''))) = nat2abp\<cdot>recTestOutputStreamOLoseAck"
  by (simp add: abp_inputChannel secondMedLoses_StreamO)

lemma tsynrec_ar: "bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(recTestInputUbundleLoseAck  .  \<C> ''dr''))) = bool2abp\<cdot>recTestOutputStreamArLoseAck"
  apply (simp add: abp_inputChannel recTestInputStreamLoseAck_def recTestOutputStreamArLoseAck_def)
  by (metis lscons_conv sup'_def tsynprojsnd_sconc_msg tsynprojsnd_strict)

lemma secondMedLoses_SB: "tsynbRec\<cdot>recTestInputUbundleLoseAck = Some recTestOutputUbundleLoseAck"
  apply (simp add: tsynbrec_insert)
  by (simp add: fun_upd_twist recTestInputUbundleLoseAck.rep_eq recTestOutputUbundleLoseAck_def tsynrec_ar tsynrec_O ubdom_insert)

lemma secondMedLoses_SPF: "RecSPF \<rightleftharpoons> recTestInputUbundleLoseAck = recTestOutputUbundleLoseAck"
  by (simp add: RecSPF_def secondMedLoses_SB)

end
