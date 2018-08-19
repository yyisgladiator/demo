(*  Title:        Receiver.thy
    Author:       Marlene Lutz, Dennis Slotboom
    E-Mail:       marlene.lutz@rwth-aachen.de, dennis.slotboom@rwth-aachen.de

    Description:  Theory for Receiver Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for Receiver Lemmata on Time-synchronous Streams *}

theory Receiver
imports ReceiverAutomaton Components "../../../UBundle_Induction" Adm

begin

(* ----------------------------------------------------------------------- *)
  section {* Receiver Test Streams and Bundles *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
  subsection {* Test situation in which no message gets lost. *}
(* ----------------------------------------------------------------------- *)

text{* Input stream of the Receiver. *}
definition recTestInputStreamNoLoss :: "(nat \<times> bool) tsyn stream" where 
  "recTestInputStreamNoLoss \<equiv> <[Msg (1, True), Msg (2, False)]>"

text{* Input bundle of the Receiver. *}
lift_definition recTestInputUbundleNoLoss :: "abpMessage tsyn SB" is
  "[\<C> ''dr'' \<mapsto> natbool2abp\<cdot>recTestInputStreamNoLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestInputStreamNoLoss_def
      natbool2abp_def tsynMap_def)

text{* Output bool stream of the Receiver. *}
definition recTestOutputStreamArNoLoss :: "bool tsyn stream" where 
  "recTestOutputStreamArNoLoss \<equiv> <[Msg True, Msg False]>"

text{* Output nat stream of the Receiver. *}
definition recTestOutputStreamONoLoss :: "nat tsyn stream" where 
  "recTestOutputStreamONoLoss \<equiv> <[Msg 1, Msg 2]>"

text{* Output bundle of the Receiver. *}
lift_definition recTestOutputUbundleNoLoss :: "abpMessage tsyn SB" is
  "[\<C> ''o'' \<mapsto> nat2abp\<cdot>recTestOutputStreamONoLoss, \<C> ''ar'' \<mapsto> bool2abp\<cdot>recTestOutputStreamArNoLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestOutputStreamArNoLoss_def
      recTestOutputStreamONoLoss_def bool2abp_def nat2abp_def tsynMap_def rangeI)

(* ----------------------------------------------------------------------- *)
  subsection {* The second medium loses the first acknowledgement. *}
(* ----------------------------------------------------------------------- *)

text{* Input stream of the Receiver. *}
definition recTestInputStreamLoseAck :: "(nat \<times> bool) tsyn stream" where 
  "recTestInputStreamLoseAck \<equiv> <[Msg (1, True), Msg (1, True), Msg (2, False)]>"

text{* Input bundle of the Receiver. *}
lift_definition recTestInputUbundleLoseAck :: "abpMessage tsyn SB" is
  "[\<C> ''dr'' \<mapsto> natbool2abp\<cdot>recTestInputStreamLoseAck]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestInputStreamLoseAck_def
      natbool2abp_def tsynMap_def)

text{* Output bool stream of the Receiver. *}
definition recTestOutputStreamArLoseAck :: "bool tsyn stream" where 
  "recTestOutputStreamArLoseAck \<equiv> <[Msg True, Msg True, Msg False]>"

text{* Output nat stream of the Receiver. *}
definition recTestOutputStreamOLoseAck :: "nat tsyn stream" where 
  "recTestOutputStreamOLoseAck \<equiv> <[Msg 1, null, Msg 2]>"

text{* Output bundle of the Receiver. *}
lift_definition recTestOutputUbundleLoseAck :: "abpMessage tsyn SB" is
  "[\<C> ''o'' \<mapsto> nat2abp\<cdot>recTestOutputStreamOLoseAck, \<C> ''ar'' \<mapsto> bool2abp\<cdot>recTestOutputStreamArLoseAck]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestOutputStreamOLoseAck_def
      recTestOutputStreamArLoseAck_def bool2abp_def nat2abp_def tsynMap_def rangeI)

(* ----------------------------------------------------------------------- *)
  subsection {* The first medium loses the first and second data message for one time each. *}
(* ----------------------------------------------------------------------- *)

text{* Input stream of the Receiver. *}
definition recTestInputStreamLoseDat :: "(nat \<times> bool) tsyn stream" where 
  "recTestInputStreamLoseDat \<equiv> <[null, Msg (1, True), null, Msg (2, False)]>"

text{* Input bundle of the Receiver. *}
lift_definition recTestInputUbundleLoseDat :: "abpMessage tsyn SB" is
  "[\<C> ''dr'' \<mapsto> natbool2abp\<cdot>recTestInputStreamLoseDat]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestInputStreamLoseDat_def 
      natbool2abp_def tsynMap_def)

text{* Output bool stream of the Receiver. *}
definition recTestOutputStreamArLoseMsg :: "bool tsyn stream" where 
  "recTestOutputStreamArLoseMsg \<equiv> <[null, Msg True, null, Msg False]>"

text{* Output nat stream of the Receiver. *}
definition recTestOutputStreamOLoseMsg :: "nat tsyn stream" where 
 "recTestOutputStreamOLoseMsg \<equiv> <[null, Msg 1, null, Msg 2]>"

text{* Output bundle of the Receiver. *}
lift_definition recTestOutputUbundleLoseMsg :: "abpMessage tsyn SB" is
  "[\<C> ''o'' \<mapsto> nat2abp\<cdot>recTestOutputStreamOLoseMsg, 
    \<C> ''ar'' \<mapsto> bool2abp\<cdot>recTestOutputStreamArLoseMsg]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestOutputStreamArLoseMsg_def
      recTestOutputStreamOLoseMsg_def bool2abp_def nat2abp_def tsynMap_def rangeI)

(* ----------------------------------------------------------------------- *)
  section {* Receiver SPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text {* Helper for @{term tsynRec} deletes elements if bits are not equal. *}
fun tsynRec_h :: "bool \<Rightarrow> (nat \<times> bool) tsyn \<Rightarrow> (nat tsyn \<times> bool)" where
  "tsynRec_h b (Msg (msg,b1)) = (if b1 = b then (Msg msg, \<not>b) else (null, b))" |
  "tsynRec_h b null = (null, b)" 

text {* @{term tsynRec}: Applies helper function on each element of the stream. *}
definition tsynRec :: "bool \<Rightarrow> (nat \<times> bool) tsyn stream \<rightarrow> nat tsyn stream" where
  "tsynRec b \<equiv> \<Lambda> s. sscanlA tsynRec_h b\<cdot>s"

text {* @{term tsynbRec}: Receiver function for Alternating Bit Protocol on stream bundles. *}
definition tsynbRec :: 
  "bool \<Rightarrow> abpMessage tsyn stream ubundle \<rightarrow> abpMessage tsyn stream ubundle option" where 
  "tsynbRec b \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle [
                     \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
                     \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))
                     ]"

text {* @{term tsynbRec}: Receiver function for Alternating Bit Protocol. *}
definition RecSPF :: "bool \<Rightarrow> abpMessage tsyn SPF" where
  "RecSPF b \<equiv> Abs_ufun (tsynbRec b)"

(* ----------------------------------------------------------------------- *)
  section {* Receiver SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynRec} insertion lemma. *}
lemma tsynrec_insert: "tsynRec b\<cdot>s = sscanlA tsynRec_h b\<cdot>s"
  by (simp add: tsynRec_def)

text {* @{term tsynRec} maps the empty (nat x bool) tsyn stream on the empty nat tsyn stream. *}
lemma tsynrec_strict [simp]: "tsynRec b\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} does not distribute directly over concatenation, when the first element 
        is a message with True bit. *}
lemma tsynrec_sconc_msg_t: "tsynRec b\<cdot>(\<up>(Msg (m, b)) \<bullet> s) = \<up>(Msg m) \<bullet> (sscanlA tsynRec_h (\<not>b)\<cdot>s)"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} distributes over concatenation, when the first element 
        is a message with False bit. *}
lemma tsynrec_sconc_msg_f: "tsynRec b\<cdot>(\<up>(Msg (m, \<not>b)) \<bullet> s) = \<up>(null) \<bullet> tsynRec b\<cdot>s"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} distributes over concatenation, when concatenating a null. *}
lemma tsynrec_sconc_null: "tsynRec b\<cdot>(\<up>(null) \<bullet> s) = \<up>(null) \<bullet> tsynRec b\<cdot>s"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} leaves the length of a stream unchanged. *}
lemma tsynrec_slen: "#(tsynRec b\<cdot>s) = #s"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} test on finite stream. *}
lemma tsynrec_test_finstream:
  "tsynRec True\<cdot>(<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>) = <[null, null,\<M> 2, \<M> 1]>"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} test on infinite stream. *}
lemma tsynrec_test_infstream: 
  "tsynRec True\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>) 
     = (<[null, null, \<M> 2, \<M> 1]>)\<infinity>"
  proof -
    have inf_unfold: 
      "tsynRec True\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>) 
                      \<bullet> ((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>))
         = <[null, null,\<M> 2, \<M> 1]> 
             \<bullet> tsynRec True\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)" 
      by (simp add: tsynrec_insert)
    have "((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>) 
            \<bullet> ((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)) 
            = ((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>) "
      using sinftimes_unfold by metis
    hence "tsynRec True\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)
             = <[null, null,\<M> 2, \<M> 1]> 
                 \<bullet> tsynRec True\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)" 
      using inf_unfold by metis
    thus ?thesis 
      by (simp add: rek2sinftimes)
  qed

text{* The output bundle of @{term tsynbRec} is well-formed. *}
lemma tsynbrec_ubwell [simp]:
 "ubWell [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(x  .  \<C> ''dr''))),
          \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(x  .  \<C> ''dr'')))]"
  apply (rule ubwellI)
  apply (simp add: usclOkay_stream_def ctype_tsyn_def)
  apply (rename_tac y)
  apply (case_tac "y = \<C> ''o''", simp_all)
  apply (simp add: nat2abp_def tsynabs_sdom_subset_eq tsynmap_tsynabs)
  by (simp add: bool2abp_def tsynabs_sdom_subset_eq tsynmap_tsynabs)

text{* The domain of the output bundle of @{term tsynbRec}. *}
lemma tsynbrec_ubundle_ubdom: 
  "ubDom\<cdot>(Abs_ubundle 
     [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
      \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))]) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: ubDom_def insert_commute)

text{* @{term tsynbRec} is monotonous. *}
lemma tsynbrec_mono [simp]:
  "monofun (\<lambda> sb. (ubDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle [
                     \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
                     \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))])"
  apply (fold ubclDom_ubundle_def)
  apply (rule ufun_monoI2)
  by (simp add: below_ubundle_def cont_pref_eq1I fun_belowI some_below)

(* ToDo: add description. *)

lemma tsynbrec_chain:
  assumes "chain Y"
  shows "chain (\<lambda>i. [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''dr''))),
                     \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''dr'')))])"
  apply (rule chainI)
  by (simp add: assms fun_below_iff monofun_cfun_arg po_class.chainE some_below)

text{* @{term tsynbRec} is continuous. *}
lemma tsynbrec_cont [simp]:
  "cont (\<lambda> sb. (ubDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle [
                  \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
                  \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))])"
  apply (fold ubclDom_ubundle_def)
  apply (rule ufun_contI2)
  apply (rule cont_Abs_UB)
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: below_ubundle_def cont_pref_eq1I fun_belowI some_below)
  by (simp_all add: tsynbrec_chain contlub_cfun_arg fun_below_iff some_lub_chain_eq lub_fun)

text{* @{term tsynbRec} insertion lemma. *}
lemma tsynbrec_insert: 
  "tsynbRec b\<cdot>sb = (ubDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle 
     [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
      \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))]"
  by (simp add: tsynbRec_def ubclDom_ubundle_def)

text{* @{term tsynbRec} is well-formed. *}
lemma tsynbrec_ufwell [simp]: "ufWell (tsynbRec b)"
  apply (rule ufun_wellI [of "tsynbRec b" "{\<C> ''dr''}" "{\<C> ''ar'', \<C> ''o''}"])
  by (simp_all add: tsynbRec_def domIff2 ubclDom_ubundle_def tsynbrec_ubundle_ubdom)

text{* The domain of the output bundle of@{term tsynbRec}. *}
lemma tsynbrec_ubdom: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
  shows "ubDom\<cdot>((Rep_cfun (tsynbRec b)) \<rightharpoonup> sb) =  {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: tsynbrec_insert assms)
  by (simp add: ubDom_def insert_commute)

text {* The output stream of @{term tsynbRec}} on channel ar. *}
lemma tsynbrec_getch_ar:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "((Rep_cfun (tsynbRec b)) \<rightharpoonup> sb) . \<C> ''ar'' = 
          bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))"
  by (simp add: tsynbrec_insert assms ubgetch_ubrep_eq)

text {* The output stream of @{term tsynbRec} on channel o. *}
lemma tsynbrec_getch_o:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
  shows "((Rep_cfun (tsynbRec b)) \<rightharpoonup> sb) . \<C> ''o'' 
           = nat2abp\<cdot>(tsynRec b\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))"
  by (simp add: tsynbrec_insert assms ubgetch_ubrep_eq)

text{* @{term tsynbRec} is strict. *}
lemma tsynbrec_strict: "(Rep_cfun (tsynbRec b)) \<rightharpoonup> ubLeast {\<C> ''dr''} = ubLeast {\<C> ''ar'', \<C> ''o''}"
  apply (rule ub_eq)
  apply (simp_all add: tsynbrec_ubdom)
  apply (rename_tac x)
  apply (case_tac "x = \<C> ''ar''")
  by (simp_all add: tsynbrec_getch_ar tsynbrec_getch_o abp2natbool_def nat2abp_def bool2abp_def)

text{* @{term RecSPF} insertion lemma. *}
lemma recspf_insert: "RecSPF b \<rightleftharpoons> sb = (Abs_ufun (tsynbRec b)) \<rightleftharpoons> sb"
  by (simp add: RecSPF_def)

text{* @{term RecSPF} is strict. *}
lemma recspf_strict: "RecSPF b \<rightleftharpoons> ubLeast{\<C> ''dr''} = ubLeast{\<C> ''ar'', \<C> ''o''}"
  by(simp add: recspf_insert tsynbrec_strict)

text{* The domain of @{term RecSPF}. *}
lemma recspf_ufdom: "ufDom\<cdot>(RecSPF b) = {\<C> ''dr''}"
  proof -
    have "ufDom\<cdot>(Abs_ufun (tsynbRec b)) = ubclDom\<cdot>(ubLeast {\<C> ''dr''} :: abpMessage tsyn stream\<^sup>\<Omega>)"
      by (simp add: tsynbrec_insert)
    then show ?thesis
      by (simp add: RecSPF_def ubclDom_ubundle_def)
  qed
  
text{* The range of @{term RecSPF}. *}
lemma recspf_ufran: "ufRan\<cdot>(RecSPF b) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: ufran_least recspf_ufdom ubclDom_ubundle_def ubclLeast_ubundle_def recspf_strict)

text{* The domain of the output bundle of @{term tsynbRec}. *}
lemma recspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>(RecSPF b)"
  shows "ubDom\<cdot>((RecSPF b) \<rightleftharpoons> sb) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: assms recspf_ufran spf_ubDom)

(* ----------------------------------------------------------------------- *)
  section {* Receiver SPF Test Lemmata *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
  subsection {* Test situation in which no message gets lost. *}
(* ----------------------------------------------------------------------- *)
  
text{* @{term tsynRec} test on @{term recTestInputStreamNoLoss}. *}
lemma tsynrec_test_inputstreamnoloss:
  "tsynRec True\<cdot>recTestInputStreamNoLoss = recTestOutputStreamONoLoss"
  by (simp add: tsynrec_insert recTestInputStreamNoLoss_def recTestOutputStreamONoLoss_def)

text{* @{term tsynProjSnd} of @{term recTestInputStreamNoLoss}. *}
lemma tsynprojsnd_test_inputstreamnoloss: 
  "tsynProjSnd\<cdot>recTestInputStreamNoLoss = recTestOutputStreamArNoLoss"
  by (simp add: recTestInputStreamNoLoss_def recTestOutputStreamArNoLoss_def tsynprojsnd_insert)

text{* @{term tsynbRec} test on @{term recTestInputUbundleNoLoss}. *}
lemma tsynbrec_test_inputubundlenoloss:
  "tsynbRec True\<cdot>recTestInputUbundleNoLoss = Some recTestOutputUbundleNoLoss"
   by (simp add: tsynbrec_insert ubdom_insert ubgetch_insert natbool2abp_abp2natbool_inv 
                tsynrec_test_inputstreamnoloss tsynprojsnd_test_inputstreamnoloss 
                recTestInputUbundleNoLoss.rep_eq recTestOutputUbundleNoLoss.abs_eq fun_upd_twist)

text{* @{term RecSPF} test on @{term recTestInputUbundleNoLoss}. *}
lemma recspf_test_inputubundlenoloss:
  "RecSPF True \<rightleftharpoons> recTestInputUbundleNoLoss = recTestOutputUbundleNoLoss"
  by (simp add: RecSPF_def tsynbrec_test_inputubundlenoloss)

(* ----------------------------------------------------------------------- *)
  subsection {* The second medium loses the first acknowledgement. *}
(* ----------------------------------------------------------------------- *)

text{* @{term tsynRec} test on @{term recTestInputStreamLoseAck}. *}
lemma tsynrec_test_inputstreamloseack:
  "tsynRec True\<cdot>recTestInputStreamLoseAck = recTestOutputStreamOLoseAck"
  by(simp add: recTestInputStreamLoseAck_def recTestOutputStreamOLoseAck_def tsynrec_insert)

text{* @{term tsynProjSnd} of @{term recTestInputStreamLoseAck}. *}
lemma tsynprojsnd_test_inputstreamloseack: 
  "tsynProjSnd\<cdot>recTestInputStreamLoseAck = recTestOutputStreamArLoseAck"
  by (simp add: recTestInputStreamLoseAck_def recTestOutputStreamArLoseAck_def tsynprojsnd_insert)

text{* @{term tsynbRec} test on @{term recTestInputUbundleLoseAck}. *}
lemma tsynbrec_test_inputubundleloseack: 
  "tsynbRec True\<cdot>recTestInputUbundleLoseAck = Some recTestOutputUbundleLoseAck"
  by (simp add: tsynbrec_insert ubdom_insert ubgetch_insert natbool2abp_abp2natbool_inv 
                tsynrec_test_inputstreamloseack tsynprojsnd_test_inputstreamloseack 
                recTestInputUbundleLoseAck.rep_eq recTestOutputUbundleLoseAck.abs_eq fun_upd_twist)

text{* @{term RecSPF} test on @{term recTestInputUbundleLoseAck}. *}
lemma recspf_test_inputubundleloseack:
  "RecSPF True \<rightleftharpoons> recTestInputUbundleLoseAck = recTestOutputUbundleLoseAck"
  by (simp add: recspf_insert tsynbrec_test_inputubundleloseack)

(* ----------------------------------------------------------------------- *)
  subsection {* The first medium loses the first and second data message for one time each. *}
(* ----------------------------------------------------------------------- *)

text{* @{term tsynRec} test on @{term recTestInputStreamLoseDat}. *}
lemma tsynrec_test_inputstreamlosedat:
  "tsynRec True\<cdot>recTestInputStreamLoseDat = recTestOutputStreamOLoseMsg" 
  by (simp add: recTestInputStreamLoseDat_def recTestOutputStreamOLoseMsg_def tsynrec_insert)

text{* @{term tsynProjSnd} of @{term recTestInputStreamLoseDat}. *}
lemma tsynprojsnd_test_inputstreamlosedat: 
  "tsynProjSnd\<cdot>recTestInputStreamLoseDat = recTestOutputStreamArLoseMsg"
  by (simp add: recTestInputStreamLoseDat_def recTestOutputStreamArLoseMsg_def tsynprojsnd_insert)

text{* @{term tsynbRec} test on @{term recTestInputUbundleLoseDat}. *}
lemma tsynbrec_test_inputubundlelosedat: 
  "tsynbRec True\<cdot>recTestInputUbundleLoseDat = Some recTestOutputUbundleLoseMsg"
    by (simp add: tsynbrec_insert ubdom_insert ubgetch_insert natbool2abp_abp2natbool_inv 
                tsynrec_test_inputstreamlosedat tsynprojsnd_test_inputstreamlosedat 
                recTestInputUbundleLoseDat.rep_eq recTestOutputUbundleLoseMsg.abs_eq fun_upd_twist)

text{* @{term RecSPF} test on @{term recTestInputStreamLoseDat}. *}
lemma recspf_test_inputubundlelosedat:
  "RecSPF True \<rightleftharpoons> recTestInputUbundleLoseDat = recTestOutputUbundleLoseMsg" 
  by (simp add: recspf_insert tsynbrec_test_inputubundlelosedat)

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver Transition Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* @{term receiverTransition} maps the old state and bundle on the correct new state and 
       bundle. *}

lemma receivertransition_rt_true:
  "receiverTransition (ReceiverState Rt, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, True)))])
     = ((ReceiverState Rf,(createArBundle True) \<uplus> (createOBundle a)))"
  by simp

lemma receivertransition_rt_false: 
  "receiverTransition (ReceiverState Rt, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, False)))])
     = ((ReceiverState Rt,(createArBundle False) \<uplus> (tsynbNull (\<C> ''o''))))"
  by simp

lemma receivertransition_rf_true: 
  "receiverTransition (ReceiverState Rf, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, True)))])
     = ((ReceiverState Rf,(createArBundle True) \<uplus> (tsynbNull (\<C> ''o''))))"
  by simp

lemma receivertransition_rf_false: 
  "receiverTransition (ReceiverState Rf, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, False)))])
     = ((ReceiverState Rt,(createArBundle False) \<uplus> (createOBundle a)))"
  by simp

lemma receivertransition_null: 
  "receiverTransition (ReceiverState s, [\<C> ''dr'' \<mapsto> null])
     = (ReceiverState s ,(tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))"
  by (cases s, simp_all)

text{* The domain of the union of all possible simple bundles on the two output channels. *}

lemma createaroutput_createooutput_ubclunion_ubdom: 
  "ubDom\<cdot>((createArBundle a) \<uplus> (createOBundle b)) = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: ubclUnion_ubundle_def ubdom_insert ubUnion_def)
  by (simp add: createArBundle.rep_eq createOBundle.rep_eq)

lemma createarbundle_ubdom: "ubDom\<cdot>(createArBundle a)= {\<C> ''ar''}"
  by(simp add: ubDom_def createArBundle.rep_eq)

lemma createaroutput_tsynbnullo_ubclunion_ubdom: 
  "ubDom\<cdot>((createArBundle a) \<uplus> (tsynbNull (\<C> ''o''))) = {\<C> ''ar'', \<C> ''o''}"
  by(simp add: ubclUnion_ubundle_def createarbundle_ubdom insert_commute)

lemma tsynbnullar_tsynbnullo_ubclunion_ubdom:
  "ubDom\<cdot>(tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')) = {\<C> ''ar'', \<C> ''o''}"
  by (metis insert_is_Un tsynbnull_ubdom ubclUnion_ubundle_def ubunionDom)

text{* The domain of the output bundle after applying @{term receiverTransition}. *}
lemma receivertransition_ubdom:
  assumes dom_f: "dom f = {\<C> ''dr''}" 
    and ubelemwell_f: "sbElemWell f"
  shows "ubDom\<cdot>(snd (receiverTransition (s, f))) = {\<C> ''ar'', \<C> ''o''}"
  proof -
    obtain inp where f_def: "f = [\<C> ''dr'' \<mapsto> inp]"
      using dom_eq_singleton_conv dom_f by force
    obtain st where s_def: "s = ReceiverState st"
      using ReceiverAutomaton.getReceiverSubState.cases by blast
    have "ubDom\<cdot>(snd (receiverTransitionH (ReceiverState.ReceiverState st, inp))) 
            = {\<C> ''ar'', \<C> ''o''}"
      proof (cases inp)
        case (Msg i)
          hence "i \<in> ctype (\<C> ''dr'')"
          using assms
          by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
        then obtain a where i_def: "i = Pair_nat_bool a"
          by auto
        then show ?thesis
          proof (cases st)
            case Rf
            then show ?thesis
              by (simp add: Msg createaroutput_createooutput_ubclunion_ubdom 
                  createaroutput_tsynbnullo_ubclunion_ubdom i_def)
          next
            case Rt
            then show ?thesis
              by (simp add: Msg createaroutput_createooutput_ubclunion_ubdom 
                  createaroutput_tsynbnullo_ubclunion_ubdom i_def)
          qed
      next
        case null
        then show ?thesis
          using receivertransition_null tsynbnullar_tsynbnullo_ubclunion_ubdom by auto
      qed
    then show "ubDom\<cdot>(snd (receiverTransition (s, f))) =  {\<C> ''ar'', \<C> ''o''}"
      by (simp add: f_def s_def)
  qed

  text{*The Receiver Automaton is well-formed.*}
lemma receivertransition_automaton_well:
  "daWell (receiverTransition, ReceiverState.ReceiverState Rt,
             tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''), {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  using receivertransition_ubdom by auto

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver Step Lemmata *}
(* ----------------------------------------------------------------------- *) 

(* ToDo: move to dAutomaton. *)

text{* After applying @{term da_h} to an automaton the domain of the output bundle is the range of 
       the automaton. *}
lemma da_h_ubdom: assumes "ubDom\<cdot>sb = daDom automat" 
  shows "ubDom\<cdot>(da_h automat state \<rightleftharpoons> sb) = daRan automat"
  by (simp add: assms spf_ubDom)

text{* The domain of the output bundle after executing one step of @{term da_h} for all cases. *}

(* ToDo: rename the lemmata with da_h instead of h. *)

lemma receiverautomaton_da_h_ubdom:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(da_h ReceiverAutomaton (ReceiverState.ReceiverState s) \<rightleftharpoons> sb) = {\<C> ''ar'', \<C> ''o''}"
  sorry

lemma receiverautomaton_h_step_ubdom_null_null:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(ubConc (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState.ReceiverState s) \<rightleftharpoons> sb)) 
           = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: tsynbnullar_tsynbnullo_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def ReceiverAutomaton.rep_eq insert_commute)+

lemma receiverautomaton_h_step_ubdom_ar_null:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(ubConc ((createArBundle x) \<uplus> (tsynbNull (\<C> ''o'')))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState.ReceiverState s) \<rightleftharpoons> sb)) 
           = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: createaroutput_tsynbnullo_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def ReceiverAutomaton.rep_eq insert_commute)+

lemma receiverautomaton_h_step_ubdom_ar_o: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(ubConc ((createArBundle x) \<uplus> (createOBundle y))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState.ReceiverState s) \<rightleftharpoons> sb)) 
           = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: createaroutput_createooutput_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def ReceiverAutomaton.rep_eq insert_commute)+

text{* The datatype is allowed on the channel. *}
lemma msga_ctype: "Msg (Pair_nat_bool a) \<in> ctype (\<C> ''dr'')"
  by (simp add: ctype_tsynI)

(* ToDo: generalize and simplify next five lemmata. *)

text{* After creating a bundle from a simple message m the contained message is m.  *}
lemma msga_createbundle_ubgetch [simp]: 
  "(createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr'')) . \<C> ''dr'' = \<up>(Msg (Pair_nat_bool a))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by (simp add: msga_ctype)

 (* assumption needed for generalization? *)
lemma createbundle_ubgetch:
  assumes "a\<in> ctype c"
  shows "createBundle a c . c = \<up>a"
  sorry

text{* The concatenation of two bundles with the same domain is the concatenation of the contained 
       messages. *}
lemma msga_createbundle_ubconc [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb .  \<C> ''dr'' 
           = \<up>(Msg (Pair_nat_bool a)) \<bullet> (sb.  \<C> ''dr'')"
  by (simp add: assms usclConc_stream_def)

lemma createbundle_ubconc:
  assumes "c\<in> ubDom\<cdot>sb" and "a \<in> ctype c"
  shows "(ubConc (createBundle a c)\<cdot>sb) . c = \<up>a \<bullet> (sb . c)"
  sorry
 

text{* The rest of the concatenation of a simple bundle with another bundle is the latter. *}
lemma msga_createbundle_ubconc_sbrt[simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "sbRt\<cdot>(ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms)
  by (simp add: assms sbRt_def usclConc_stream_def)

lemma createbundle_ubconc_sbrt:
  assumes "c \<in> ubDom\<cdot>sb"
  shows "sbRt\<cdot>(ubConc (createBundle a c)\<cdot>sb) = sb"
  sorry

text{* Simplify the input bundle in case of a null. *}
lemma tsynbnull_eq[simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull (\<C> ''dr''))\<cdot>sb)) = [\<C> ''dr'' \<mapsto> null]"
  apply (rule convDiscrUp_eqI)
  apply (subst convdiscrup_inv_eq)
  apply (simp add: assms sbHdElem_def sbHdElem_cont domIff2 usclConc_stream_def)+
  apply (subst fun_eq_iff, rule)
  apply (case_tac "x = \<C> ''dr''")
  apply (simp add: convDiscrUp_def)
  apply (subst ubConc_usclConc_eq)
  apply (simp_all add: assms usclConc_stream_def up_def)
  by (metis convDiscrUp_dom domIff fun_upd_apply)

lemma tsynbnull_eqII:
  assumes "ubDom\<cdot>sb = {c}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull c)\<cdot>sb)) = [c \<mapsto> -]"
  sorry

text{* Simplify the input bundle in case of a single message. *}
lemma createaroutput_eq[simp]: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb)) 
           = [\<C> ''dr'' \<mapsto> Msg (Pair_nat_bool a)]"
  apply (rule convDiscrUp_eqI)
  apply (subst convdiscrup_inv_eq)
  apply (simp add: assms sbHdElem_def sbHdElem_cont domIff2 usclConc_stream_def)+
  apply (subst fun_eq_iff, rule)
  apply (case_tac "x = \<C> ''dr''")
  apply (simp add: convDiscrUp_def)
  apply (subst ubConc_usclConc_eq)
  apply (simp_all add: assms usclConc_stream_def up_def)
  by (metis convDiscrUp_dom domIff fun_upd_apply)

lemma createoutput_eq:
  assumes "a \<in> ctype c" and "ubDom\<cdot>sb = {c}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createBundle a c)\<cdot>sb)) = [c \<mapsto> a]"
  sorry

text {* For every state and input one step of @{term da_h} is executed correctly. *}

(* ToDo: rename with da_h/H instead of h. *)

text{* Empty Input. *}
lemma receiverautomaton_h_strict:
  "da_h ReceiverAutomaton (ReceiverState r) \<rightleftharpoons> ubLeast {\<C> ''dr''} 
     = ubLeast {\<C> ''ar'', \<C> ''o''}"
  by (simp add: ReceiverAutomaton.rep_eq daDom_def daRan_def da_h_bottom ubclLeast_ubundle_def)

text{* ReceiverState Rf and input null. *}
lemma receiverautomaton_h_step_rf_null:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''dr''))\<cdot>sb) 
           = ubConc ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))
               \<cdot>(da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  (*using assms receiverautomaton_h_step_ubdom_null_null by auto*)
  by(simp add: assms receiverautomaton_da_h_ubdom tsynbnullar_tsynbnullo_ubclunion_ubdom)
 (* apply(rule ubrestrict_id)
  by (simp only: assms receiverautomaton_h_step_ubdom_null_null)*)

text{* ReceiverState Rt and input null. *}
lemma receiverautomaton_h_step_rt_null: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''dr''))\<cdot>sb) 
           = ubConc ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))
               \<cdot>(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

text{* ReceiverState Rf and input true. *}
lemma receiverautomaton_h_step_rf_true:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
    and "(snd a) = True"
  shows "da_h ReceiverAutomaton (ReceiverState Rf) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = ubConc (createArBundle (snd a) \<uplus> (tsynbNull (\<C> ''o'')))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

text{* ReceiverState Rt and input true. *}
lemma receiverautomaton_h_step_rt_true: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
    and "(snd a) = True"
  shows "da_h ReceiverAutomaton (ReceiverState Rt) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb)
             = ubConc (createArBundle (snd a) \<uplus> (createOBundle (fst a)))
                 \<cdot>(da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

text{* ReceiverState Rf and input false. *}
lemma receiverautomaton_h_step_rf_false: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
    and "(snd a) = False"
  shows "da_h ReceiverAutomaton (ReceiverState Rf) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = ubConc (createArBundle (snd a) \<uplus> createOBundle (fst a))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

text{* ReceiverState Rt and input false. *}
lemma receiverautomaton_h_step_rt_false: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = False"
  shows "da_h ReceiverAutomaton (ReceiverState Rt) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = ubConc (createArBundle (snd a) \<uplus> (tsynbNull (\<C> ''o'')))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

text{* The SPF generated from @{term ReceiverAutomaton} executes the first step correctly. *}
lemma receiverautomaton_H_step:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "da_H ReceiverAutomaton \<rightleftharpoons> sb 
           = ubConc ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))
               \<cdot>(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb)"
  apply (simp add: da_H_def da_h_ubdom daRan_def daInitialState_def daInitialOutput_def 
         ReceiverAutomaton.rep_eq daDom_def assms)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* The domain of the @{term ReceiverAutomaton}. *}
lemma dadom_receiverautomaton: 
  "daDom ReceiverAutomaton = {\<C> ''dr''}"
  by (simp add: daDom_def ReceiverAutomaton.rep_eq)

text{* The range of the @{term ReceiverAutomaton}. *}
lemma daran_receiverautomaton: 
  "daRan ReceiverAutomaton = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: daRan_def ReceiverAutomaton.rep_eq)

text{* Initial output of the @{term ReceiverAutomaton}. *}
lemma dainitialoutput_receiverautomaton:
  "daInitialOutput ReceiverAutomaton = tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')"
  by (simp add: daInitialOutput_def ReceiverAutomaton.rep_eq)

text{* Application of @{term ubLeast} on @{term ReceiverSPF} yields only the initial output. *}
lemma receiverspf_strict:
  "ReceiverSPF \<rightleftharpoons> ubLeast{\<C> ''dr''} = tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o'')"
  apply (fold ubclLeast_ubundle_def)
  by (simp add: ReceiverSPF_def da_H_bottom dadom_receiverautomaton daran_receiverautomaton 
                dainitialoutput_receiverautomaton tsynbnullar_tsynbnullo_ubclunion_ubdom)

text{* The domain of @{term ReceiverSPF}. *}
lemma receiverspf_ufdom: "ufDom\<cdot>ReceiverSPF = {\<C> ''dr''}"
  by (simp add: ReceiverSPF_def da_H_def ReceiverAutomaton.rep_eq daDom_def)

text{* The range of @{term ReceiverSPF}. *}
lemma receiverspf_ufran: "ufRan\<cdot>ReceiverSPF = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: ReceiverSPF_def da_H_def ReceiverAutomaton.rep_eq daRan_def)

text{* The domain of the output bundle of @{term ReceiverSPF}. *}
lemma receiverspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>ReceiverSPF"
  shows "ubDom\<cdot>(ReceiverSPF \<rightleftharpoons> sb) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: assms receiverspf_ufran spf_ubDom)

(* Step lemmata for RecSPF *)
lemma recspf_ubconc_null: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "RecSPF b \<rightleftharpoons> ubConc (tsynbNull (\<C> ''dr''))\<cdot>sb 
           = ubConc (tsynbNull (\<C> ''ar'') \<uplus> (tsynbNull (\<C> ''o'')))\<cdot>(RecSPF b \<rightleftharpoons> sb)"
  sorry

lemma recspf_true_ubconc_true: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = True"
  shows "RecSPF True \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb 
           = ubConc (createArBundle (snd a) \<uplus> createOBundle (fst a))\<cdot>(RecSPF False \<rightleftharpoons> sb)"
  sorry

lemma recspf_true_ubconc_false: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = False"
  shows "RecSPF True \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb 
           = ubConc (createArBundle (snd a) \<uplus> tsynbNull (\<C> ''o''))\<cdot>(RecSPF True \<rightleftharpoons> sb)"
  sorry

lemma recspf_false_ubconc_true: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = True"
  shows "RecSPF False \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb 
           = ubConc (createArBundle (snd a) \<uplus> (tsynbNull (\<C> ''o'')))\<cdot>(RecSPF False \<rightleftharpoons> sb)"
  sorry

lemma recspf_false_ubconc_false: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = False"
  shows "RecSPF False \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb 
           = ubConc (createArBundle (snd a) \<uplus> createOBundle (fst a))\<cdot>(RecSPF True \<rightleftharpoons> sb)"
  sorry

(* the assumption is different here *)
lemma eq_conc_rf_false:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = False"
    and "(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb) = (RecSPF True \<rightleftharpoons> sb)"
  shows "da_h ReceiverAutomaton (ReceiverState Rf) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
            = RecSPF False \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb"
  by(simp add: assms recspf_false_ubconc_false receiverautomaton_h_step_rf_false)

lemma eq_conc_rf_true:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = True"
    and "(da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> sb) = (RecSPF False \<rightleftharpoons> sb)"
  shows "da_h ReceiverAutomaton (ReceiverState Rf) 
            \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = RecSPF False \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb"
  by(simp add: assms recspf_false_ubconc_true receiverautomaton_h_step_rf_true)

lemma eq_conc_rt_false:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = False"
    and "(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb) = (RecSPF True \<rightleftharpoons> sb)"
  shows "da_h ReceiverAutomaton (ReceiverState Rt) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = RecSPF True \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb"
  by(simp add: assms recspf_true_ubconc_false receiverautomaton_h_step_rt_false)

lemma eq_conc_rt_true:
  assumes dom: "ubDom\<cdot>sb = {\<C> ''dr''}"
    and ind_hyp: "(da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb) = (RecSPF True \<rightleftharpoons> sb)"
    and snd_true: "(snd a) = True"
  shows "da_h ReceiverAutomaton (ReceiverState Rt) 
           \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = RecSPF True \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb"
proof-
  have recaut_eq_recspf_false: "da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> sb = RecSPF False \<rightleftharpoons> sb"
    proof(induction sb rule: ind_ub)
      case 1
      then show ?case 
        proof (rule admI)
          fix Y :: "nat \<Rightarrow> abpMessage tsyn stream\<^sup>\<Omega>"
          assume chain_Y: "chain Y"
          assume adm_hyp: "\<forall>i::nat. da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> Y i 
                                      = RecSPF False \<rightleftharpoons> Y i"
          have "(\<Squnion>n. da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> Y n) 
                   = (\<Squnion>n. RecSPF False \<rightleftharpoons> Y n)"
            using adm_hyp by fastforce
          then show "da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> (\<Squnion>i::nat. Y i) 
                  = RecSPF False \<rightleftharpoons> (\<Squnion>i::nat. Y i)"
            by (simp add: chain_Y ufunlub_ufun_fun)
        qed
      next
        case 2
        then show ?case 
          by (simp add: assms receiverautomaton_h_strict receiverspf_ufdom recspf_strict 
              ubclLeast_ubundle_def)
      next
        case (3 u ub)
        then show ?case
          proof (cases rule: tsynb_cases [of u "(\<C> ''dr'')"])
            case max_len
            then show ?case
              using "3.IH" by blast
          next
            case not_ubleast
            then show ?case 
              by (simp add: "3.IH")
          next
            case numb_channel
            then show ?case 
              by (simp add: "3.IH" assms receiverspf_ufdom)
          next
            case (msg m)
            fix m :: "abpMessage"
            assume ind_hyp_dom: "da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> ub = RecSPF False \<rightleftharpoons> ub 
                      \<and> ubDom\<cdot>u = ubDom\<cdot>sb \<and> ubDom\<cdot>ub = ubDom\<cdot>sb \<and> ubMaxLen (Fin (1::nat)) u 
                         \<and> u \<noteq> ubLeast (ubDom\<cdot>sb)"
            assume "\<M> m \<in> ctype (\<C> ''dr'')"
            hence ctype_m: "m \<in> ctype (\<C> ''dr'')"
              using ctype_tsyn_iff by blast              
            from ctype_m obtain a where m_def: "m = Pair_nat_bool a"
              by auto
            show "da_h ReceiverAutomaton (ReceiverState Rf) 
                    \<rightleftharpoons> ubConc (createBundle (\<M> m) (\<C> ''dr''))\<cdot>ub 
                      = RecSPF False \<rightleftharpoons> ubConc (createBundle (\<M> m) (\<C> ''dr''))\<cdot>ub"
              proof-
                have hyp_ub: "(ubDom\<cdot>sb = ubDom\<cdot>ub) \<Longrightarrow> (da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb) = (RecSPF True \<rightleftharpoons> sb)
                       \<Longrightarrow> (da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> ub) = (RecSPF True \<rightleftharpoons> ub)"
                  sorry
                  have m_true: "(snd a) = True \<Longrightarrow> da_h ReceiverAutomaton (ReceiverState Rf)
                               \<rightleftharpoons> ubConc (createBundle (\<M> (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>ub 
                                 = RecSPF False \<rightleftharpoons> ubConc (createBundle (\<M> (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>ub"
                  by(simp add: eq_conc_rf_true ind_hyp_dom dom)                   
                have m_false: "(snd a) = False \<Longrightarrow>  da_h ReceiverAutomaton (ReceiverState Rf) 
                    \<rightleftharpoons> ubConc (createBundle (\<M> (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>ub 
                      = RecSPF False \<rightleftharpoons> ubConc (createBundle (\<M> (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>ub"                  
                  by(simp add: eq_conc_rf_false dom ind_hyp_dom hyp_ub ind_hyp)
                show ?thesis
                  using m_true m_false m_def by blast
              qed
          next
            case null
            assume "da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> ub = RecSPF False \<rightleftharpoons> ub 
                      \<and> ubDom\<cdot>u = ubDom\<cdot>sb \<and> ubDom\<cdot>ub = ubDom\<cdot>sb \<and> ubMaxLen (Fin (1::nat)) u 
                         \<and> u \<noteq> ubLeast (ubDom\<cdot>sb)"
            show "da_h ReceiverAutomaton (ReceiverState Rf) \<rightleftharpoons> ubConc (tsynbNull (\<C> ''dr''))\<cdot>ub 
                    = RecSPF False \<rightleftharpoons> ubConc (tsynbNull (\<C> ''dr''))\<cdot>ub"
              by (simp add: "3.IH" assms(1) receiverautomaton_h_step_rf_null recspf_ubconc_null)
          qed
      qed
    show "da_h ReceiverAutomaton (ReceiverState Rt) 
            \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
              = RecSPF True \<rightleftharpoons> ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb"
      using recaut_eq_recspf_false 
      by(simp add: assms recspf_true_ubconc_true receiverautomaton_h_step_rt_true)
  qed

text{* If @{term ReceiverSPF} and @{term RecSPF} get the same input, they yield the same result. *}
lemma recspf_receiverspf_ub_eq:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>ReceiverSPF"
  shows "ReceiverSPF \<rightleftharpoons> sb = ubConc (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(RecSPF True \<rightleftharpoons> sb)"
  proof -
    have recaut_eq_recspf: "da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> sb = RecSPF True \<rightleftharpoons> sb"
      proof (induction sb rule: ind_ub)
        case 1
        then show ?case
          proof (rule admI)
            fix Y :: "nat \<Rightarrow> abpMessage tsyn stream\<^sup>\<Omega>"
            assume chain_Y: "chain Y"
            assume adm_hyp: "\<forall>i::nat. da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> Y i 
                                        = RecSPF True \<rightleftharpoons> Y i"
            have "(\<Squnion>n. da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> Y n) 
                     = (\<Squnion>n. RecSPF True \<rightleftharpoons> Y n)"
              using adm_hyp by fastforce
            then show "da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> (\<Squnion>i::nat. Y i) 
                    = RecSPF True \<rightleftharpoons> (\<Squnion>i::nat. Y i)"
              by (simp add: chain_Y ufunlub_ufun_fun)
          qed
      next
        case 2
        then show ?case 
          by (simp add: assms receiverautomaton_h_strict receiverspf_ufdom recspf_strict 
              ubclLeast_ubundle_def)
      next
        case (3 u ub)
        then show ?case 
          proof (cases rule: tsynb_cases [of u "(\<C> ''dr'')"])
            case max_len
            then show ?case
              using "3.IH" by blast
          next
            case not_ubleast
            then show ?case 
              by (simp add: "3.IH")
          next
            case numb_channel
            then show ?case 
              by (simp add: "3.IH" assms receiverspf_ufdom)
          next
            case (msg m)
            fix m :: "abpMessage"
            assume "da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> ub = RecSPF True \<rightleftharpoons> ub 
                      \<and> ubDom\<cdot>u = ubDom\<cdot>sb \<and> ubDom\<cdot>ub = ubDom\<cdot>sb \<and> ubMaxLen (Fin (1::nat)) u 
                         \<and> u \<noteq> ubLeast (ubDom\<cdot>sb)"
            assume "\<M> m \<in> ctype (\<C> ''dr'')"
            hence ctype_m: "m \<in> ctype (\<C> ''dr'')"
              using ctype_tsyn_iff by blast              
            from ctype_m obtain a where m_def: "m = Pair_nat_bool a"
              by auto
            show "da_h ReceiverAutomaton (ReceiverState Rt) 
                    \<rightleftharpoons> ubConc (createBundle (\<M> m) (\<C> ''dr''))\<cdot>ub 
                      = RecSPF True \<rightleftharpoons> ubConc (createBundle (\<M> m) (\<C> ''dr''))\<cdot>ub"
              by (metis "3.IH" assms eq_conc_rt_false eq_conc_rt_true m_def receiverspf_ufdom)
          next
            case null
            assume "da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> ub = RecSPF True \<rightleftharpoons> ub 
                      \<and> ubDom\<cdot>u = ubDom\<cdot>sb \<and> ubDom\<cdot>ub = ubDom\<cdot>sb \<and> ubMaxLen (Fin (1::nat)) u 
                         \<and> u \<noteq> ubLeast (ubDom\<cdot>sb)"
            show "da_h ReceiverAutomaton (ReceiverState Rt) \<rightleftharpoons> ubConc (tsynbNull (\<C> ''dr''))\<cdot>ub 
                    = RecSPF True \<rightleftharpoons> ubConc (tsynbNull (\<C> ''dr''))\<cdot>ub"
              by (simp add: "3.IH" assms receiverautomaton_h_step_rt_null receiverspf_ufdom 
                  recspf_ubconc_null)
          qed
      qed
    show "ReceiverSPF \<rightleftharpoons> sb 
            = ubConc (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(RecSPF True \<rightleftharpoons> sb)"
      using ReceiverSPF_def assms recaut_eq_recspf receiverautomaton_H_step receiverspf_ufdom 
      by auto
  qed

text{* @{term ReceiverSPF} is equal to @{term RecSPF}. *}
lemma recspf_receiverspf_eq: 
  "ReceiverSPF = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(RecSPF True)"
  proof (rule ufun_eqI)
    show "ufDom\<cdot>ReceiverSPF 
          = ufDom\<cdot>(spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(RecSPF True))"
      by (simp add: receiverspf_ufdom recspf_ufdom)
  next 
    fix x :: "abpMessage tsyn stream\<^sup>\<Omega>"
    assume dom: "ubclDom\<cdot>x = ufDom\<cdot>ReceiverSPF"
    show "ReceiverSPF \<rightleftharpoons> x 
            = spfConcOut (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))\<cdot>(RecSPF True) \<rightleftharpoons> x"
      by (metis dom insert_absorb2 receiverspf_ubdom receiverspf_ufdom recspf_receiverspf_ub_eq 
          recspf_ubdom recspf_ufdom spfConcOut_step subset_insertI ubclDom_ubundle_def 
          ubconceq_insert ubrestrict_id)
  qed

end
