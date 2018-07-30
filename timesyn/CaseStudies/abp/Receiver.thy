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
  "[\<C> ''o'' \<mapsto> nat2abp\<cdot>recTestOutputStreamOLoseMsg, \<C> ''ar'' \<mapsto> bool2abp\<cdot>recTestOutputStreamArLoseMsg]"
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
definition tsynRec :: "(nat \<times> bool) tsyn stream \<rightarrow> nat tsyn stream" where
  "tsynRec \<equiv> \<Lambda> s. sscanlA tsynRec_h True\<cdot>s"

text {* @{term tsynbRec}: Receiver function for Alternating Bit Protocol on stream bundles. *}
definition tsynbRec :: "abpMessage tsyn stream ubundle \<rightarrow> abpMessage tsyn stream ubundle option" where 
  "tsynbRec \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle [
                     \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
                     \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))
                     ]"

text {* @{term tsynbRec}: Receiver function for Alternating Bit Protocol. *}
definition RecSPF :: "abpMessage tsyn SPF" where
  "RecSPF \<equiv> Abs_ufun tsynbRec"

(* ----------------------------------------------------------------------- *)
  section {* Receiver SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynRec} insertion lemma. *}
lemma tsynrec_insert: "tsynRec\<cdot>s = sscanlA tsynRec_h True\<cdot>s"
  by (simp add: tsynRec_def)

text {* @{term tsynRec} maps the empty (nat x bool ) tsyn stream on the empty nat tsyn stream. *}
lemma tsynrec_strict [simp]: "tsynRec\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} does not distribute directly over concatenation, when the first element 
  is a message with True bit.*}
lemma tsynrec_sconc_msg_t: " tsynRec\<cdot>(\<up>(Msg (m, True)) \<bullet> s) = \<up>(Msg m)\<bullet> (sscanlA tsynRec_h False\<cdot>s)"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} distributes over concatenation, when the first element 
  is a message with False bit.*}
lemma tsynrec_sconc_msg_f: " tsynRec\<cdot>(\<up>(Msg (m, False)) \<bullet> s) = \<up>(null)\<bullet> tsynRec\<cdot>s"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} distributes over concatenation, when concatenating a null.*}
lemma tsynrec_sconc_null: " tsynRec\<cdot>(\<up>(null) \<bullet> s) = \<up>(null) \<bullet> tsynRec\<cdot>s"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} leaves the length of a stream unchanged. *}
lemma tsynrec_slen: "#(tsynRec\<cdot>s) = #s"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} test on finite stream. *}
lemma tsynrec_test_finstream:
  "tsynRec\<cdot>(<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>) = <[null, null,\<M> 2, \<M> 1]>"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} test on infinite stream. *}
lemma tsynrec_test_infstream: 
  "tsynRec\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>) 
     = (<[null, null, \<M> 2, \<M> 1]>)\<infinity>"
proof -
  have inf_unfold:"tsynRec\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>) \<bullet> 
       ((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>))
       = <[null, null,\<M> 2, \<M> 1]> \<bullet> tsynRec\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)" 
    by (simp add: tsynrec_insert)
  have "((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>) \<bullet> 
       ((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)) =
       ((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>) " using sinftimes_unfold by metis
  hence "tsynRec\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)
       = <[null, null,\<M> 2, \<M> 1]> \<bullet> tsynRec\<cdot>((<[\<M>(1, False), null, \<M>(2, True),\<M>(1, False)]>)\<infinity>)" 
    using inf_unfold by metis
  thus ?thesis by (simp add: rek2sinftimes)
qed

text{* The output bundle of @{term tsynbRec} is well-formed. *}
lemma tsynbrec_ubwell [simp]:
 "ubWell [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(x  .  \<C> ''dr''))),
          \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(x  .  \<C> ''dr'')))]"
  apply (simp add: ubWell_def)
  apply (simp add: usclOkay_stream_def)
  apply (simp add: nat2abp_def bool2abp_def)
  apply (simp add: ctype_tsyn_def tsynMap_def)
  apply (simp add: smap_sdom)
  apply (simp add: image_subset_iff image_iff range_eqI)
  apply (rule)
  using tsynApplyElem.elims apply blast
  using tsynApplyElem.elims by blast

text{* The domain of the output bundle of @{term tsynbRec}. *}
lemma tsynbrec_ubundle_ubdom: "ubDom\<cdot>(Abs_ubundle 
              [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
               \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))]) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: ubDom_def insert_commute)

text{* @{term tsynbRec} is monotonous. *}
lemma tsynbrec_mono [simp]:
  "monofun (\<lambda> sb. (ubDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle [
              \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
              \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))])"
  apply(fold ubclDom_ubundle_def)
  apply (rule ufun_monoI2)
  by (simp add: below_ubundle_def cont_pref_eq1I fun_belowI some_below)

text{* Creating a chain on the two output channels. *}

lemma tsynbrec_chain: "chain Y \<Longrightarrow>
  chain (\<lambda>i::nat. [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''dr''))), 
                   \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''dr'')))])"
  apply (rule chainI)
  by (simp add: fun_below_iff monofun_cfun_arg po_class.chainE some_below)

lemma tsynbrec_ubundle_chain: "chain Y \<Longrightarrow>
  chain (\<lambda>i::nat. Abs_ubundle 
        [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''dr''))),
         \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''dr'')))])"
  apply (rule chainI)
  apply (simp add: below_ubundle_def)
  by (simp add: fun_below_iff monofun_cfun_arg po_class.chainE some_below)

lemma tsynbrec_chain2: " chain Y \<Longrightarrow>
  chain (\<lambda>i::nat. [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>Rep_ubundle (Y i)\<rightharpoonup>\<C> ''dr'')), 
                   \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>Rep_ubundle (Y i)\<rightharpoonup>\<C> ''dr''))])"
  by (metis (no_types, lifting) po_class.chain_def tsynbrec_chain ubgetch_insert)

text{* Extracting the lub doesn't change the term.*}

lemma tsynbrec_ar_contlub: assumes "chain Y"
  shows "bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(\<Squnion>i. Y i  .  \<C> ''dr''))) 
  = (\<Squnion>i. (bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(((Y i.  \<C> ''dr'')))))))"
  by (simp add: assms contlub_cfun_arg)

lemma tsynbrec_o_contlub: assumes "chain Y"
  shows "nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(\<Squnion>i. Y i  .  \<C> ''dr''))) 
  = (\<Squnion>i. (nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(((Y i.  \<C> ''dr'')))))))"
  by (simp add: assms contlub_cfun_arg)

text{* @{term tsynbRec} is continuous. *}
lemma tsynbrec_cont [simp]:
  "cont (\<lambda> sb. (ubDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle [
               \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
               \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))])"
  apply (fold ubclDom_ubundle_def)
  apply (rule ufun_contI2)
  apply (rule cont_Abs_UB)
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: below_ubundle_def cont_pref_eq1I fun_belowI some_below)
  using tsynbrec_chain apply (simp add: contlub_cfun_arg fun_below_iff some_lub_chain_eq lub_fun)
  using tsynbrec_ubwell by blast

text{* @{term tsynbRec} insertion lemma. *}
lemma tsynbrec_insert: "tsynbRec\<cdot>sb = (ubDom\<cdot>sb = {\<C> ''dr''}) \<leadsto> Abs_ubundle 
              [\<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr''))), 
               \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''dr'')))]"
   by (simp add: tsynbRec_def ubclDom_ubundle_def)

text{* @{term tsynbRec} is well-formed. *}
lemma tsynbrec_ufwell [simp]: "ufWell tsynbRec"
  apply (rule ufun_wellI)
  apply (simp_all add: tsynbRec_def domIff2 ubclDom_ubundle_def)
  by (simp add: tsynbrec_ubundle_ubdom)

text{* @{term RecSPF} insertion lemma. *}
lemma recspf_insert: "RecSPF \<rightleftharpoons> sb = (Abs_ufun tsynbRec) \<rightleftharpoons> sb"
  by (simp add: RecSPF_def)

text{* The domain of @{term RecSPF}. *}
lemma recspf_ufdom: "ufDom\<cdot>RecSPF = {\<C> ''dr''}"
  by (metis RecSPF_def rep_abs_cufun2 tsynbnull_ubdom tsynbrec_insert tsynbrec_ufwell 
      ubclDom_ubundle_def ufdom_2ufundom)
  
text{* The range of @{term RecSPF}. *}
lemma recspf_ufran: "ufRan\<cdot>RecSPF = {\<C> ''ar'', \<C> ''o''}"
  proof -
    have  "\<forall> sb. ubDom\<cdot>Rep_cfun tsynbRec \<rightharpoonup> sb = {\<C> ''ar'', \<C> ''o''} \<or> ubDom\<cdot>sb \<noteq> {\<C> ''dr''}"
      by (simp add: tsynbrec_insert tsynbrec_ubundle_ubdom ubclDom_ubundle_def)
    hence "ubclDom\<cdot>(SOME sbout::abpMessage tsyn stream\<^sup>\<Omega>. sbout \<in> ran (Rep_cufun RecSPF)) 
             = {\<C> ''ar'', \<C> ''o''}"
      by (metis (no_types) RecSPF_def recspf_ufdom rep_abs_cufun2 spf_ubDom tsynbrec_ufwell
          ubclDom_ubundle_def ufdom_insert ufran_insert)
    thus ?thesis
      by (simp add: ufRan_def)
  qed

text{* The domain of the output bundle of @{term tsynbRec}. *}
lemma recspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>RecSPF"
  shows "ubDom\<cdot>(RecSPF \<rightleftharpoons> sb) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: assms recspf_ufran spf_ubDom)

text{* @{term RecSPF} is strict. *}
lemma recspf_strict: "RecSPF \<rightleftharpoons> ubLeast{\<C> ''dr''} = ubLeast{\<C> ''ar'', \<C> ''o''}"
  proof -
    have ubleast_dr: "ubLeast{\<C> ''dr''} = Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>)"
      by (simp add: ubLeast_def)
    hence recspf_bundle_strict: "RecSPF \<rightleftharpoons> (Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>)) 
             = Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''ar'', \<C> ''o''}) \<leadsto> \<epsilon>)"
      proof -
        have ar_is_strict : "bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>\<epsilon>)) = \<epsilon>" 
          by (simp add: abp2natbool_def bool2abp_def)
        have o_is_strict : "nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(\<epsilon>))) = \<epsilon>" 
          by (simp add: abp2natbool_def tsynRec_def nat2abp_def)
        have eval_recspf : "RecSPF \<rightleftharpoons> (Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>))
                              = Abs_ubundle [
                                  \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(
                                    Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>)  .  \<C> ''dr''))),
                                  \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(
                                    Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>)  .  \<C> ''dr'')))]"
          proof -
            have "ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>)) = {\<C> ''dr''}"
              by (metis ubDom_ubLeast ubleast_dr)
            hence "ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c = \<C> ''dr'') \<leadsto> \<epsilon>)) = {\<C> ''dr''}"
              by(simp add: singleton_iff)
            hence "ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c = \<C> ''dr'') \<leadsto> \<epsilon>)) \<noteq> {\<C> ''dr''} \<longrightarrow> the None 
                     = Abs_ubundle [
                         \<C> ''ar'' \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(
                           Abs_ubundle (\<lambda>c. (c = \<C> ''dr'') \<leadsto> \<epsilon>)  .  \<C> ''dr''))),
                         \<C> ''o'' \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(
                           Abs_ubundle (\<lambda>c. (c = \<C> ''dr'') \<leadsto> \<epsilon>)  .  \<C> ''dr'')))]"
              by blast
            thus ?thesis 
              by (simp add: RecSPF_def tsynbrec_insert)
          qed
        have is_empty_stream : "(Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>))  .  \<C> ''dr'' = \<epsilon>"
          by (metis singletonI ubLeast_def ubleast_ubgetch)
        hence recspf_is_strict: "RecSPF \<rightleftharpoons> (Abs_ubundle (\<lambda>c. (c \<in> {\<C> ''dr''}) \<leadsto> \<epsilon>)) 
                                   = Abs_ubundle [\<C> ''ar'' \<mapsto> \<epsilon>, \<C> ''o'' \<mapsto> \<epsilon>]"
          by (metis ar_is_strict eval_recspf o_is_strict)       
        have "Abs_ubundle [\<C> ''ar'' \<mapsto>  \<epsilon>, \<C> ''o'' \<mapsto>  \<epsilon>] =
                Abs_ubundle (\<lambda>c. (c = \<C> ''ar'' \<or> c = \<C> ''o'') \<leadsto> \<epsilon>)"
          by (metis (no_types, lifting) fun_upd_apply)
        from this recspf_is_strict show ?thesis by simp
      qed
    thus "RecSPF \<rightleftharpoons>  ubLeast{\<C> ''dr''} = ubLeast{\<C> ''ar'', \<C> ''o''}"
        by(simp add: ubLeast_def)
  qed

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver Transition Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* @{term receiverTransition} maps the old state and bundle on the correct new state and bundle. *}

lemma receivertransition_rt_true:
  "receiverTransition (State Rt, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, True)))])
     = ((State Rf,(createArBundle True) \<uplus> (createOBundle a)))"
  by simp

lemma receivertransition_rt_false: 
  "receiverTransition (State Rt, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, False)))])
     = ((State Rt,(createArBundle False) \<uplus> (tsynbNull (\<C> ''o''))))"
  by simp

lemma receivertransition_rf_true: 
  "receiverTransition (State Rf, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, True)))])
     = ((State Rf,(createArBundle True) \<uplus> (tsynbNull (\<C> ''o''))))"
  by simp

lemma receivertransition_rf_false: 
  "receiverTransition (State Rf, [\<C> ''dr'' \<mapsto> (Msg (Pair_nat_bool (a, False)))])
     = ((State Rt,(createArBundle False) \<uplus> (createOBundle a)))"
  by simp

lemma receivertransition_null: 
  "receiverTransition (State s, [\<C> ''dr'' \<mapsto> null])
     = (State s ,(tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))"
  by (cases s, simp_all)

text{* The domain of the union of all possible simple bundles on the two output channels. *}

lemma createaroutput_createooutput_ubclunion_ubdom: 
  "ubDom\<cdot>((createArBundle a) \<uplus> (createOBundle b)) = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: ubclUnion_ubundle_def ubdom_insert ubUnion_def)
  by (simp add: createArBundle.rep_eq createOBundle.rep_eq)

lemma createaroutput_tsynbnullo_ubclunion_ubdom: 
  "ubDom\<cdot>((createArBundle a) \<uplus> (tsynbNull (\<C> ''o''))) = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: ubclUnion_ubundle_def ubdom_insert ubUnion_def)
  by (simp add: createArBundle.rep_eq tsynbNull.rep_eq)

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
    obtain st where s_def: "s = State st"
      using ReceiverAutomaton.getSubState.cases by blast
    have "ubDom\<cdot>(snd (receiverTransitionH (ReceiverState.State st, inp))) = {\<C> ''ar'', \<C> ''o''}"
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
  "daWell (receiverTransition, ReceiverState.State Rt, tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''), 
                   {\<C> ''dr''}, {\<C> ''ar'', \<C> ''o''})"
  using receivertransition_ubdom by auto

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver Step Lemmata *}
(* ----------------------------------------------------------------------- *) 

text{* After applying @{term da_h} to an automaton the domain of the output bundle is the range of the automaton *}
lemma da_h_ubdom: assumes "ubDom\<cdot>sb = daDom automat" 
  shows "ubDom\<cdot>(da_h automat state \<rightleftharpoons> sb) = daRan automat"
  by (simp add: assms spf_ubDom)

text{* The domain of the output bundle after executing one step of @{term da_h} for all cases. *}

lemma receiverautomaton_h_step_ubdom_null_null:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(ubConc (tsynbNull (\<C> ''ar'') \<uplus> tsynbNull (\<C> ''o''))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState.State s) \<rightleftharpoons> sb)) = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: tsynbnullar_tsynbnullo_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def ReceiverAutomaton.rep_eq insert_commute)+

lemma receiverautomaton_h_step_ubdom_ar_null:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(ubConc ((createArBundle x) \<uplus> (tsynbNull (\<C> ''o'')))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState.State s) \<rightleftharpoons> sb)) = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: createaroutput_tsynbnullo_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def ReceiverAutomaton.rep_eq insert_commute)+

lemma receiverautomaton_h_step_ubdom_ar_o: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubDom\<cdot>(ubConc ((createArBundle x) \<uplus> (createOBundle y))
                  \<cdot>(da_h ReceiverAutomaton (ReceiverState.State s) \<rightleftharpoons> sb)) = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: createaroutput_createooutput_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def ReceiverAutomaton.rep_eq insert_commute)+

text{* The datatype is allowed on  the channel. *}
lemma msga_ctype: "Msg (Pair_nat_bool a) \<in> ctype (\<C> ''dr'')"
  by (simp add: ctype_tsynI)

text{* After creating a bundle from a simple message m the contained message is m.  *}
lemma msga_createbundle_ubgetch [simp]: 
  "(createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr'')) . \<C> ''dr'' = \<up>(Msg (Pair_nat_bool a))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by (simp add: msga_ctype)

text{* The concatenation of two bundles with the same domain is the concatenation of the contained messages.*}
lemma msga_createbundle_ubconc [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb .  \<C> ''dr'' 
           = \<up>(Msg (Pair_nat_bool a)) \<bullet> (sb.  \<C> ''dr'')"
  by (simp add: assms usclConc_stream_def)

text{* The rest of the concatenation of a simple bundle with another bundle is the latter. *}
lemma msga_createbundle_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
  shows "sbRt\<cdot>(ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms)
  by (simp add: assms sbRt_def usclConc_stream_def)

text{* Simplify the input bundle in case of a null. *}
lemma tsynbnull_eq [simp]:
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

text{* Simplify the input bundle in case of a single message. *}
lemma createaroutput_eq [simp]:
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

text {*For every state and input one step of @{term da_h} is executed correctly *}

text{* State Rf and input null. *}
lemma receiverautomaton_h_step_rf_null:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "da_h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''dr''))\<cdot>sb) 
           = ubConc ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))\<cdot>(da_h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

text{* State Rt and input null. *}
lemma receiverautomaton_h_step_rt_null: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''dr''))\<cdot>sb) 
           = ubConc ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))\<cdot>(da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

text{* State Rf and input true. *}
lemma receiverautomaton_h_step_rf_true:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
    and "(snd a) = True"
  shows "da_h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
           = ubConc (createArBundle (snd a) \<uplus> (tsynbNull (\<C> ''o'')))
               \<cdot>(da_h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

text{* State Rt and input null. *}
lemma receiverautomaton_h_step_rt_true: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
    and "(snd a) = True"
  shows "da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb)
           = ubConc (createArBundle (snd a) \<uplus> (createOBundle (fst a)))
               \<cdot>(da_h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

text{* State Rf and input false. *}
lemma receiverautomaton_h_step_rf_false: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}" 
    and "(snd a) = False"
  shows "da_h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
           = ubConc (createArBundle (snd a) \<uplus> createOBundle (fst a))
               \<cdot>(da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

text{* State Rt and input null. *}
lemma receiverautomaton_h_step_rt_false: 
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
    and "(snd a) = False"
  shows "da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (createBundle (Msg (Pair_nat_bool a)) (\<C> ''dr''))\<cdot>sb) 
           = ubConc (createArBundle (snd a) \<uplus> (tsynbNull (\<C> ''o'')))
               \<cdot>(da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def ReceiverAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

text{* The SPF generated from @{term ReceiverAutomaton} executes the first step correctly.*}
lemma receiverautomaton_H_step:
  assumes "ubDom\<cdot>sb = {\<C> ''dr''}"
  shows "da_H ReceiverAutomaton \<rightleftharpoons> sb 
           = ubConc ((tsynbNull (\<C> ''ar'')) \<uplus> (tsynbNull (\<C> ''o'')))\<cdot>(da_h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp add: da_H_def da_h_ubdom daRan_def daInitialState_def daInitialOutput_def 
         ReceiverAutomaton.rep_eq daDom_def assms)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* @{term ReceiverSPF} is strict. *}
lemma receiverspf_strict: "ReceiverSPF \<rightleftharpoons> ubLeast{\<C> ''dr''} = ubLeast{\<C> ''ar'', \<C> ''o''}"
  sorry

text{* The domain of @{term ReceiverSPF}. *}
lemma receiverspf_ufdom: "ufDom\<cdot>ReceiverSPF = {\<C> ''dr''}"
  apply (simp add: ReceiverSPF_def da_H_def ReceiverAutomaton_def daDom_def)
  using ReceiverAutomaton.abs_eq ReceiverAutomaton.rep_eq by auto

text{* The range of @{term ReceiverSPF}. *}
lemma receiverspf_ufran: "ufRan\<cdot>ReceiverSPF = {\<C> ''ar'', \<C> ''o''}"
  apply (simp add: ReceiverSPF_def da_H_def ReceiverAutomaton_def daRan_def)
  using ReceiverAutomaton.abs_eq ReceiverAutomaton.rep_eq by auto

text{* The domain of the output bundle of @{term ReceiverSPF}. *}
lemma receiverspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>ReceiverSPF"
  shows "ubDom\<cdot>(ReceiverSPF \<rightleftharpoons> sb) = {\<C> ''ar'', \<C> ''o''}"
  by (simp add: assms receiverspf_ufran spf_ubDom)

text{* If @{term ReceiverSPF} and @{term RecSPF} get the same input, they yield the same result . *}
lemma recspf_receiverspf_ub_eq:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>ReceiverSPF"
  shows "ReceiverSPF \<rightleftharpoons> sb = RecSPF \<rightleftharpoons> sb"
  apply (induction sb rule: ind_ub)
  apply (rule admI)
  using ufunlub_ufun_fun apply force
  defer
  apply (simp add: assms receiverspf_ubdom receiverspf_ufdom recspf_ubdom recspf_ufdom 
                   recspf_strict receiverspf_strict)
  sorry

text{* @{term ReceiverSPF} is equal to @{term RecSPF}. *}
lemma recspf_receiverspf_eq: "ReceiverSPF = RecSPF"
  apply (rule ufun_eqI)
  apply (simp add: receiverspf_ufdom recspf_ufdom)
  by (simp add: recspf_receiverspf_ub_eq ubclDom_ubundle_def)

(* ----------------------------------------------------------------------- *)
  section {* The second medium loses the first acknowledgement test. *}
(* ----------------------------------------------------------------------- *)

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
