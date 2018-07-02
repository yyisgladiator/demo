(*  Title:        Receiver.thy
    Author:       Marlene Lutz
    E-Mail:       marlene.lutz@rwth-aachen.de

    Description:  Theory for Receiver Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for Receiver Lemmata on Time-synchronous Streams *}

theory Receiver
imports ReceiverAutomaton 

begin

(* ----------------------------------------------------------------------- *)
  section {* Datatype Conversion *}
(* ----------------------------------------------------------------------- *)

text {* Inverse of A. *}
fun invA :: "Receiver \<Rightarrow> (nat \<times> bool)" where
  "invA (A (n,b)) = (n,b)" |
  "invA n = undefined"

text {* Conversion of a pair (nat,bool) stream into an equivalent receiver stream. *}
definition natbool2abp :: "(nat \<times> bool) tsyn stream \<rightarrow> Receiver tsyn stream" where
  "natbool2abp \<equiv> tsynMap A"

text {* Conversion of a receiver stream into an equivalent pair (nat,bool) stream. *}
definition abp2natbool :: "Receiver tsyn stream \<rightarrow> (nat \<times> bool) tsyn stream" where
  "abp2natbool \<equiv> tsynMap invA"

text {* Inverse of B. *}
fun invB :: "Receiver \<Rightarrow> bool" where
  "invB (B x) = x" |
  "invB x = undefined"

text {* Conversion of a bool stream into an equivalent receiver stream. *}
definition bool2abp :: "bool tsyn stream \<rightarrow> Receiver tsyn stream" where
  "bool2abp \<equiv> tsynMap B"

text {* Conversion of a receiver stream into an equivalent bool stream. *}
definition abp2bool :: "Receiver tsyn stream \<rightarrow> bool tsyn stream" where
  "abp2bool \<equiv> tsynMap invB"

text {* Inverse of C. *}
fun invC :: "Receiver \<Rightarrow> nat" where
  "invC (C x) = x" |
  "invC x = undefined"

text {* Conversion of a nat stream into an equivalent receiver stream. *}
definition nat2abp :: "nat tsyn stream \<rightarrow> Receiver tsyn stream" where
  "nat2abp \<equiv> tsynMap C"

text {* Conversion of a receiver stream into an equivalent nat stream. *}
definition abp2nat :: "Receiver tsyn stream \<rightarrow> nat tsyn stream" where
  "abp2nat \<equiv> tsynMap invC"

(* ----------------------------------------------------------------------- *)
  section {* Receiver Test Streams and Bundles *}
(* ----------------------------------------------------------------------- *)

(* Everything works fine *)

definition recTestInputStreamNoLoss :: "(nat \<times> bool) tsyn stream" where 
  "recTestInputStreamNoLoss \<equiv> <[Msg (1, True), Msg (2, False)]>"

lift_definition recTestInputUbundleNoLoss :: "Receiver tsyn SB" is
  "[\<guillemotright>dr \<mapsto> natbool2abp\<cdot>recTestInputStreamNoLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestInputStreamNoLoss_def
      natbool2abp_def tsynMap_def)

definition recTestOutputStreamArNoLoss :: "bool tsyn stream" where 
  "recTestOutputStreamArNoLoss \<equiv> <[Msg True, Msg False]>"

definition recTestOutputStreamONoLoss :: "nat tsyn stream" where 
  "recTestOutputStreamONoLoss \<equiv> <[Msg 1, Msg 2]>"

lift_definition recTestOutputUbundleNoLoss :: "Receiver tsyn SB" is
  "[o\<guillemotright> \<mapsto> nat2abp\<cdot>recTestOutputStreamONoLoss, ar\<guillemotright> \<mapsto> bool2abp\<cdot>recTestOutputStreamArNoLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestOutputStreamArNoLoss_def
      recTestOutputStreamONoLoss_def bool2abp_def nat2abp_def tsynMap_def rangeI)

(* Second medium loses first acknowledgement *)

definition recTestInputStreamLoseAck :: "(nat \<times> bool) tsyn stream" where 
  "recTestInputStreamLoseAck \<equiv> <[Msg (1, True), Msg (1, True), Msg (2, False)]>"

lift_definition recTestInputUbundleLoseAck :: "Receiver tsyn SB" is
  "[\<guillemotright>dr \<mapsto> natbool2abp\<cdot>recTestInputStreamLoseAck]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestInputStreamLoseAck_def
      natbool2abp_def tsynMap_def)

definition recTestOutputStreamArLoseAck :: "bool tsyn stream" where 
  "recTestOutputStreamArLoseAck \<equiv> <[Msg True, Msg True, Msg False]>"

definition recTestOutputStreamOLoseAck :: "nat tsyn stream" where 
  "recTestOutputStreamOLoseAck \<equiv> <[Msg 1, null, Msg 2]>"

lift_definition recTestOutputUbundleLoseAck :: "Receiver tsyn SB" is
  "[o\<guillemotright> \<mapsto> nat2abp\<cdot>recTestOutputStreamOLoseAck, ar\<guillemotright> \<mapsto> bool2abp\<cdot>recTestOutputStreamArLoseAck]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestOutputStreamOLoseAck_def
      recTestOutputStreamArLoseAck_def bool2abp_def nat2abp_def tsynMap_def rangeI)

(* First medium loses the first and second data one time *)

definition recTestInputStreamLoseDat :: "(nat \<times> bool) tsyn stream" where 
  "recTestInputStreamLoseDat \<equiv> <[null, Msg (1, True), null, Msg (2, False)]>"

lift_definition recTestInputUbundleLoseDat :: "Receiver tsyn SB" is
  "[\<guillemotright>dr \<mapsto> natbool2abp\<cdot>recTestInputStreamLoseDat]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def recTestInputStreamLoseDat_def 
      natbool2abp_def tsynMap_def)

definition recTestOutputStreamArLoseMsg :: "bool tsyn stream" where 
  "recTestOutputStreamArLoseMsg \<equiv> <[null, Msg True, null, Msg False]>"

definition recTestOutputStreamOLoseMsg :: "nat tsyn stream" where 
 "recTestOutputStreamOLoseMsg \<equiv> <[null, Msg 1, null, Msg 2]>"

lift_definition recTestOutputUbundleLoseMsg :: "Receiver tsyn SB" is
  "[o\<guillemotright> \<mapsto> nat2abp\<cdot>recTestOutputStreamOLoseMsg, ar\<guillemotright> \<mapsto> bool2abp\<cdot>recTestOutputStreamArLoseMsg]"
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
definition tsynbRec :: "Receiver tsyn stream ubundle \<rightarrow> Receiver tsyn stream ubundle option" where 
  "tsynbRec \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle [
                     ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
                     o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))
                     ]"

text {* @{term tsynbRec}: Receiver function for Alternating Bit Protocol. *}
definition RecSPF :: "Receiver tsyn SPF" where
  "RecSPF \<equiv> Abs_ufun tsynbRec"

(* ----------------------------------------------------------------------- *)
  section {* Receiver SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynRec} insertion lemma. *}
lemma tsynrec_insert: "tsynRec\<cdot>s = sscanlA tsynRec_h True\<cdot>s"
  by (simp add: tsynRec_def)

text {* @{term tsynRec} test on finite stream. *}
lemma tsynrec_test_finstream:
  "tsynRec\<cdot>(<[Msg(1, False), null, Msg(2, True),Msg(1, False)]>) = <[null, null,Msg 2, Msg 1]>"
  by (simp add: tsynrec_insert)

text {* @{term tsynRec} test on infinite stream. *}
lemma tsynrec_test_infstream: 
  "tsynRec\<cdot>((<[Msg(1, False), null, Msg(2, True),Msg(1, False)]>)\<infinity>) 
     = (<[null, null, Msg 2, Msg 1]>)\<infinity>"
  apply (simp add: tsynrec_insert)
  oops

lemma tsynbrec_ubwell [simp]:
 "ubWell [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(x  .  \<guillemotright>dr))),
          o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(x  .  \<guillemotright>dr)))]"
  apply (simp add: ubWell_def)
  apply (simp add: usclOkay_stream_def)
  apply (simp add: nat2abp_def bool2abp_def)
  apply (simp add: ctype_tsyn_def tsynMap_def)
  apply (simp add: smap_sdom)
  apply (simp add: image_subset_iff image_iff range_eqI)
  apply (rule)
  using tsynApplyElem.elims apply blast
  using tsynApplyElem.elims by blast

lemma tsynbrec_ubundle_ubdom: "ubDom\<cdot>(Abs_ubundle 
              [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))]) = {ar\<guillemotright>, o\<guillemotright>}"
  by (simp add: ubDom_def insert_commute)

lemma tsynbrec_lub_ubwell: 
  "ubWell (\<Squnion>i::nat. [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>Rep_ubundle (Y i)\<rightharpoonup>\<guillemotright>dr)), 
                     o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>Rep_ubundle (Y i)\<rightharpoonup>\<guillemotright>dr))])"
  sorry

lemma tsynbrec_mono [simp]:
  "monofun (\<lambda> sb. (ubDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle [
              ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
              o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))])"
  apply(fold ubclDom_ubundle_def)
  apply (rule ufun_monoI2)
  by (simp add: below_ubundle_def cont_pref_eq1I fun_belowI some_below)

lemma tsynbrec_chain: "chain Y \<Longrightarrow>
  chain (\<lambda>i::nat. [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(Y i  .  \<guillemotright>dr))), 
                   o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(Y i  .  \<guillemotright>dr)))])"
  apply (rule chainI)
  by (simp add: fun_below_iff monofun_cfun_arg po_class.chainE some_below)

lemma tsynbrec_ubundle_chain: "chain Y \<Longrightarrow>
  chain (\<lambda>i::nat. Abs_ubundle 
        [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(Y i  .  \<guillemotright>dr))),
         o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(Y i  .  \<guillemotright>dr)))])"
  apply (rule chainI)
  apply (simp add: below_ubundle_def)
  by (simp add: fun_below_iff monofun_cfun_arg po_class.chainE some_below)

lemma tsynbrec_chain2: " chain Y \<Longrightarrow>
  chain (\<lambda>i::nat. [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>Rep_ubundle (Y i)\<rightharpoonup>\<guillemotright>dr)), 
                   o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>Rep_ubundle (Y i)\<rightharpoonup>\<guillemotright>dr))])"
  by (metis (no_types, lifting) po_class.chain_def tsynbrec_chain ubgetch_insert)

lemma tsynbrec_ar_contlub: assumes "chain Y"
  shows "bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(\<Squnion>i. Y i  .  \<guillemotright>dr))) 
  = (\<Squnion>i. (bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(((Y i.  \<guillemotright>dr)))))))"
  by (simp add: assms contlub_cfun_arg)

lemma tsynbrec_o_contlub: assumes "chain Y"
  shows "nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(\<Squnion>i. Y i  .  \<guillemotright>dr))) 
  = (\<Squnion>i. (nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(((Y i.  \<guillemotright>dr)))))))"
  by (simp add: assms contlub_cfun_arg)

lemma tsynbrec_cont [simp]:
  "cont (\<lambda> sb. (ubDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle [
               ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))])"
  apply(fold ubclDom_ubundle_def)
  apply (rule ufun_contI)
  apply (rule ub_below)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: ubgetch_ubrep_eq monofun_cfun_arg)
  apply (simp add: ubclDom_ubundle_def)
  apply (rule ub_below)
  apply (metis (no_types, lifting) tsynbrec_ubundle_chain tsynbrec_ubundle_ubdom ubdom_chain_eq2)
  apply (simp add: tsynbrec_ubundle_ubdom ubgetch_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq ubgetch_lub tsynbrec_ar_contlub tsynbrec_o_contlub tsynbrec_chain)
  by (simp add: ubgetch_insert tsynbrec_lub_ubwell part_the_lub tsynbrec_chain2)

lemma tsynbrec_insert: "tsynbRec\<cdot>sb = (ubDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle 
              [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))]"
   by (simp add: tsynbRec_def ubclDom_ubundle_def)

lemma tsynbrec_ufwell [simp]: "ufWell tsynbRec"
  apply (rule ufun_wellI)
  apply (simp_all add: tsynbRec_def domIff2 ubclDom_ubundle_def)
  by (simp add: tsynbrec_ubundle_ubdom)

lemma recspf_insert: "RecSPF \<rightleftharpoons> sb = (Abs_ufun tsynbRec) \<rightleftharpoons> sb"
  by (simp add: RecSPF_def)

lemma recspf_ufdom: "ufDom\<cdot>RecSPF = {\<guillemotright>dr}"
  apply(simp add: ufDom_def)
  proof -
    show "ubclDom\<cdot>(SOME b::Receiver tsyn stream\<^sup>\<Omega>. b \<in> dom (Rep_cufun RecSPF)) =  {\<guillemotright>dr}" 
      proof -
        have "b \<in> dom (Rep_cufun RecSPF) \<Longrightarrow> ubclDom\<cdot>b  = {\<guillemotright>dr}"
          proof - 
            have "ubclDom\<cdot>b  \<noteq> {\<guillemotright>dr} \<Longrightarrow> b \<notin> dom (Rep_cufun RecSPF)" 
              proof -
                assume "ubclDom\<cdot>b  \<noteq> {\<guillemotright>dr}"
                hence "(Rep_ufun RecSPF)\<cdot>b = None" 
                  proof -
                    have "tsynbRec\<cdot>b = None" using \<open>ubclDom\<cdot>(b::Receiver tsyn stream\<^sup>\<Omega>) \<noteq> {\<guillemotright>dr}\<close> 
                      tsynbrec_insert ubclDom2ubDom by auto
                    thus ?thesis  by (simp add: RecSPF_def)
                  qed
                thus "b \<notin> dom (Rep_cufun RecSPF)" by (simp add: domIff)
              qed
            thus "b \<in> dom (Rep_cufun RecSPF) \<Longrightarrow> ubclDom\<cdot>b  = {\<guillemotright>dr}" by blast
          qed
        thus ?thesis 
          proof -
            have "ufDom\<cdot>RecSPF = {\<guillemotright>dr}"
              by (metis RecSPF_def rep_abs_cufun2 tsynbnull_ubdom tsynbrec_insert tsynbrec_ufwell ubclDom2ubDom ufdom_2ufundom)
            then show ?thesis by (simp add: ufdom_insert)
          qed
      qed
  qed

lemma recspf_ufran: "ufRan\<cdot>RecSPF = {ar\<guillemotright>, o\<guillemotright>}"
  apply(simp add: ufRan_def)
  proof -
    show "ubclDom\<cdot>(SOME sbout::Receiver tsyn stream\<^sup>\<Omega>. sbout \<in> ran (Rep_cufun RecSPF)) = {ar\<guillemotright>, o\<guillemotright>}" 
      proof -
        have "sbout \<in> ran (Rep_cufun RecSPF) \<Longrightarrow> ubclDom\<cdot>sbout = {ar\<guillemotright>, o\<guillemotright>} " 
          proof -
            assume ass:"sbout \<in> ran (Rep_cufun RecSPF)"
            hence ex_input : "\<exists>sbin. (Rep_cufun RecSPF) sbin = Some sbout"  by simp
            obtain sbin where "(Rep_cufun RecSPF) sbin = Some sbout" using ex_input by auto
            hence "(Rep_cufun RecSPF) sbin = Some ( Abs_ubundle [
                     ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sbin  .  \<guillemotright>dr))), 
                     o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sbin  .  \<guillemotright>dr)))
                     ])"  by (metis RecSPF_def recspf_ufdom rep_abs_cufun2 tsynbrec_insert
                              tsynbrec_ufwell ubclDom2ubDom ufdom_2ufundom)
            hence "ubclDom\<cdot>(sbout) = {ar\<guillemotright>, o\<guillemotright>}"  
              using \<open>Rep_cufun RecSPF (sbin::Receiver tsyn stream\<^sup>\<Omega>)
                      = Some (sbout::Receiver tsyn stream\<^sup>\<Omega>)\<close> 
                     tsynbrec_ubundle_ubdom ubclDom2ubDom by auto
            thus ?thesis by blast
          qed
        thus ?thesis 
          proof -
            have "\<forall>u. ubDom\<cdot>Rep_cfun tsynbRec\<rightharpoonup>u = {ar\<guillemotright>, o\<guillemotright>} \<or> ubDom\<cdot>u \<noteq> {\<guillemotright>dr}"
              by (simp add: tsynbrec_insert tsynbrec_ubundle_ubdom ubclDom_ubundle_def)
          then show ?thesis
            by (metis (no_types) RecSPF_def recspf_ufdom rep_abs_cufun2 spf_ubDom tsynbrec_ufwell
                ubclDom2ubDom ufdom_insert ufran_insert)
          qed
      qed
  qed

lemma recspf_ubdom: 
  assumes "ubDom\<cdot>sb = ufDom\<cdot>RecSPF"
  shows "ubDom\<cdot>(RecSPF \<rightleftharpoons> sb) = {ar\<guillemotright>, o\<guillemotright>}"
  by (simp add: assms recspf_ufran spf_ubDom)

lemma recspf_strict: "RecSPF \<rightleftharpoons> ubclLeast{\<guillemotright>dr} = ubclLeast{ar\<guillemotright>, o\<guillemotright>}"
  proof -
    have "ubclLeast{\<guillemotright>dr} = ubLeast{\<guillemotright>dr}" by (simp add: ubclLeast_ubundle_def)
    hence "ubclLeast{\<guillemotright>dr} = Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<epsilon> )"  by (simp add: ubLeast_def)
    hence "RecSPF \<rightleftharpoons> (Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<epsilon> )) 
           = Abs_ubundle (\<lambda>c. (c \<in> {ar\<guillemotright>, o\<guillemotright>}) \<leadsto> \<epsilon> )"
      proof -
        have ar_is_strict : " bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>\<epsilon>)) = \<epsilon>" 
          by(simp add: abp2natbool_def bool2abp_def)
        have o_is_strict : "nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(\<epsilon>))) = \<epsilon>" 
          by(simp add: abp2natbool_def tsynRec_def nat2abp_def)
        have eval_recSPF : "RecSPF \<rightleftharpoons> (Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<epsilon> )) = Abs_ubundle [
          ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>((Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<epsilon> ))  .  \<guillemotright>dr))), 
          o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>((Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<epsilon> ))  .  \<guillemotright>dr))) ]"
          by (metis RecSPF_def \<open>ubclLeast {\<guillemotright>dr} 
               = Abs_ubundle (\<lambda>c::channel. (c \<in> {\<guillemotright>dr})\<leadsto>\<epsilon>)\<close> option.sel
               rep_abs_cufun2 tsynbrec_insert tsynbrec_ufwell 
               ubclDom2ubDom ubcldom_least_cs)
        have is_empty_stream : "(Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<epsilon> ))  .  \<guillemotright>dr  = \<epsilon>" 
          by (metis singletonI ubLeast_def ubleast_ubgetch)
        hence recspf_is_strict: "RecSPF \<rightleftharpoons> (Abs_ubundle (\<lambda>c. (c \<in> {\<guillemotright>dr}) \<leadsto> \<bottom> )) = Abs_ubundle [
                     ar\<guillemotright> \<mapsto> \<bottom>, 
                     o\<guillemotright> \<mapsto> \<bottom>
                     ]"  by (metis ar_is_strict eval_recSPF o_is_strict)
        have "Abs_ubundle [   ar\<guillemotright> \<mapsto> \<bottom>, o\<guillemotright> \<mapsto> \<bottom> ] = Abs_ubundle (\<lambda>c. (c \<in> {ar\<guillemotright>, o\<guillemotright>}) \<leadsto> \<bottom> )" 
          by (metis channel.distinct(33) fun_upd_apply insert_iff singletonD)
        from this recspf_is_strict show ?thesis by simp
      qed
    thus "RecSPF \<rightleftharpoons>  ubclLeast{\<guillemotright>dr} = ubclLeast{ar\<guillemotright>, o\<guillemotright>}"
      proof -
        show ?thesis
          by (metis (no_types) \<open>RecSPF \<rightleftharpoons> Abs_ubundle (\<lambda>c::channel. (c \<in> {\<guillemotright>dr})\<leadsto>\<epsilon>) 
              = Abs_ubundle (\<lambda>c::channel. (c \<in> {ar\<guillemotright>, o\<guillemotright>})\<leadsto>\<epsilon>)\<close> ubLeast_def ubclLeast_ubundle_def)
      qed
  qed

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver Transition Lemmata *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lemma receivertransition_rt_true: 
  "receiverTransition (State Rt, [\<guillemotright>dr \<mapsto> (Msg (A (a, True)))])
     = ((State Rf,(createArOutput True) \<uplus> (createOOutput a)))"
  by simp

lemma receivertransition_rt_false: 
  "receiverTransition (State Rt, [\<guillemotright>dr \<mapsto> (Msg (A (a, False)))])
     = ((State Rt,(createArOutput False) \<uplus> (tsynbNull o\<guillemotright>)))"
  by simp

lemma receivertransition_rf_true: 
  "receiverTransition (State Rf, [\<guillemotright>dr \<mapsto> (Msg (A (a, True)))])
     = ((State Rf,(createArOutput True) \<uplus> (tsynbNull o\<guillemotright>)))"
  by simp

lemma receivertransition_rf_false: 
  "receiverTransition (State Rf, [\<guillemotright>dr \<mapsto> (Msg (A (a, False)))])
     = ((State Rt,(createArOutput False) \<uplus> (createOOutput a)))"
  by simp

lemma receivertransition_null: 
  "receiverTransition (State s, [\<guillemotright>dr \<mapsto> null])
     = (State s ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"
  by (cases s, simp_all)

lemma createaroutput_createooutput_ubclunion_ubdom: 
  "ubDom\<cdot>((createArOutput a) \<uplus> (createOOutput b)) = {ar\<guillemotright>, o\<guillemotright>}"
  by (metis createArOutput.rep_eq createOOutput.rep_eq dom_empty dom_fun_upd insert_is_Un 
      option.simps(3) ubclUnion_ubundle_def ubdom_insert ubunionDom)

lemma createaroutput_tsynbnullo_ubclunion_ubdom: 
  "ubDom\<cdot>((createArOutput a) \<uplus> (tsynbNull o\<guillemotright>)) = {ar\<guillemotright>, o\<guillemotright>}"
  by (metis createArOutput.rep_eq dom_fun_upd insert_is_Un option.simps(3) tsynbNull.rep_eq 
      tsynbnull_ubdom ubclUnion_ubundle_def ubdom_insert ubunionDom)

lemma tsynbnullar_tsynbnullo_ubclunion_ubdom:
  "ubDom\<cdot>(tsynbNull ar\<guillemotright> \<uplus> tsynbNull o\<guillemotright>) = {ar\<guillemotright>, o\<guillemotright>}"
  by (metis insert_is_Un tsynbnull_ubdom ubclUnion_ubundle_def ubunionDom)

lemma receivertransition_ubdom:
  assumes dom_f: "dom f = {\<guillemotright>dr}" 
    and ubelemwell_f: "sbElemWell f"
  shows "ubDom\<cdot>(snd (receiverTransition (s, f))) = {ar\<guillemotright>, o\<guillemotright>}"
  proof -
    obtain inp where f_def: "f = [\<guillemotright>dr \<mapsto> inp]"
      using dom_eq_singleton_conv dom_f by force
    obtain st where s_def: "s = State st"
      using ReceiverAutomaton.getSubState.cases by blast
    have "ubDom\<cdot>(snd (receiverTransitionH (ReceiverState.State st, inp))) = {ar\<guillemotright>, o\<guillemotright>}"
      proof (cases inp)
        case (Msg i)
          hence "i \<in> ctype \<guillemotright>dr"
          using assms
          by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
        then obtain a where i_def: "i = A a"
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
    then show "ubDom\<cdot>(snd (receiverTransition (s, f))) =  {ar\<guillemotright>, o\<guillemotright>}"
      by (simp add: f_def s_def)
  qed

lemma receivertransition_automaton_well:
  "automaton_well (receiverTransition, ReceiverState.State Rt, tsynbNull ar\<guillemotright> \<uplus> tsynbNull o\<guillemotright>, 
                   {\<guillemotright>dr}, {ar\<guillemotright>, o\<guillemotright>})"
  using receivertransition_ubdom by auto

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver Step Lemmata *}
(* ----------------------------------------------------------------------- *) 

lemma receiverautomaton_h_step_ubdom_null_null:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "ubDom\<cdot>(ubConc (tsynbNull ar\<guillemotright> \<uplus> tsynbNull o\<guillemotright>)
                  \<cdot>(h ReceiverAutomaton (ReceiverState.State s) \<rightleftharpoons> sb)) = {ar\<guillemotright>, o\<guillemotright>}"
  apply (simp add: tsynbnullar_tsynbnullo_ubclunion_ubdom)
  apply (subst h_out_dom)
  apply (simp add: assms getDom_def ReceiverAutomaton.rep_eq)
  by (simp add: assms ReceiverAutomaton.rep_eq  getRan_def insert_commute)

lemma receiverautomaton_h_step_ubdom_ar_null:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "ubDom\<cdot>(ubConc ((createArOutput x) \<uplus> (tsynbNull o\<guillemotright>))
                  \<cdot>(h ReceiverAutomaton (ReceiverState.State s) \<rightleftharpoons> sb)) = {ar\<guillemotright>, o\<guillemotright>}"
  apply (simp add: createaroutput_tsynbnullo_ubclunion_ubdom)
  apply (subst h_out_dom)
  apply (simp add: assms getDom_def ReceiverAutomaton.rep_eq)
  by (simp add: assms ReceiverAutomaton.rep_eq  getRan_def insert_commute)

lemma receiverautomaton_h_step_ubdom_ar_o: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "ubDom\<cdot>(ubConc ((createArOutput x) \<uplus> (createOOutput y))
                  \<cdot>(h ReceiverAutomaton (ReceiverState.State s) \<rightleftharpoons> sb)) = {ar\<guillemotright>, o\<guillemotright>}"
  apply (simp add: createaroutput_createooutput_ubclunion_ubdom)
  apply (subst h_out_dom)
  apply (simp add: assms getDom_def ReceiverAutomaton.rep_eq)
  by (simp add: assms ReceiverAutomaton.rep_eq  getRan_def insert_commute)

lemma msga_ctype: "Msg (A a) \<in> ctype \<guillemotright>dr"
  by (simp add: ctype_tsynI)

lemma msga_createbundle_ubgetch [simp]: "(createBundle (Msg (A a)) \<guillemotright>dr) . \<guillemotright>dr = \<up>(Msg (A a))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by (simp add: msga_ctype)

lemma msga_createbundle_ubconc [simp]:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb .  \<guillemotright>dr = \<up>(Msg (A a)) \<bullet> (sb.  \<guillemotright>dr)"
  by (simp add: assms usclConc_stream_def)

lemma msga_createbundle_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
  shows "sbRt\<cdot>(ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms)
  by (simp add: assms sbRt_def usclConc_stream_def)

lemma tsynbnull_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull \<guillemotright>dr)\<cdot>sb)) = [\<guillemotright>dr \<mapsto> null]"
  apply (rule convDiscrUp_eqI)
  apply (subst convdiscrup_inv_eq)
  apply (simp add: assms sbHdElem_def sbHdElem_cont domIff2 usclConc_stream_def)+
  apply (subst fun_eq_iff, rule)
  apply (case_tac "x = \<guillemotright>dr")
  apply (simp add: convDiscrUp_def)
  apply (subst ubConc_usclConc_eq)
  apply (simp_all add: assms usclConc_stream_def up_def)
  by (metis convDiscrUp_dom domIff fun_upd_apply)

lemma createaroutput_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb)) = [\<guillemotright>dr \<mapsto> Msg (A a)]"
  apply (rule convDiscrUp_eqI)
  apply (subst convdiscrup_inv_eq)
  apply (simp add: assms sbHdElem_def sbHdElem_cont domIff2 usclConc_stream_def)+
  apply (subst fun_eq_iff, rule)
  apply (case_tac "x = \<guillemotright>dr")
  apply (simp add: convDiscrUp_def)
  apply (subst ubConc_usclConc_eq)
  apply (simp_all add: assms usclConc_stream_def up_def)
  by (metis convDiscrUp_dom domIff fun_upd_apply)

(* h_step lemma for state rf and input null *)
lemma receiverautomaton_h_step_rf_null: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (tsynbNull \<guillemotright>dr)\<cdot>sb) 
           = ubConc ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))\<cdot>(h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* h_step lemma for state Rt and input null *)
lemma receiverautomaton_h_step_rt_null: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (tsynbNull \<guillemotright>dr)\<cdot>sb) 
           = ubConc ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))\<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* h_step lemma for state Rf and input true *)
lemma receiverautomaton_h_step_rf_true:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
    and "(snd a) = True"
  shows "h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) 
           = ubConc (createArOutput (snd a) \<uplus> (tsynbNull o\<guillemotright>))
               \<cdot>(h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

(* h_step lemma for state Rt and input true *)
lemma receiverautomaton_h_step_rt_true: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
    and "(snd a) = True"
  shows "h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb)
           = ubConc (createArOutput (snd a) \<uplus> (createOOutput (fst a)))
               \<cdot>(h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

(* h_step lemma for state Rf and input false *)
lemma receiverautomaton_h_step_rf_false: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
    and "(snd a) = False"
  shows "h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) 
           = ubConc (createArOutput (snd a) \<uplus> createOOutput (fst a))
               \<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

(* h_step lemma for state Rt and input false *)
lemma receiverautomaton_h_step_rt_false: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
    and "(snd a) = False"
  shows "h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) 
           = ubConc (createArOutput (snd a) \<uplus> (tsynbNull o\<guillemotright>))
               \<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def usclConc_stream_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

(* H_step lemma *)
lemma receiverautomaton_H_step:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "H ReceiverAutomaton \<rightleftharpoons> sb 
           = ubConc ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))\<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp add: H_def h_out_dom getRan_def getInitialState_def getInitialOutput_def 
         ReceiverAutomaton.rep_eq getDom_def assms)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* ----------------------------------------------------------------------- *)
  section {* Automaton Receiver SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lemma receiverspf_strict: "ReceiverSPF \<rightleftharpoons> ubclLeast{\<guillemotright>dr} = ubclLeast{ar\<guillemotright>, o\<guillemotright>}"
  sorry

lemma receiverspf_ufdom: "ufDom\<cdot>ReceiverSPF = {\<guillemotright>dr}"
  apply (simp add: ReceiverSPF_def H_def ReceiverAutomaton_def getDom_def)
  using ReceiverAutomaton.abs_eq ReceiverAutomaton.rep_eq by auto

lemma receiverspf_ufran: "ufRan\<cdot>ReceiverSPF = {ar\<guillemotright>, o\<guillemotright>}"
  sorry

lemma receiverspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>ReceiverSPF"
  shows "ubDom\<cdot>(ReceiverSPF \<rightleftharpoons> sb) = {ar\<guillemotright>, o\<guillemotright>}"
  by (simp add: assms receiverspf_ufran spf_ubDom)

lemma recspf_receiverspf_ub_eq:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>ReceiverSPF" 
  shows "ReceiverSPF \<rightleftharpoons> sb = RecSPF \<rightleftharpoons> sb"
  apply (rule ub_eq)
  apply (simp add: assms receiverspf_ubdom receiverspf_ufdom recspf_ubdom recspf_ufdom)
  sorry

lemma recspf_receiverspf_eq: "ReceiverSPF = RecSPF"
  apply (rule ufun_eqI)
  apply (simp add: receiverspf_ufdom recspf_ufdom)
  by (simp add: recspf_receiverspf_ub_eq ubclDom_ubundle_def)


end