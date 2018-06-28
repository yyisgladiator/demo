(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Theory for Automaton Sender Lemmata.
*)

chapter {* Theory for Sender Automaton Lemmata *}

theory Sender
imports SenderAutomaton 

begin

(* ----------------------------------------------------------------------- *)
  section {* Datatype Conversion *}
(* ----------------------------------------------------------------------- *)

text {* Inverse of C. *}
fun invC :: "Sender \<Rightarrow> (nat \<times> bool)" where
  "invC (C (n,b)) = (n,b)" |
  "invC n = undefined"

text {* Conversion of a pair (nat,bool) stream into an equivalent receiver stream. *}
definition natbool2abp :: "(nat \<times> bool) tsyn stream \<rightarrow> Sender tsyn stream" where
  "natbool2abp \<equiv> tsynMap C"

text {* Conversion of a receiver stream into an equivalent pair (nat,bool) stream. *}
definition abp2natbool :: "Sender tsyn stream \<rightarrow> (nat \<times> bool) tsyn stream" where
  "abp2natbool \<equiv> tsynMap invC"

text {* Inverse of B. *}
fun invB :: "Sender \<Rightarrow> bool" where
  "invB (B x) = x" |
  "invB x = undefined"

text {* Conversion of a bool stream into an equivalent receiver stream. *}
definition bool2abp :: "bool tsyn stream \<rightarrow> Sender tsyn stream" where
  "bool2abp \<equiv> tsynMap B"

text {* Conversion of a receiver stream into an equivalent bool stream. *}
definition abp2bool :: "Sender tsyn stream \<rightarrow> bool tsyn stream" where
  "abp2bool \<equiv> tsynMap invB"

text {* Inverse of C. *}
fun invA :: "Sender \<Rightarrow> nat" where
  "invA (A x) = x" |
  "invA x = undefined"

text {* Conversion of a nat stream into an equivalent receiver stream. *}
definition nat2abp :: "nat tsyn stream \<rightarrow> Sender tsyn stream" where
  "nat2abp \<equiv> tsynMap A"

text {* Conversion of a receiver stream into an equivalent nat stream. *}
definition abp2nat :: "Sender tsyn stream \<rightarrow> nat tsyn stream" where
  "abp2nat \<equiv> tsynMap invA"

(* ----------------------------------------------------------------------- *)
  section {* Sender Test Streams and Bundles *}
(* ----------------------------------------------------------------------- *)

(* Everything works fine for two messages therefore sender changes state *)

definition sndTestInputStreamINoLoss :: "nat tsyn stream" where 
  "sndTestInputStreamINoLoss \<equiv> <[Msg 1, Msg 2, Msg 1, null]>"

definition sndTestInputStreamAsNoLoss :: "bool tsyn stream" where 
  "sndTestInputStreamAsNoLoss \<equiv> <[null, Msg True, Msg False, Msg True]>"

lift_definition sndTestInputUbundleNoLoss :: "Sender tsyn SB" is
  "[\<guillemotright>i \<mapsto> nat2abp\<cdot>sndTestInputStreamINoLoss, \<guillemotright>as \<mapsto> bool2abp\<cdot>sndTestInputStreamAsNoLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestInputStreamINoLoss_def 
      sndTestInputStreamAsNoLoss_def bool2abp_def nat2abp_def tsynMap_def rangeI)

definition sndTestOutputStreamNoLoss :: "(nat \<times> bool) tsyn stream" where 
  "sndTestOutputStreamNoLoss \<equiv> <[Msg (1, True), Msg (2, False), Msg (1, True), null]>"

lift_definition sndTestOutputUbundleNoLoss :: "Sender tsyn SB" is
  "[ds\<guillemotright> \<mapsto> natbool2abp\<cdot>sndTestOutputStreamNoLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestOutputStreamNoLoss_def 
      natbool2abp_def tsynMap_def)

(* One medium loses data or acknowledgement *)

definition sndTestInputStreamIOneLoss :: "nat tsyn stream" where 
  "sndTestInputStreamIOneLoss \<equiv> <[Msg 1, null, Msg 2, null]>"

definition sndTestInputStreamAsOneLoss :: "bool tsyn stream" where 
  "sndTestInputStreamAsOneLoss \<equiv> <[null, null, Msg True, Msg False]>"

lift_definition sndTestInputUbundleOneLoss :: "Sender tsyn SB" is
  "[\<guillemotright>i \<mapsto> tsynMap A\<cdot>sndTestInputStreamIOneLoss,
    \<guillemotright>as \<mapsto> tsynMap B\<cdot>sndTestInputStreamAsOneLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestInputStreamAsOneLoss_def
      sndTestInputStreamIOneLoss_def tsynMap_def rangeI)

definition sndTestOutputStreamOneLoss :: "(nat \<times> bool) tsyn stream" where 
  "sndTestOutputStreamOneLoss \<equiv> <[Msg (1, True), Msg (1, True), Msg (2, False), null]>"

lift_definition sndTestOutputUbundleOneLoss :: "Sender tsyn SB" is
  "[ds\<guillemotright> \<mapsto> natbool2abp\<cdot>sndTestOutputStreamOneLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestOutputStreamOneLoss_def 
      natbool2abp_def tsynMap_def)

(* Two messages are successive lost by medium therefore there are two messages in the buffer *)
definition sndTestInputStreamITwoLoss :: "nat tsyn stream" where
  "sndTestInputStreamITwoLoss \<equiv> <[Msg 1, Msg 2, Msg 3, null, null, null]>"

definition sndTestInputStreamAsTwoLoss :: "bool tsyn stream" where 
  "sndTestInputStreamAsTwoLoss \<equiv> <[null, null, null, Msg True, Msg False, Msg True]>"

lift_definition sndTestInputUbundleTwoLoss :: "Sender tsyn SB" is
  "[\<guillemotright>i \<mapsto> nat2abp\<cdot>sndTestInputStreamITwoLoss, \<guillemotright>as \<mapsto> bool2abp\<cdot>sndTestInputStreamAsTwoLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestInputStreamITwoLoss_def
      sndTestInputStreamAsTwoLoss_def nat2abp_def bool2abp_def tsynMap_def rangeI)

definition sndTestOutputStreamTwoLoss :: "(nat \<times> bool) tsyn stream" where 
  "sndTestOutputStreamTwoLoss \<equiv> <[Msg (1, True), Msg (1, True), Msg (1, True), Msg (2, False), 
                                  Msg (3, True), null]>"

lift_definition sndTestOutputUbundleTwoLoss :: "Sender tsyn SB" is
  "[ds\<guillemotright> \<mapsto> natbool2abp\<cdot>sndTestOutputStreamTwoLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestOutputStreamTwoLoss_def 
      natbool2abp_def tsynMap_def)

(* ----------------------------------------------------------------------- *)
  section {* Automaton Sender Transition Lemmata *}
(* ----------------------------------------------------------------------- *)

lemma createdsoutput_ubdom:
  "ubDom\<cdot>(createDsOutput a) = {ds\<guillemotright>}"
  by (metis createDsOutput.rep_eq dom_empty dom_fun_upd option.simps(3) ubdom_insert)

lemma sendertransition_ubdom:
  assumes dom_f: "dom f = {\<guillemotright>i, \<guillemotright>as}" and ubelemwell_f: "sbElemWell f"
  shows "ubDom\<cdot>(snd (senderTransition (s, f))) = {ds\<guillemotright>}"
  proof -
    obtain inp_i inp_as where f_def: "f = [\<guillemotright>i \<mapsto> inp_i, \<guillemotright>as \<mapsto> inp_as]"
      using dom2exElem dom_f by blast
    obtain st buf where s_def: "s = State st buf"
      using SenderAutomaton.getSubState.cases by blast
    have "ubDom\<cdot>(snd (senderTransitionH (SenderState.State st buf, inp_i,inp_as ))) = {ds\<guillemotright>}"
      proof (cases inp_i)
        case (Msg i)
        hence msg_i: "inp_i = Msg i" 
          by simp
        hence "i \<in> ctype \<guillemotright>i"
          using assms by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
        then obtain inp where i_def: "i = A inp"
          by auto
        then show ?thesis
          proof (cases inp_as)
            case (Msg ack)
            hence msg_as: "inp_as = Msg ack" 
              by simp
            hence "ack \<in> ctype \<guillemotright>as"
              using assms by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
            then obtain a where as_def: "ack = B a"
              by auto
            then show ?thesis
              proof (cases st)
                case Sf
                then show ?thesis
                  by (simp add: msg_as msg_i i_def as_def createdsoutput_ubdom) 
              next
                case St
                then show ?thesis
                  by (simp add: msg_as msg_i i_def as_def createdsoutput_ubdom) 
              qed
          next
            case null
            then show ?thesis 
              proof (cases st)
                case Sf
                then show ?thesis
                  by (simp add: msg_i i_def createdsoutput_ubdom null) 
              next
                case St
                then show ?thesis
                  by (simp add: msg_i i_def createdsoutput_ubdom null) 
              qed
          qed
      next
        case null
        hence null_i: "inp_i = null" 
          by simp
        then show ?thesis
          proof (cases inp_as)
            case (Msg ack)
            hence "ack \<in> ctype \<guillemotright>as"
              using assms by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
            then obtain a where as_def: "ack = B a"
              by auto
            then show ?thesis
              proof (cases st)
                case Sf
                then show ?thesis
                  by (simp add: null_i Msg as_def createdsoutput_ubdom) 
              next
                case St
                then show ?thesis
                  by (simp add: null_i Msg as_def createdsoutput_ubdom) 
              qed
          next
            case null
            hence null_as: "inp_as = null" 
              by simp
            then show ?thesis 
              proof (cases st)
                case Sf
                then show ?thesis
                  by (simp add: null_i null_as createdsoutput_ubdom) 
              next
                case St
                then show ?thesis
                  by (simp add: null_i null_as createdsoutput_ubdom) 
              qed
          qed
      qed
    then show "ubDom\<cdot>(snd (senderTransition (s, f))) = {ds\<guillemotright>}"
      using f_def s_def by force
  qed

lemma sendertransition_automaton_well:
  "automaton_well (senderTransition, SenderState.State Sf [], tsynbNull ds\<guillemotright>, {\<guillemotright>i,\<guillemotright>as }, {ds\<guillemotright>})"
  using sendertransition_ubdom by simp

end