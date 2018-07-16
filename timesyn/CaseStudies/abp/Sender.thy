(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Theory for Automaton Sender Lemmata.
*)

chapter {* Theory for Sender Automaton Lemmata *}

theory Sender
imports SenderAutomaton Components

begin

(* ----------------------------------------------------------------------- *)
  section {* Sender Test Streams and Bundles *}
(* ----------------------------------------------------------------------- *)

(* Everything works fine for two messages therefore sender changes state *)

definition sndTestInputStreamINoLoss :: "nat tsyn stream" where 
  "sndTestInputStreamINoLoss \<equiv> <[Msg 1, Msg 2, Msg 1, null]>"

definition sndTestInputStreamAsNoLoss :: "bool tsyn stream" where 
  "sndTestInputStreamAsNoLoss \<equiv> <[null, Msg True, Msg False, Msg True]>"

lift_definition sndTestInputUbundleNoLoss :: "abpMessage tsyn SB" is
  "[\<C> ''i'' \<mapsto> nat2abp\<cdot>sndTestInputStreamINoLoss, \<C> ''as'' \<mapsto> bool2abp\<cdot>sndTestInputStreamAsNoLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestInputStreamINoLoss_def 
      sndTestInputStreamAsNoLoss_def bool2abp_def nat2abp_def tsynMap_def rangeI)

definition sndTestOutputStreamNoLoss :: "(nat \<times> bool) tsyn stream" where 
  "sndTestOutputStreamNoLoss \<equiv> <[Msg (1, True), Msg (2, False), Msg (1, True), null]>"

lift_definition sndTestOutputUbundleNoLoss :: "abpMessage tsyn SB" is
  "[\<C> ''ds'' \<mapsto> natbool2abp\<cdot>sndTestOutputStreamNoLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestOutputStreamNoLoss_def 
      natbool2abp_def tsynMap_def)

(* One medium loses data or acknowledgement *)

definition sndTestInputStreamIOneLoss :: "nat tsyn stream" where 
  "sndTestInputStreamIOneLoss \<equiv> <[Msg 1, null, Msg 2, null]>"

definition sndTestInputStreamAsOneLoss :: "bool tsyn stream" where 
  "sndTestInputStreamAsOneLoss \<equiv> <[null, null, Msg True, Msg False]>"

lift_definition sndTestInputUbundleOneLoss :: "abpMessage tsyn SB" is
  "[\<C> ''i'' \<mapsto> nat2abp\<cdot>sndTestInputStreamIOneLoss,
    \<C> ''as'' \<mapsto> bool2abp\<cdot>sndTestInputStreamAsOneLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestInputStreamAsOneLoss_def
      sndTestInputStreamIOneLoss_def nat2abp_def bool2abp_def tsynMap_def rangeI)

definition sndTestOutputStreamOneLoss :: "(nat \<times> bool) tsyn stream" where 
  "sndTestOutputStreamOneLoss \<equiv> <[Msg (1, True), Msg (1, True), Msg (2, False), null]>"

lift_definition sndTestOutputUbundleOneLoss :: "abpMessage tsyn SB" is
  "[\<C> ''ds'' \<mapsto> natbool2abp\<cdot>sndTestOutputStreamOneLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestOutputStreamOneLoss_def 
      natbool2abp_def tsynMap_def)

(* Two messages are successive lost by medium therefore there are two messages in the buffer *)
definition sndTestInputStreamITwoLoss :: "nat tsyn stream" where
  "sndTestInputStreamITwoLoss \<equiv> <[Msg 1, Msg 2, Msg 3, null, null, null]>"

definition sndTestInputStreamAsTwoLoss :: "bool tsyn stream" where 
  "sndTestInputStreamAsTwoLoss \<equiv> <[null, null, null, Msg True, Msg False, Msg True]>"

lift_definition sndTestInputUbundleTwoLoss :: "abpMessage tsyn SB" is
  "[\<C> ''i'' \<mapsto> nat2abp\<cdot>sndTestInputStreamITwoLoss, \<C> ''as'' \<mapsto> bool2abp\<cdot>sndTestInputStreamAsTwoLoss]" 
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestInputStreamITwoLoss_def
      sndTestInputStreamAsTwoLoss_def nat2abp_def bool2abp_def tsynMap_def rangeI)

definition sndTestOutputStreamTwoLoss :: "(nat \<times> bool) tsyn stream" where 
  "sndTestOutputStreamTwoLoss \<equiv> <[Msg (1, True), Msg (1, True), Msg (1, True), Msg (2, False), 
                                  Msg (3, True), null]>"

lift_definition sndTestOutputUbundleTwoLoss :: "abpMessage tsyn SB" is
  "[\<C> ''ds'' \<mapsto> natbool2abp\<cdot>sndTestOutputStreamTwoLoss]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def sndTestOutputStreamTwoLoss_def 
      natbool2abp_def tsynMap_def)

(* ----------------------------------------------------------------------- *)
  section {* Automaton Sender Transition Lemmata *}
(* ----------------------------------------------------------------------- *)

lemma createdsoutput_ubdom:
  "ubDom\<cdot>(createDsBundle a) = {\<C> ''ds''}"
  by (metis createDsBundle.rep_eq dom_empty dom_fun_upd option.simps(3) ubdom_insert)

lemma sendertransition_ubdom:
  assumes dom_f: "dom f = {\<C> ''i'', \<C> ''as''}" and ubelemwell_f: "sbElemWell f"
  shows "ubDom\<cdot>(snd (senderTransition (s, f))) = {\<C> ''ds''}"
  proof -
    obtain inp_i inp_as where f_def: "f = [\<C> ''i'' \<mapsto> inp_i, \<C> ''as'' \<mapsto> inp_as]"
  (* ToDo: remove smt. *)
      by (smt assms domD dom_eq_singleton_conv dom_fun_upd fun_upd_def fun_upd_triv fun_upd_twist 
          fun_upd_upd insertI1 insert_absorb)
    obtain st buf where s_def: "s = State st buf"
      using SenderAutomaton.getSubState.cases by blast
    have "ubDom\<cdot>(snd (senderTransitionH (SenderState.State st buf, inp_i,inp_as ))) = {\<C> ''ds''}"
      proof (cases inp_i)
        case (Msg i)
        hence msg_i: "inp_i = Msg i" 
          by simp
        hence "i \<in> ctype (\<C> ''i'')"
          using assms by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
        then obtain inp where i_def: "i = Nat inp"
          by auto
        then show ?thesis
          proof (cases inp_as)
            case (Msg ack)
            hence msg_as: "inp_as = Msg ack" 
              by simp
            hence "ack \<in> ctype (\<C> ''as'')"
              using assms by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
            then obtain a where as_def: "ack = Bool a"
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
            hence "ack \<in> ctype (\<C> ''as'')"
              using assms by (simp add: dom_f f_def sbElemWell_def ctype_tsyn_def image_def)
            then obtain a where as_def: "ack = Bool a"
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
    then show "ubDom\<cdot>(snd (senderTransition (s, f))) = {\<C> ''ds''}"
      using f_def s_def by force
  qed

lemma sendertransition_automaton_well:
  "daWell (senderTransition, State Sf [], tsynbNull (\<C> ''ds''), {\<C> ''i'', \<C> ''as''}, {\<C> ''ds''})"
  using sendertransition_ubdom by simp

end