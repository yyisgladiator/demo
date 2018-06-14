(*  Title:        Components.thy
    Author:       Dennis Slotboom, Annika Savelsberg
    E-Mail:       dennis.slotboom@rwth-aachen.de, annika.savelsberg@rwth-aachen.de

    Description:  Theory for ABP Component Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for ABP Component Lemmata on Time-synchronous Streams *}

theory Components
imports ReceiverAutomaton SenderAutomaton

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

lemma tsynbrec_ubundle_ubdom: "ubDom\<cdot>(Abs_ubundle 
              [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))]) = {ar\<guillemotright>, o\<guillemotright>}"
  sorry

lemma tsynbrec_mono [simp]:
  "monofun (\<lambda> sb. (ubclDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle [
               ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))])"
  sorry

lemma tsynbrec_cont [simp]:
  "cont (\<lambda> sb. (ubclDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle [
               ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))])"
  sorry

lemma tsynbrec_insert: "tsynbRec\<cdot>sb = (ubDom\<cdot>sb = {\<guillemotright>dr}) \<leadsto> Abs_ubundle 
              [ar\<guillemotright> \<mapsto> bool2abp\<cdot>(tsynProjSnd\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr))), 
               o\<guillemotright> \<mapsto> nat2abp\<cdot>(tsynRec\<cdot>(abp2natbool\<cdot>(sb  .  \<guillemotright>dr)))]"
  sorry

lemma tsynbrec_ufwell [simp]: "ufWell tsynbRec"
  sorry

lemma recspf_insert: "RecSPF \<rightleftharpoons> sb = (Abs_ufun tsynbRec) \<rightleftharpoons> sb"
  sorry

lemma recspf_ufdom: "ufDom\<cdot>RecSPF = {\<guillemotright>dr}"
  sorry

lemma recspf_ufran: "ufRan\<cdot>RecSPF = {ar\<guillemotright>, o\<guillemotright>}"
  sorry

lemma recspf_ubdom: 
  assumes "ubDom\<cdot>sb = ufDom\<cdot>RecSPF"
  shows "ubDom\<cdot>(RecSPF \<rightleftharpoons> sb) = {ar\<guillemotright>, o\<guillemotright>}"
  by (simp add: assms recspf_ufran spf_ubDom)

lemma recspf_strict: "RecSPF \<rightleftharpoons> ubclLeast{\<guillemotright>dr} = ubclLeast{ar\<guillemotright>, o\<guillemotright>}"
  sorry

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