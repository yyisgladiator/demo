(*  Title:        Components.thy
    Author:       Dennis Slotboom, Annika Savelsberg
    E-Mail:       dennis.slotboom@rwth-aachen.de, annika.savelsberg@rwth-aachen.de

    Description:  Theory for ABP Component Lemmata on Time-synchronous Streams.
*)

chapter {* Theory for ABP Component Lemmata on Time-synchronous Streams *}

theory Components
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
  by (simp add: assms ubConc_usclConc_eq usclConc_stream_def msga_createbundle_ubgetch)

lemma msga_createbundle_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
  shows "sbRt\<cdot>(ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms)
  by (simp add: assms sbRt_def msga_createbundle_ubgetch msga_createbundle_ubconc)

lemma tsynbnull_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull \<guillemotright>dr)\<cdot>sb)) = [\<guillemotright>dr \<mapsto> null]"
  apply (rule convDiscrUp_eqI)
  apply (subst convdiscrup_inv_eq)
  apply (simp add: assms sbHdElem_def sbHdElem_cont domIff2)+
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
  apply (simp add: assms sbHdElem_def sbHdElem_cont domIff2)+
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
         autGetNextOutput_def autGetNextState_def getTransition_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* h_step lemma for state Rt and input null *)
lemma receiverautomaton_h_step_rt_null: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
  shows "h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (tsynbNull \<guillemotright>dr)\<cdot>sb) 
           = ubConc ((tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))\<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def)
  using assms receiverautomaton_h_step_ubdom_null_null by auto

(* h_step lemma for state Rf and input true *)
lemma receiverautomaton_h_step_rf_true:
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
    and "(snd a) = True"
  shows "h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) 
           = ubConc (createArOutput (snd a) \<uplus> (tsynbNull o\<guillemotright>))
               \<cdot>(h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def)
  using assms receiverautomaton_h_step_ubdom_ar_null by auto

(* h_step lemma for state Rt and input true *)
lemma receiverautomaton_h_step_rt_true: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
    and "(snd a) = True"
  shows "h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb)
           = ubConc (createArOutput (snd a) \<uplus> (createOOutput (fst a)))
               \<cdot>(h ReceiverAutomaton (State Rf) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

(* h_step lemma for state Rf and input false *)
lemma receiverautomaton_h_step_rf_false: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}" 
    and "(snd a) = False"
  shows "h ReceiverAutomaton (State Rf) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) 
           = ubConc (createArOutput (snd a) \<uplus> createOOutput (fst a))
               \<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def)
  using assms receiverautomaton_h_step_ubdom_ar_o by auto

(* h_step lemma for state Rt and input false *)
lemma receiverautomaton_h_step_rt_false: 
  assumes "ubDom\<cdot>sb = {\<guillemotright>dr}"
    and "(snd a) = False"
  shows "h ReceiverAutomaton (State Rt) \<rightleftharpoons> (ubConc (createBundle (Msg (A a)) \<guillemotright>dr)\<cdot>sb) 
           = ubConc (createArOutput (snd a) \<uplus> (tsynbNull o\<guillemotright>))
               \<cdot>(h ReceiverAutomaton (State Rt) \<rightleftharpoons> sb)"
  apply (simp_all add: h_final getDom_def ReceiverAutomaton.rep_eq h_out_dom assms getRan_def 
         autGetNextOutput_def autGetNextState_def getTransition_def)
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