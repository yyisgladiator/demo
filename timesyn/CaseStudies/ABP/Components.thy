(*  Title:        Components.thy
    Author:       Dennis Slotboom, Annika Savelsberg
    E-Mail:       dennis.slotboom@rwth-aachen.de, annika.savelsberg@rwth-aachen.de

    Description:  ABP Components on time-synchronous streams.
*)

chapter {* ABP Components on Time-synchronous Streams *}

theory Components
imports "../../tsynStream"  ReceiverAutomaton

begin

(* ToDo: not cont.
fun tsynRecProj :: "('a \<times> bool) tsyn discr \<rightarrow> 'a tsyn discr" where
  "tsynRecProj (Discr (Msg (m, b))) = Discr (Msg m)" |
  "tsynRecProj (Discr null) = Discr null"

fixrec tsynRec_h :: "('a \<times> bool) tsyn stream \<rightarrow> bool \<rightarrow> 'a tsyn stream" where
  "tsynRec_h\<cdot>\<epsilon>\<cdot>bit = \<epsilon>" |
  "tsynRec_h\<cdot>(up\<cdot>a && as)\<cdot>bit = (
     if (undiscr a) = null then (up\<cdot>(Discr null)) && tsynRec_h\<cdot>as\<cdot>bit
     else (
       if bit = snd (invMsg (undiscr a)) then up\<cdot>(tsynRecProj a) &&  tsynRec_h\<cdot>as\<cdot>True
       else tsynRec_h\<cdot>as\<cdot>True
     )
  )"
*)

(*
rec :: bool \<rightarrow> ('a \<times> bool) tsyn stream \<rightarrow> (bool tsyn stream \<times> 'a tsyn stream)
rec b \<epsilon> = (\<epsilon>, \<epsilon>)
rec b (- \<bullet> dats) = (- \<bullet> bits, - \<bullet> msgs) where (bits, msgs) = rec(b, dats)
rec b ((m, b) \<bullet> dats) = (b \<bullet> bits, m \<bullet> msgs) where (bits, msgs) = rec(\<not>b, dats)
rec b ((m, \<not>b) \<bullet> dats) = (\<not>b \<bullet> bits, - \<bullet> msgs) where (bits, msgs) = rec(b, dats)
*)

fun rec_h :: "bool \<Rightarrow> ('a \<times> bool) tsyn \<Rightarrow> ('a tsyn \<times> bool)" where
  "rec_h b (Msg (msg,b1)) = (if b1 = b then (Msg msg, \<not>b) else (null, b))" |
  "rec_h b null = (null, b) " 

definition receiver :: "('a \<times> bool) tsyn stream \<rightarrow> 'a tsyn stream" where
  "receiver \<equiv> \<Lambda> s. sscanlA rec_h True\<cdot>s"

lemma receiver_insert: "receiver\<cdot>s = sscanlA rec_h True\<cdot>s"
  by (simp add: receiver_def)

lemma receiver_test_finstream:
  "receiver\<cdot>(<[Msg(1, False), null, Msg(2, True),Msg(1, False)]>) = <[null, null,Msg 2, Msg 1]>"
  by (simp add: receiver_insert)

lemma receiver_test_infstream: 
  "receiver\<cdot>((<[Msg(1, False), null, Msg(2, True),Msg(1, False)]>)\<infinity>) 
     = (<[null, null, Msg 2, Msg 1]>)\<infinity>"
  apply (simp add: receiver_insert)
  oops

(* The ReceiverAutomaton is well formed *)

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
    and ubelemwell_f: "ubElemWell f"
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
          by (simp add: dom_f f_def ubElemWell_def ctype_tsyn_def image_def)
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
  
end