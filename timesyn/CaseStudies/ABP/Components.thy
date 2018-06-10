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

lemma trans_rt_true: "receiverTransition (State Rt, [\<guillemotright>dr \<mapsto> (Msg (A (a,True)))]) = ((State Rf,(createArOutput True) \<uplus> (createOOutput a)))"
  by simp

lemma trans_rt_false: "receiverTransition (State Rt, [\<guillemotright>dr \<mapsto> (Msg (A (a,False)))]) = ((State Rt,(createArOutput False) \<uplus> (tsynbNull o\<guillemotright>)))"
  by simp

lemma trans_rf_true: "receiverTransition (State Rf, [\<guillemotright>dr \<mapsto> (Msg (A (a,True)))]) = ((State Rf,(createArOutput True) \<uplus> (tsynbNull o\<guillemotright>)))"
  by simp

lemma trans_rf_false: "receiverTransition (State Rf, [\<guillemotright>dr \<mapsto> (Msg (A (a,False)))]) = ((State Rt,(createArOutput False) \<uplus> (createOOutput a)))"
  by simp

lemma trans_null: "receiverTransition (State s, [\<guillemotright>dr \<mapsto> null]) =  (State s ,(tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>))"
  by (smt ReceiverSubstate.exhaust dom_empty dom_fun_upd fun_upd_same option.distinct(1) option.sel receiverTransition.simps receiverTransitionH.simps(2) receiverTransitionH.simps(4))

lemma unionub1: "ubDom\<cdot>((createArOutput a) \<uplus> (createOOutput b)) = {ar\<guillemotright>, o\<guillemotright>}"
  by (smt createArOutput.rep_eq createOOutput.rep_eq dom_empty dom_fun_upd insert_is_Un option.simps(3) ubclDom_ubundle_def ubclunion_dom ubdom_insert)

lemma unionub2: "ubDom\<cdot>((createArOutput a) \<uplus> (tsynbNull o\<guillemotright>)) = {ar\<guillemotright>, o\<guillemotright>}"
  by (smt createArOutput.rep_eq dom_empty dom_fun_upd insert_is_Un option.simps(3) tsynbnull_ubdom ubclDom_ubundle_def ubclunion_dom ubdom_insert)

lemma receiver_dom: "\<And> s f. dom f = {\<guillemotright>dr} \<and> ubElemWell f \<Longrightarrow> ubDom\<cdot>(snd (receiverTransition (s, f))) = {ar\<guillemotright>, o\<guillemotright>}"
  proof -
    fix s:: ReceiverState and f::"channel \<rightharpoonup> Receiver tsyn"
    assume a1: "dom f = {\<guillemotright>dr} \<and> ubElemWell f"
    obtain x where f_def: "f = [\<guillemotright>dr \<mapsto> x]"
      using a1 dom_eq_singleton_conv by force
    obtain ss where s_def: "s = State ss"
      using ReceiverAutomaton.getSubState.cases by blast
    show "ubDom\<cdot>(snd (receiverTransition (s, f))) =  {ar\<guillemotright>, o\<guillemotright>}"
      proof (cases x)
        case (Msg x1)
        hence "x1 \<in> ctype \<guillemotright>dr"
          apply (subst ctype_event_iff)
          by (metis a1 ctype_eventI ctype_tsyn_iff f_def fun_upd_same insertI1 option.sel ubElemWellI)   
        then obtain a where x1_def: "x1 = A a"
          by auto 
        then show ?thesis
          apply(simp add: s_def x1_def)
          by (metis (full_types) Msg ReceiverSubstate.exhaust \<open>\<And>thesis::bool. (\<And>a::nat \<times> bool. (x1::Receiver) = A a \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a1 f_def fun_upd_same option.sel receiverTransitionH.simps(1) receiverTransitionH.simps(3) snd_conv unionub1 unionub2)
      next
        case null
        then show ?thesis
          apply(simp add: s_def)
          by (smt ReceiverSubstate.exhaust a1 f_def fun_upd_same insert_is_Un option.sel receiverTransitionH.simps(2) receiverTransitionH.simps(4) snd_conv tsynbnull_ubdom ubclDom_ubundle_def ubclunion_dom) 
      qed
  qed

lemma receiver_automaton_well: 
  "automaton_well (receiverTransition, ReceiverState.State Rt, tsynbNull ar\<guillemotright> \<uplus> tsynbNull o\<guillemotright>, {\<guillemotright>dr}, {ar\<guillemotright>, o\<guillemotright>})"
  using receiver_dom by auto

lift_definition ReceiverAutomaton :: "(ReceiverState, Receiver tsyn) automaton" is "(receiverTransition, State Rt , (tsynbNull ar\<guillemotright>) \<uplus> (tsynbNull o\<guillemotright>), {c1}, {c2,c3})"
  using receiver_automaton_well by blast
  
  
end