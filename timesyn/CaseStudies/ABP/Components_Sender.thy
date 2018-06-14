(* merge into Components theory *)
theory Components_Sender
imports SenderAutomaton 

begin

lemma sendertransition_ubdom:
  assumes dom_f: "dom f = {\<guillemotright>i, \<guillemotright>as}" 
    and ubelemwell_f: "sbElemWell f"
  shows "ubDom\<cdot>(snd (senderTransition (s, f))) = {ds\<guillemotright>}"
  proof -
    obtain inp where f_def: "f = [\<guillemotright>i \<mapsto> inp]"
      using dom_eq_singleton_conv dom_f sorry
    obtain st buf where s_def: "s = State st buf"
      using SenderAutomaton.getSubState.cases by blast
    have "ubDom\<cdot>(snd (senderTransitionH (SenderState.State st buf, inp ) )) = {ds\<guillemotright>}" sorry
(*
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
  *)  then show "ubDom\<cdot>(snd (senderTransition (s, f))) =  {ds\<guillemotright>}"
      apply (simp add: f_def s_def as_def)
  qed


lemma sender_automaton_well:
  "automaton_well (senderTransition, SenderState.State Sf [], tsynbNull ds\<guillemotright>, {\<guillemotright>i,\<guillemotright>as }, {ds\<guillemotright>})"
  apply (rule automaton_wellI,simp)
sorry


end