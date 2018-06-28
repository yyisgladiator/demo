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

lemma sender_automaton_well:
  "automaton_well (senderTransition, SenderState.State Sf [], tsynbNull ds\<guillemotright>, {\<guillemotright>i,\<guillemotright>as }, {ds\<guillemotright>})"
  using sendertransition_ubdom by simp

end