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


(* ----------------------------------------------------------------------- *)
  section {* Automaton Sender Step Lemmata *}
(* ----------------------------------------------------------------------- *) 

lemma da_h_ubdom: assumes "ubDom\<cdot>sb = daDom automat" 
  shows "ubDom\<cdot>(da_h automat state \<rightleftharpoons> sb) = daRan automat"
  by (simp add: assms spf_ubDom)


lemma tsynbnulli_tsynbnullas_ubclunion_ubdom:
  "ubDom\<cdot>(tsynbNull (\<C> ''i'') \<uplus> tsynbNull (\<C> ''as'')) = {\<C> ''i'', \<C> ''as''}"
  by (metis insert_is_Un tsynbnull_ubdom ubclUnion_ubundle_def ubunionDom)

lemma ibundle_ubdom : 
  "ubDom\<cdot>(createIBundle a) = {\<C> ''i''}" 
  by (simp add:createIBundle.rep_eq ubdom_insert)

lemma tsynbnotnulli_tsynbnullas_ubclunion_ubdom:
  "ubDom\<cdot>(createIBundle a  \<uplus> tsynbNull (\<C> ''as'')) = {\<C> ''i'', \<C> ''as''}"
  by (metis ibundle_ubdom insert_is_Un tsynbnull_ubdom ubclUnion_ubundle_def ubunionDom)


lemma asbundle_ubdom : 
  "ubDom\<cdot>(createAsBundle b) = {\<C> ''as''}" 
  by (simp add:createAsBundle.rep_eq ubdom_insert)


lemma tsynbnulli_tsynbnotnullas_ubclunion_ubdom:
  "ubDom\<cdot>(tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b) = {\<C> ''i'', \<C> ''as''}"
  by (metis asbundle_ubdom insert_is_Un tsynbnull_ubdom ubclUnion_ubundle_def ubunionDom)



lemma tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom:
  "ubDom\<cdot>(createIBundle a  \<uplus> createAsBundle b) = {\<C> ''i'', \<C> ''as''}"
  by (metis asbundle_ubdom ibundle_ubdom insert_is_Un ubclUnion_ubundle_def ubunionDom)


lemma senderautomaton_h_step_ubdom_out_null:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "ubDom\<cdot>(ubConc (tsynbNull (\<C> ''ds''))
                  \<cdot>(da_h SenderAutomaton (SenderState.State s buffer) \<rightleftharpoons> sb)) = {\<C> ''ds''}"
  apply (simp add: tsynbnulli_tsynbnullas_ubclunion_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def SenderAutomaton.rep_eq insert_commute)+


lemma senderautomaton_h_step_ubdom_out_not_null:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "ubDom\<cdot>(ubConc (createDsBundle (a, b))
                  \<cdot>(da_h SenderAutomaton (SenderState.State s buffer) \<rightleftharpoons> sb)) = {\<C> ''ds''}"
  apply (simp add: createdsoutput_ubdom)
  apply (subst da_h_ubdom)
  by (simp add: assms daDom_def daRan_def SenderAutomaton.rep_eq insert_commute)+
  

lemma msga_ctype: "Msg (Pair_nat_bool a) \<in> ctype (\<C> ''ds'')"
  by (simp add: ctype_tsynI) 


lemma tsynb_null_null_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb))
          = [\<C> ''i'' \<mapsto> null, \<C> ''as'' \<mapsto> null]"
  sorry 


lemma tsynb_i_null_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb))
          = [\<C> ''i'' \<mapsto> Msg (Nat a), \<C> ''as'' \<mapsto> null]"
  sorry

lemma tsynb_null_as_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b)\<cdot>sb))
          = [\<C> ''i'' \<mapsto> null, \<C> ''as'' \<mapsto> Msg (Bool b)]"
  sorry


lemma tsynb_i_as_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createIBundle a  \<uplus> createAsBundle b)\<cdot>sb))
          = [\<C> ''i'' \<mapsto> Msg (Nat a), \<C> ''as'' \<mapsto> Msg (Bool b)]"
  sorry


lemma tsynb_null_null_ubgetch_i[simp]:
  "tsynbNull (\<C> ''i'') \<uplus> tsynbNull (\<C> ''as'')  .  \<C> ''i'' = \<up>null"
  by (simp add: ubclUnion_ubundle_def)

lemma tsynb_null_null_ubgetch_as[simp]:
  "tsynbNull (\<C> ''i'') \<uplus> tsynbNull (\<C> ''as'')  .  \<C> ''as'' = \<up>null"
  by (simp add: ubclUnion_ubundle_def)


lemma rep_ubundle_i_null: "Rep_ubundle (createIBundle a \<uplus> tsynbNull (\<C> ''as'')) 
               = [\<C> ''i'' \<mapsto> \<up>(Msg (Nat a)), \<C> ''as'' \<mapsto> \<up>(null)]"
  sorry


lemma tsynb_i_null_ubgetch_i [simp]:
  "createIBundle a  \<uplus> tsynbNull (\<C> ''as'')  .  \<C> ''i'' = \<up>(Msg(Nat a))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by(simp add: rep_ubundle_i_null)

lemma tsynb_i_null_ubgetch_as[simp]:
  "createIBundle a  \<uplus> tsynbNull (\<C> ''as'')  .  \<C> ''as'' = \<up>null"
  by (simp add: ubclUnion_ubundle_def)


lemma rep_ubundle_null_as: "Rep_ubundle (tsynbNull (\<C> ''i'') \<uplus> createAsBundle b) 
               = [\<C> ''i'' \<mapsto> \<up>null, \<C> ''as'' \<mapsto> \<up>(Msg(Bool b))]"
  sorry
  

lemma tsynb_null_as_ubgetch_i[simp]:
  "tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b  .  \<C> ''i'' = \<up>null"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by(simp add: rep_ubundle_null_as)

lemma tsynb_null_as_ubgetch_as[simp]:
  "tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b  .  \<C> ''as'' = \<up>(Msg (Bool b))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by(simp add: rep_ubundle_null_as)


lemma rep_ubundle_i_as: "Rep_ubundle (createIBundle a \<uplus> createAsBundle b) 
               = [\<C> ''i'' \<mapsto> \<up>(Msg(Nat a)), \<C> ''as'' \<mapsto> \<up>(Msg(Bool b))]"
  sorry

lemma tsynb_i_as_ubgetch_as[simp]:
  "createIBundle a  \<uplus> createAsBundle b  .  \<C> ''as'' = \<up>(Msg (Bool b))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by(simp add: rep_ubundle_i_as)

lemma tsynb_i_as_ubgetch_i[simp]:
  "createIBundle a  \<uplus> createAsBundle b  .  \<C> ''i'' = \<up>(Msg (Nat a))"
  apply (simp add: ubgetch_insert createBundle.rep_eq)
  by(simp add: rep_ubundle_i_as)




lemma sbrt_ubconc_null_null [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (tsynbNull (\<C> ''i'') \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb) = sb"
  sorry

lemma sbrt_ubconc_i_null [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb) = sb"
  sorry

lemma sbrt_ubconc_null_as [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b )\<cdot>sb) = sb"
  sorry

lemma sbrt_ubconc_i_as [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (createIBundle a  \<uplus> createAsBundle b )\<cdot>sb) = sb"
  sorry


(* h_step lemma for -- state:Sf   input:(null, null)   buffer:empty *)
lemma senderautomaton_h_step_sf_null_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf [])  
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State Sf []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_null by auto




(* h_step lemma for -- state:Sf   input:(null, null)   buffer:non-empty *)
lemma senderautomaton_h_step_sf_null_null_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (State Sf buffer)  
         \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
       = ubConc ((createDsBundle (Pair (last buffer) False )))
                 \<cdot>(da_h SenderAutomaton (State Sf buffer) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto



(* h_step lemma for -- state:St   input:(null, null)   buffer:empty *)
lemma senderautomaton_h_step_st_null_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St []) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State St []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_null by auto


(* h_step lemma for -- state:St   input:(null, null)   buffer:non-empty *)
lemma senderautomaton_h_step_st_null_null_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (State St buffer) 
         \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc ((createDsBundle (Pair (last buffer) True )))
                    \<cdot>(da_h SenderAutomaton (State St buffer) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:St   input:(Nat a, null)   buffer:empty *)
lemma senderautomaton_h_step_st_i_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St []) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (State St [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(Nat a, null)   buffer:non-empty *)
lemma senderautomaton_h_step_st_i_null_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (State St buffer) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (createDsBundle (last buffer, True))
                   \<cdot>(da_h SenderAutomaton (State St (prepend buffer a)) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:Sf   input:(Nat a, null)   buffer:empty *)
lemma senderautomaton_h_step_sf_i_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf []) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (State Sf [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(Nat a, null)   buffer:non-empty *)
lemma senderautomaton_h_step_sf_i_null_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (State Sf buffer)
          \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
        = ubConc (createDsBundle (last buffer, False))
                  \<cdot>(da_h SenderAutomaton (State Sf (prepend buffer a)) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:St   input:(null, True)   buffer:empty *)
lemma senderautomaton_h_step_st_null_true_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St [])
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State St []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(null, True)   buffer:one element *)
lemma senderautomaton_h_step_st_null_true_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St [a])
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
          = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State Sf []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(null, True)   buffer:more than one element *)
lemma senderautomaton_h_step_st_null_true_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (State St buffer)
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), False))
                    \<cdot>(da_h SenderAutomaton (State Sf (butlast buffer )) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(null, False)   buffer:empty *)
lemma senderautomaton_h_step_st_null_false_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St [])
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State St []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:St   input:(null, False)   buffer:non-empty *)
lemma senderautomaton_h_step_st_null_false_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer \<noteq> 0"
  shows "da_h SenderAutomaton (State St buffer) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last buffer, True))
                    \<cdot>(da_h SenderAutomaton (State St buffer) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(null, True)   buffer:empty *)
lemma senderautomaton_h_step_sf_null_false_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf []) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State Sf []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(null, False)   buffer:one element *)
lemma senderautomaton_h_step_sf_null_false_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf [a])
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State St []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:Sf   input:(null, False)   buffer:more than one element *)
lemma senderautomaton_h_step_sf_null_false_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (State Sf buffer) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), True))
                    \<cdot>(da_h SenderAutomaton (State St (butlast buffer )) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:Sf   input:(null, True)   buffer:empty *)
lemma senderautomaton_h_step_sf_null_true_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf [])
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State Sf []) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto



(* h_step lemma for -- state:Sf   input:(null, True)   buffer:non-empty *)
lemma senderautomaton_h_step_sf_null_true_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer \<noteq> 0"
  shows "da_h SenderAutomaton (State Sf buffer) 
          \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
       = ubConc (createDsBundle (last buffer, False))\<cdot>(da_h SenderAutomaton (State Sf buffer) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto



(* h_step lemma for -- state:St   input:(a, True)   buffer:empty *)
lemma senderautomaton_h_step_st_i_true_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St [])  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (State St [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(a, True)   buffer:one element *)
lemma senderautomaton_h_step_st_i_true_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St [b])  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (State Sf [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(a, True)   buffer:more than one element *)
lemma senderautomaton_h_step_st_i_true_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (State St buffer) 
            \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), False))
                     \<cdot>(da_h SenderAutomaton (State Sf (prepend (butlast buffer ) a)) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(a, False)   buffer:empty *)
lemma senderautomaton_h_step_st_i_false_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State St [])  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (State St [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto

(* h_step lemma for -- state:St   input:(a, False)   buffer:non-empty *)
lemma senderautomaton_h_step_st_i_false_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer \<noteq> 0"
  shows "da_h SenderAutomaton (State St buffer) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last buffer, True))
                  \<cdot>(da_h SenderAutomaton (State St (prepend buffer a)) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto




(* h_step lemma for -- state:Sf   input:(a, False)   buffer:empty *)
lemma senderautomaton_h_step_sf_i_false_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf [])  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
       = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (State Sf [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(a, False)   buffer:one element *)
lemma senderautomaton_h_step_sf_i_false_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf [b])  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
       = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (State St [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(a, False)   buffer:more than one element *)
lemma senderautomaton_h_step_sf_i_false_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (State Sf buffer)  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
       = ubConc (createDsBundle (last (butlast buffer), True))
         \<cdot>(da_h SenderAutomaton (State St (prepend (butlast buffer ) a)) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(a, True)   buffer:empty *)
lemma senderautomaton_h_step_sf_i_true_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (State Sf [])  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
       = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (State Sf [a]) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* h_step lemma for -- state:Sf   input:(a, True)   buffer:non-empty *)
lemma senderautomaton_h_step_sf_i_true_non_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer \<noteq> 0"
  shows "da_h SenderAutomaton (State Sf buffer)  \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
       = ubConc (createDsBundle (last buffer, False))\<cdot>(da_h SenderAutomaton (State Sf (prepend buffer a)) \<rightleftharpoons> sb)"
  apply (simp_all add: da_h_final daDom_def SenderAutomaton.rep_eq da_h_ubdom assms daRan_def 
         daNextOutput_def daNextState_def daTransition_def usclConc_stream_def
         tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)
  using assms senderautomaton_h_step_ubdom_out_not_null by auto


(* H_step lemma *)
lemma senderautomaton_H_step:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_H SenderAutomaton \<rightleftharpoons> sb 
           = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (State St []) \<rightleftharpoons> sb)"
  by (simp add: da_H_def da_h_ubdom daRan_def daInitialState_def daInitialOutput_def 
         SenderAutomaton.rep_eq daDom_def assms)
  

end