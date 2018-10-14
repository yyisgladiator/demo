(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Theory for Automaton Sender Lemmata.
*)

chapter {* Theory for Sender Automaton Lemmata *}

theory Sender
imports SenderAutomaton Components

begin
declare One_nat_def[simp del]
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

lemma sendertransition_ubdom:
  assumes dom_f: "dom f = {\<C> ''i'', \<C> ''as''}" and ubelemwell_f: "sbElemWell f"
  shows "ubDom\<cdot>(snd (senderTransition (s, f))) = {\<C> ''ds''}"
  oops

lemma sendertransition_automaton_well:
  "daWell (senderTransition, SenderState Sf [] 0, tsynbNull (\<C> ''ds''), {\<C> ''i'', \<C> ''as''}, 
          {\<C> ''ds''})"
  by simp

(* ----------------------------------------------------------------------- *)
  section {* Automaton Sender SPF Lemmata *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lemma dadom_senderautomaton:"daDom SenderAutomaton = {\<C> ''i'', \<C> ''as''}"
  by(simp add: daDom_def SenderAutomaton.rep_eq insert_commute)

lemma daran_senderautomaton:"daRan SenderAutomaton = {\<C> ''ds''}"
  by (simp add: daRan_def SenderAutomaton.rep_eq)
    
lemma dainitialoutput_senderautomaton:
  "daInitialOutput SenderAutomaton = tsynbNull (\<C> ''ds'')"
  by(simp add: daInitialOutput_def SenderAutomaton.rep_eq)

lemma senderspf_ufdom: "ufDom\<cdot>SenderSPF = {\<C> ''i'', \<C> ''as''}"
  by (simp add: SenderSPF_def da_H_def SenderAutomaton.rep_eq daDom_def insert_commute)

lemma senderspf_ufran: "ufRan\<cdot>SenderSPF = {\<C> ''ds''}"
  by (simp add: SenderSPF_def da_H_def SenderAutomaton.rep_eq daRan_def)

lemma senderspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>SenderSPF"
  shows "ubDom\<cdot>(SenderSPF \<rightleftharpoons> sb) = {\<C> ''ds''}"
  by (simp add: assms senderspf_ufran spf_ubDom)
  
lemma senderspf_strict: "SenderSPF \<rightleftharpoons> ubclLeast{\<C> ''i'', \<C> ''as''} = tsynbNull (\<C> ''ds'')"
  apply (simp add: SenderSPF_def)
  apply (subst da_H_bottom)
  apply (simp_all add: dadom_senderautomaton dainitialoutput_senderautomaton daran_senderautomaton)
  by blast
                                                             
(* ----------------------------------------------------------------------- *)
  section {* Automaton Sender Step Lemmata *}
(* ----------------------------------------------------------------------- *) 

lemma da_h_ubdom: assumes "ubDom\<cdot>sb = daDom automat" 
  shows "ubDom\<cdot>(da_h automat state \<rightleftharpoons> sb) = daRan automat"
  by (simp add: assms spf_ubDom)

lemma tsynbnulli_tsynbnullas_ubclunion_ubdom:
  "ubDom\<cdot>(tsynbNull (\<C> ''i'') \<uplus> tsynbNull (\<C> ''as'')) = {\<C> ''i'', \<C> ''as''}"
  by(simp add: ubclUnion_ubundle_def insert_commute)

lemma tsynbnotnulli_tsynbnullas_ubclunion_ubdom:
  "ubDom\<cdot>(createIBundle a  \<uplus> tsynbNull (\<C> ''as'')) = {\<C> ''i'', \<C> ''as''}"
  by(simp add: ubclUnion_ubundle_def insert_commute)

lemma tsynbnulli_tsynbnotnullas_ubclunion_ubdom:
  "ubDom\<cdot>(tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b) = {\<C> ''i'', \<C> ''as''}"
  by(simp add: ubclUnion_ubundle_def insert_commute)

lemma tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom:
  "ubDom\<cdot>(createIBundle a  \<uplus> createAsBundle b) = {\<C> ''i'', \<C> ''as''}"
  by(simp add: ubclUnion_ubundle_def insert_commute)

lemma senderautomaton_da_h_ubdom:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "ubDom\<cdot>(da_h SenderAutomaton (SenderState.SenderState s buffer c) \<rightleftharpoons> sb) = {\<C> ''ds''}"
  by (simp add: da_h_ubdom assms daDom_def daRan_def SenderAutomaton.rep_eq insert_commute)

lemma tsynb_null_null_eq:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb))
          = [\<C> ''i'' \<mapsto> null, \<C> ''as'' \<mapsto> null]"
  apply(simp add: sbHdElem_def sbHdElem_cont)
  apply (rule convDiscrUp_eqI)                   
  apply(simp add: domIff2 ubclUnion_ubundle_def assms dom_def usclConc_stream_def)
  apply (subst fun_eq_iff,rule)
  apply(case_tac "x = \<C> ''i'' \<or> x = \<C> ''as''")
  apply(simp add: assms ubclUnion_ubundle_def usclConc_stream_def convDiscrUp_def)
  apply (simp add: up_def disj_commute)
  by (simp add: convDiscrUp_def tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)

lemma tsynb_i_null_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb))
          = [\<C> ''i'' \<mapsto> Msg (ABPNat a), \<C> ''as'' \<mapsto> null]"   
  apply(simp add: sbHdElem_def sbHdElem_cont)
  apply (rule convDiscrUp_eqI)                   
  apply(simp add: domIff2 ubclUnion_ubundle_def assms dom_def usclConc_stream_def)
  apply (subst fun_eq_iff,rule)
  apply(case_tac "x = \<C> ''i'' \<or> x = \<C> ''as''")
  apply(simp add: assms ubclUnion_ubundle_def usclConc_stream_def convDiscrUp_def)
  apply (simp add: up_def disj_commute)
  by (simp add: convDiscrUp_def tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)

lemma tsynb_null_as_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b)\<cdot>sb))
          = [\<C> ''i'' \<mapsto> null, \<C> ''as'' \<mapsto> Msg (ABPBool b)]"
  apply(simp add: sbHdElem_def sbHdElem_cont)
  apply (rule convDiscrUp_eqI)                   
  apply(simp add: domIff2 ubclUnion_ubundle_def assms dom_def usclConc_stream_def)
  apply (subst fun_eq_iff,rule)
  apply(case_tac "x = \<C> ''i'' \<or> x = \<C> ''as''")
  apply(simp add: assms ubclUnion_ubundle_def usclConc_stream_def convDiscrUp_def)
  apply (simp add: up_def disj_commute)
  by (simp add: convDiscrUp_def tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)

lemma tsynb_i_as_eq [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "inv convDiscrUp (sbHdElem\<cdot>(ubConc (createIBundle a  \<uplus> createAsBundle b)\<cdot>sb))
          = [\<C> ''i'' \<mapsto> Msg (ABPNat a), \<C> ''as'' \<mapsto> Msg (ABPBool b)]"
  apply(simp add: sbHdElem_def sbHdElem_cont)
  apply (rule convDiscrUp_eqI)                   
  apply(simp add: domIff2 ubclUnion_ubundle_def assms dom_def usclConc_stream_def)
  apply (subst fun_eq_iff,rule)
  apply(case_tac "x = \<C> ''i'' \<or> x = \<C> ''as''")
  apply(simp add: assms ubclUnion_ubundle_def usclConc_stream_def convDiscrUp_def)
  apply (simp add: up_def disj_commute)
  by (simp add: convDiscrUp_def tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom)

lemma tsynb_nulli_ubgetch_i[simp]:
  assumes "\<C> ''i'' \<notin> ubDom\<cdot>sb"
  shows "tsynbNull (\<C> ''i'') \<uplus> sb  .  \<C> ''i'' = \<up>null"
  by (simp add: assms ubclUnion_ubundle_def)

lemma tsynb_nullas_ubgetch_as[simp]:
  "sb \<uplus> tsynbNull (\<C> ''as'')  .  \<C> ''as'' = \<up>null"
  by (simp add: ubclUnion_ubundle_def)

lemma tsynb_notnulli_ubgetch_i[simp]:
  assumes " \<C> ''i'' \<notin> ubDom\<cdot>sb" 
  shows "createIBundle a  \<uplus> sb  .  \<C> ''i'' = \<up>(Msg(ABPNat a))"
  by(simp add: assms ubclUnion_ubundle_def )

lemma tsynb_notnullas_ubgetch_as[simp]:
  "sb  \<uplus> createAsBundle b  .  \<C> ''as'' = \<up>(Msg (ABPBool b))"
  by (simp add: ubclUnion_ubundle_def)

lemma sbrt_ubconc_null_null [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (tsynbNull (\<C> ''i'') \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms tsynbnulli_tsynbnullas_ubclunion_ubdom usclConc_stream_def)+
  by auto

lemma sbrt_ubconc_i_null [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms tsynbnotnulli_tsynbnullas_ubclunion_ubdom usclConc_stream_def)+
  by auto

lemma sbrt_ubconc_null_as [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b )\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms tsynbnulli_tsynbnotnullas_ubclunion_ubdom usclConc_stream_def)+
  by auto

lemma sbrt_ubconc_i_as [simp]:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows  "sbRt\<cdot>(ubConc (createIBundle a  \<uplus> createAsBundle b )\<cdot>sb) = sb"
  apply (rule ub_eq)
  apply (simp add: assms tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom usclConc_stream_def)+
  by auto

lemma size_greater_one_not_empty: 
  assumes "size buffer > 1" 
  shows "buffer \<noteq> []"
  using assms by auto 

(* h_step lemma for -- state:Sf   input:(null, null)   buffer:empty  counter does not change*)
lemma senderautomaton_h_step_sf_null_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState Sf [] c)  
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf [] c) \<rightleftharpoons> sb)"
   by(simp add: assms da_h_final tsynbnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+

(* h_step lemma for -- state:Sf   input:(null, null)   buffer:non-empty  c = 0 *)
lemma senderautomaton_h_step_sf_null_null_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState Sf buffer 0)  
         \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
       = ubConc (createDsBundle (Pair (last buffer) False))
                \<cdot>(da_h SenderAutomaton (SenderState Sf buffer 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(null, null)   buffer:non-empty  c \<noteq> 0 *)
lemma senderautomaton_h_step_sf_null_null_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState Sf buffer c)  
         \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
       = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf buffer (c-1)) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, null)   buffer:empty  c does not change *)
lemma senderautomaton_h_step_st_null_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState St [] c) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St [] c) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, null)   buffer:non-empty  c = 0 *)
lemma senderautomaton_h_step_st_null_null_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState St buffer 0) 
         \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc ((createDsBundle (Pair (last buffer) True )))
                    \<cdot>(da_h SenderAutomaton (SenderState St buffer 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, null)   buffer:non-empty  c \<noteq> 0 *)
lemma senderautomaton_h_step_st_null_null_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState St buffer c) 
         \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St buffer (c-1)) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(Nat a, null)   buffer:empty  c is set to 3 *)
lemma senderautomaton_h_step_st_i_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState St [] c) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (SenderState St [a] 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnotnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(Nat a, null)   buffer:non-empty  c = 0 *)
lemma senderautomaton_h_step_st_i_null_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState St buffer 0) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (createDsBundle (last buffer, True))
                   \<cdot>(da_h SenderAutomaton (SenderState St (prepend buffer a) 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnotnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(Nat a, null)   buffer:non-empty c \<noteq> 0 *)
lemma senderautomaton_h_step_st_i_null_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq>  0"
  shows "da_h SenderAutomaton (SenderState St buffer c) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))
           \<cdot>(da_h SenderAutomaton (SenderState St (prepend buffer a) (c-1)) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnotnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(Nat a, null)   buffer:empty c is set to 3 *)
lemma senderautomaton_h_step_sf_i_null_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState Sf [] c) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
         = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (SenderState Sf [a] 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnotnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(Nat a, null)   buffer:non-empty  c = 0 *)
lemma senderautomaton_h_step_sf_i_null_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState Sf buffer 0)
          \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
        = ubConc (createDsBundle (last buffer, False))
                  \<cdot>(da_h SenderAutomaton (SenderState Sf (prepend buffer a) 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnotnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(Nat a, null)   buffer:non-empty c \<noteq> 0 *)
lemma senderautomaton_h_step_sf_i_null_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState Sf buffer c)
          \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> tsynbNull (\<C> ''as''))\<cdot>sb)
        = ubConc (tsynbNull (\<C> ''ds''))
                  \<cdot>(da_h SenderAutomaton (SenderState Sf (prepend buffer a) (c-1)) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnotnulli_tsynbnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, b)   buffer:empty  c does not change *)
lemma senderautomaton_h_step_st_null_notnull_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState St [] c)
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St [] c) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, True)   buffer:one element  c does not change *)
lemma senderautomaton_h_step_st_null_true_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState St [a] c)
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
          = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf [] c) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, True)   buffer:more than one element  c is set to 3 *)
lemma senderautomaton_h_step_st_null_true_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "  (1::nat) < size buffer"
  shows "da_h SenderAutomaton (SenderState St buffer c)
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), False))
                    \<cdot>(da_h SenderAutomaton (SenderState Sf (butlast buffer) 3) \<rightleftharpoons> sb)"
    by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton
                 usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
                 daTransition_def SenderAutomaton.rep_eq  da_h_ubdom   daran_senderautomaton 
                 size_greater_one_not_empty)+


(* h_step lemma for -- state:St   input:(null, False)   buffer:non-empty  c = 0 *)
lemma senderautomaton_h_step_st_null_false_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState St buffer 0) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last buffer, True))
                    \<cdot>(da_h SenderAutomaton (SenderState St buffer 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(null, False)   buffer:non-empty  c \<noteq> 0 *)
lemma senderautomaton_h_step_st_null_false_non_empty_not_zero :
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState St buffer c) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))
                    \<cdot>(da_h SenderAutomaton (SenderState St buffer (c-1)) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(null, b)   buffer:empty  c does not change *)
lemma senderautomaton_h_step_sf_null_notnull_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState Sf [] c) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle b)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf [] c) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(null, False)   buffer:one element c does not change *)
lemma senderautomaton_h_step_sf_null_false_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState Sf [a] c)
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St [] c) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(null, False)   buffer:more than one element  c is set to 3*)
lemma senderautomaton_h_step_sf_null_false_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (SenderState Sf buffer c) 
           \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), True))
                    \<cdot>(da_h SenderAutomaton (SenderState St (butlast buffer) 3) \<rightleftharpoons> sb)"
    by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton
                 usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
                 daTransition_def SenderAutomaton.rep_eq  da_h_ubdom   daran_senderautomaton 
                 size_greater_one_not_empty)+


(* h_step lemma for -- state:Sf   input:(null, True)   buffer:non-empty  c = 0*)
lemma senderautomaton_h_step_sf_null_true_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState Sf buffer 0) 
          \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
          = ubConc (createDsBundle (last buffer, False))
                    \<cdot>(da_h SenderAutomaton (SenderState Sf buffer 3) \<rightleftharpoons> sb)"
  by(simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+

(* h_step lemma for -- state:Sf   input:(null, True)   buffer:non-empty  c \<noteq> 0*)
lemma senderautomaton_h_step_sf_null_true_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState Sf buffer c ) 
          \<rightleftharpoons> (ubConc (tsynbNull (\<C> ''i'')  \<uplus> createAsBundle True)\<cdot>sb)
       = ubConc (tsynbNull (\<C> ''ds''))
                \<cdot>(da_h SenderAutomaton (SenderState Sf buffer (c-1)) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+

(* h_step lemma for -- state:St   input:(a, b)   buffer:empty  c is set to 3*)
lemma senderautomaton_h_step_st_i_notnull_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState St [] c)  
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle b)\<cdot>sb)
         = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (SenderState St [a] 3) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(a, True)   buffer:one element c is set to 3 *)
lemma senderautomaton_h_step_st_i_true_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState St [b] c) 
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (SenderState Sf [a] 3) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(a, True)   buffer:more than one element  c is set to 3*)
lemma senderautomaton_h_step_st_i_true_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (SenderState St buffer c) 
            \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), False))
                     \<cdot>(da_h SenderAutomaton (SenderState Sf (prepend (butlast buffer ) a) 3) \<rightleftharpoons> sb)"
    by(simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton
                 usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
                 daTransition_def SenderAutomaton.rep_eq  da_h_ubdom   daran_senderautomaton 
                 size_greater_one_not_empty)+


(* h_step lemma for -- state:St   input:(a, False)   buffer:non-empty  c = 0 *)
lemma senderautomaton_h_step_st_i_false_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState St buffer 0) 
           \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last buffer, True))
                  \<cdot>(da_h SenderAutomaton (SenderState St (prepend buffer a) 3) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:St   input:(a, False)   buffer:non-empty  c \<noteq> 0 *)
lemma senderautomaton_h_step_st_i_false_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState St buffer c)
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))
                 \<cdot>(da_h SenderAutomaton (SenderState St (prepend buffer a) (c-1)) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(a, b)   buffer:empty  c is set to 3 *)
lemma senderautomaton_h_step_sf_i_notnull_empty:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState Sf [] c)  
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle b)\<cdot>sb)
        = ubConc (createDsBundle (a, False))\<cdot>(da_h SenderAutomaton (SenderState Sf [a] 3) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(a, False)   buffer:one element c is set to 3 *)
lemma senderautomaton_h_step_sf_i_false_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_h SenderAutomaton (SenderState Sf [b] c) 
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (a, True))\<cdot>(da_h SenderAutomaton (SenderState St [a] 3) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(a, False)   buffer:more than one element  c is set to 3*)
lemma senderautomaton_h_step_sf_i_false_more_than_one_element:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "size buffer > 1"
  shows "da_h SenderAutomaton (SenderState Sf buffer c)  \<rightleftharpoons> 
         (ubConc (createIBundle a  \<uplus> createAsBundle False)\<cdot>sb)
         = ubConc (createDsBundle (last (butlast buffer), True))
         \<cdot>(da_h SenderAutomaton (SenderState St (prepend (butlast buffer) a) 3) \<rightleftharpoons> sb)"
    by(simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton
                 usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
                 daTransition_def SenderAutomaton.rep_eq  da_h_ubdom   daran_senderautomaton 
                 size_greater_one_not_empty)+


(* h_step lemma for -- state:Sf   input:(a, True)   buffer:non-empty c = 0 *)
lemma senderautomaton_h_step_sf_i_true_non_empty_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  shows "da_h SenderAutomaton (SenderState Sf buffer 0)  
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (createDsBundle (last buffer, False))
                 \<cdot>(da_h SenderAutomaton (SenderState Sf (prepend buffer a) 3) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* h_step lemma for -- state:Sf   input:(a, True)   buffer:non-empty c \<noteq> 0 *)
lemma senderautomaton_h_step_sf_i_true_non_empty_not_zero:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  and "buffer \<noteq> []"
  and "c \<noteq> 0"
  shows "da_h SenderAutomaton (SenderState Sf buffer c)  
         \<rightleftharpoons> (ubConc (createIBundle a  \<uplus> createAsBundle True)\<cdot>sb)
         = ubConc (tsynbNull (\<C> ''ds''))
                 \<cdot>(da_h SenderAutomaton (SenderState Sf (prepend buffer a) (c-1)) \<rightleftharpoons> sb)"
  by (simp add: assms da_h_final tsynbnotnulli_tsynbnotnullas_ubclunion_ubdom dadom_senderautomaton 
               usclConc_stream_def tsynb_null_null_eq daNextOutput_def daNextState_def 
               daTransition_def SenderAutomaton.rep_eq da_h_ubdom daran_senderautomaton)+


(* H_step lemma *)
lemma senderautomaton_H_step:
  assumes "ubDom\<cdot>sb = {\<C> ''i'', \<C> ''as''}"
  shows "da_H SenderAutomaton \<rightleftharpoons> sb 
           = ubConc (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St [] 0) \<rightleftharpoons> sb)"
  by(simp add: assms da_H_def daInitialState_def daInitialOutput_def SenderAutomaton.rep_eq  
               da_h_ubdom dadom_senderautomaton daran_senderautomaton)

end