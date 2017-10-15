(*
    Description:  This is a specification of the "Alternating Bit Protocol" on timed streams. 
*)

theory ABP3
imports TSPSTheorie

begin
  default_sort message



(* ----------------------------------------------------------------------- *)
  section \<open>Definition of bsASic datatypes \<close>
(* ----------------------------------------------------------------------- *)


datatype data = \<D> nat
  (* neesDS to be instanciated to countables in order to use with streams *)
  instance data::countable
  apply(intro_classes)
  by(countable_datatype)


datatype M = D data | B bool | DB data bool
  (* DB is used to hide (data\<times>bool) type *)

  instance M::countable
  apply(intro_classes)
  by(countable_datatype)


(* StansDS for : DataBitPair *)
definition DBP :: "(data \<times> bool) \<Rightarrow> M" where
"DBP \<equiv>  \<lambda>(d,b). DB d b"


instantiation M::message
begin

  (* defines which elements sARe allowed on the channels *)
    (* overwrites the "ctype" definition in Channel.thy ! *)
  fun ctype_M :: "channel \<Rightarrow> M set" where
  "ctype_M abpIn = range D"    | (* external \<rightarrow> Send*)
  "ctype_M as = range B"    | (* Med2 \<rightarrow> Send *)
  "ctype_M ds = range DBP"  | (* Send \<rightarrow> Med1 *)
  "ctype_M dr = range DBP"  | (* Med1 \<rightarrow> Recv *)
  "ctype_M abpOut = range D"    | (* Recv \<rightarrow> external *)
  "ctype_M ar = range B"      (* Recv \<rightarrow> Med2 *)

  instance
  by(intro_classes)
end



(* StBundles sARe defined with "M stream". these sARe converters from the "subtypes" of M to M and back *)
definition m2d :: "M tstream \<Rightarrow> data tstream" where
"m2d s \<equiv>  tstmap (inv D)\<cdot>s"
definition d2m :: "data tstream \<Rightarrow> M tstream" where
"d2m s \<equiv> tstmap D\<cdot>s"

definition m2b :: "M tstream \<Rightarrow> bool tstream" where
"m2b s \<equiv> tstmap (inv B)\<cdot>s" 
definition b2m :: "bool tstream \<Rightarrow> M tstream" where
"b2m s \<equiv> tstmap B\<cdot>s"

definition m2db :: "M tstream \<Rightarrow> (data\<times>bool) tstream" where
"m2db s \<equiv>  tstmap (inv DBP)\<cdot>s"
definition db2m :: "(data\<times>bool) tstream \<Rightarrow> M tstream" where
"db2m s \<equiv>  tstmap DBP\<cdot>s"










(* ----------------------------------------------------------------------- *)
  section \<open>Alternating Bit Protocol\<close>
(* ----------------------------------------------------------------------- *)

(* From here: Medium definition *)

(* tstream kein CPO, event stream allerdings, daher konvertierung *)
definition outswitch2 :: "'a event stream \<Rightarrow> bool stream \<Rightarrow> 'a event stream" where
"outswitch2 \<equiv> \<mu> f . (\<lambda>input oracle . 
  (* abort if inputs sARe empty *)
  if(input=\<epsilon> \<or> oracle = \<epsilon>) then \<epsilon> else 
    (* ignore -Tick- in input stream *)
    if (shd input = \<surd>) then \<up>\<surd> \<bullet> f (srt\<cdot>input) oracle else 
      (* if oracle is True then -shd input- is in the output stream *)
      if (shd oracle) then \<up>(shd input) \<bullet> f (srt\<cdot>input) (srt\<cdot>oracle) 
        (* otherwise delete -shd input- *)
        else f (srt\<cdot>input) (srt\<cdot>oracle) ) "


definition outswitch :: "'a tstream \<Rightarrow> bool stream \<Rightarrow> 'a tstream" where
"outswitch input oracle =(* [\<surd>] \<bullet>+*) Abs_tstream (outswitch2 (Rep_tstream input) oracle)"
                            (* \<bullet>+ = concat tStream *)


definition outswitch22:: "'a tstream \<Rightarrow> bool stream \<Rightarrow> 'a tstream" where
"outswitch22  \<equiv> \<mu> h . (\<lambda> input oracle .
                            let rest = (h (tsDropFirst\<cdot>input) (srt\<cdot>oracle)) in
                             if(input=\<bottom> \<or> oracle =\<bottom>) then \<bottom> else 
                               if (shd oracle = True) then (tsTakeFirst\<cdot>input) \<bullet> rest else
                                  rest)"


  
definition mediumTSPF :: "channel \<Rightarrow> channel \<Rightarrow> bool stream \<Rightarrow> 'm TSPF" where
"mediumTSPF cFrom cTo oracle \<equiv> Abs_TSPF (\<lambda> b. (tsbiDom\<cdot>b = {cFrom}) \<leadsto> 
          Abs_TSB_inf [cTo \<mapsto> outswitch22 (b . cFrom) oracle])"
                                    (* getChannel *)

definition medium :: "channel \<Rightarrow> channel \<Rightarrow> 'm TSPF set" where
"medium cFrom cTo = { (mediumTSPF cFrom cTo oracle) | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity> }"


(* ds \<rightarrow> Input, data\<times>bool *)
(* dr \<rightarrow> Output, data\<times>bool *)
lift_definition MED1 :: "'m TSPS" is "medium ds dr"
sorry

lift_definition MED2 :: "'m TSPS" is "medium ar as"
sorry


(* From here: Recv definition *)


(* dr \<rightarrow> Input, (data,bit) *)
(* abpOut \<rightarrow> Output, data without duplication  *)
(* ar \<rightarrow> Output, bit *)
lift_definition Recv :: "M TSPF" is
"(\<lambda>b. (tsbiDom\<cdot>b = {dr}) \<leadsto> 
    let sDR = (*[\<surd>] \<bullet>+ *)m2db (b . dr); (* the \<surd> is there to ensure strong causality *)
        sDRNoDup = tsrcdups sDR;
        out = d2m (tstprojfst\<cdot>sDRNoDup);
        sAR  = b2m (tstprojsnd\<cdot>sDR)   in 
    Abs_TSB_inf [abpOut \<mapsto> out, ar \<mapsto> sAR ])"
sorry

lift_definition RECV :: "M TSPS" is "{Recv}"
using tsps_well_def by auto



(* Send component *)



(* this function describes the "Send" psARt of the Alternating Bit Protocol *)

(* the 3. Input saves the time since the lsASt message wsAS sent *)
(* the 4. Input is the previous Message (prevM), in csASe this Message neesDS to be resend *)
definition send2 :: "data event stream \<Rightarrow> bool event stream \<Rightarrow> nat \<Rightarrow> (data\<times>bool) \<Rightarrow> (data\<times>bool) event stream " where
                                                         (* count    previous *)
"send2 \<equiv> \<mu> f . (\<lambda> input sASEvent count prevTupel. 
  (* if inputs sARe empty abort *)
  if (input = \<epsilon> \<or> sASEvent = \<epsilon>) then \<epsilon> else

    let newTupel = (inv Msg (shd input), \<not> snd prevTupel) in
                                      (* 2. element in tupel *)

    (* correct response from Recv sARrived, send next Data element *)
    if(shd sASEvent = Msg (snd prevTupel)) then <[Msg newTupel, \<surd>]> \<bullet> f (srt\<cdot>input) (srt\<cdot>sASEvent) 0 newTupel 
     (* bestätigung angekommen *)                                   (* delete first tick     counterReset *)
    else 
      (* if timeout (more than 3 ticks without response from Recv) then resend message *)
      if (count = 4) then (<[Msg prevTupel,\<surd>]>) \<bullet> f input (srt\<cdot>sASEvent) 0 prevTupel  
      
      (* no timeout, no correct response ... *)
      (* counter = 0,1,2,3 *)
      else \<up>\<surd> \<bullet> f input (srt\<cdot>sASEvent) (Suc count) prevTupel)"


definition send_helper :: "data tstream \<Rightarrow> bool tstream \<Rightarrow> (data\<times>bool) tstream" where
"send_helper input sAS \<equiv>
    let initialBit= False ;
        inS       = Rep_tstream input ; (* go inside tstreams, work with event streams*)
        sASEvent   = Rep_tstream sAS;
        sASAddHead = \<up>(Msg initialBit) \<bullet> sASEvent in
  Abs_tstream (send2 inS sASAddHead 0 (undefined, \<not>initialBit))"
(* go back to tstreams *)



(* Send-Component *)
  (* abpIn  \<rightarrow> Input,  Data *)
  (* as  \<rightarrow> Input,  Bit  *)
  (* ds  \<rightarrow> Output, Data\<times>Bit  *)
lift_definition Send :: "M TSPF" is
"\<lambda>b. (tsbiDom\<cdot>b = {abpIn,as}) \<leadsto> 
    let input = m2d (b . abpIn);
        sAS    = m2b (b . as);
        sDS    = db2m (send_helper input sAS) in
    Abs_TSB_inf [ds \<mapsto> (* [\<surd>] \<bullet>+ *) sDS]"
sorry


(* Send hat kein Oracel, ist also deterministisch *)
lift_definition SEND :: "M TSPS" is "{Send}"
using tsps_well_def by auto













(* ----------------------------------------------------------------------- *)
  subsection \<open>LemmsAS on ABP\<close>
(* ----------------------------------------------------------------------- *)

lemma send_dom [simp]: "tspfDom\<cdot>Send = {abpIn,as}"
(*apply(simp add: tspfDom_def Send.rep_eq)*)
(*apply(simp add: tsbDom_def tsb_welltyped_def)*)
sorry

lemma send_ran [simp]: "tspfRan\<cdot>Send = {ds}"
sorry

lemma medium_dom [simp]:"tspfDom\<cdot>(mediumTSPF cFrom cTo oracle) = {cFrom}"
(*apply(simp add: tspfDom_def mediumTSPF_def)*)
sorry

lemma medium_ran [simp]:"tspfRan\<cdot>(mediumTSPF cFrom cTo oracle) = {cTo}"
apply(simp add: tspfRan_def mediumTSPF_def)
sorry


(* lemmsAS über outswitch *)
lemma [simp]:"cont (\<lambda> f . (\<lambda>input oracle . 
  (* abort if inputs sARe empty *)
  if(input=\<epsilon> \<or> oracle = \<epsilon>) then \<epsilon> else 
    (* ignore -Tick- in input stream *)
    if (shd input = \<surd>) then \<up>\<surd> \<bullet> f (srt\<cdot>input) oracle else 
      (* if oracle is True then -shd input- is in the output stream *)
      if (shd oracle) then \<up>(shd input) \<bullet> f (srt\<cdot>input) (srt\<cdot>oracle) 
        (* otherwise delete -shd input- *)
        else f (srt\<cdot>input) (srt\<cdot>oracle) ))"
sorry

lemma outswitch2_eps [simp]: "outswitch2 \<epsilon> oracle = \<epsilon>"
by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_eps2 [simp]: "outswitch2 ts \<epsilon> = \<epsilon>"
by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_tick: assumes "oracle \<noteq> \<epsilon>"
  shows "outswitch2 (\<up>\<surd>\<bullet>ts) oracle = \<up>\<surd> \<bullet> outswitch2 ts oracle"
using assms by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_true:"outswitch2 (\<up>(Msg a) \<bullet> ts) (\<up>True \<bullet> os) = \<up>(Msg a) \<bullet> outswitch2 ts os"
by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_false: "outswitch2 (\<up>(Msg a) \<bullet> ts) (\<up>False \<bullet> os) = outswitch2 ts os"
by (subst outswitch2_def [THEN fix_eq2], auto)


lemma outswitch2_len [simp]: assumes "#(sfilter{True}\<cdot>oracle)=\<infinity>"
  shows "#(outswitch2 ts oracle) \<le> #ts"
sorry

lemma outswitch2_ticks [simp]: assumes "#oracle = \<infinity>"
  shows "#(sfilter {\<surd>}\<cdot>(outswitch2 ts oracle)) = #(sfilter {\<surd>}\<cdot>ts)"
sorry

lemma [simp]:  "Rep_tstream (Abs_tstream (outswitch2 (Rep_tstream ts) oracle)) = (outswitch2 (Rep_tstream ts) oracle)"
sorry

lemma outswitch_eps [simp]: "outswitch \<bottom> oracle = \<bottom>"
by (simp add: outswitch_def tsconc_insert espf2tspf_def)

lemma outswitch_tick: assumes "oracle \<noteq> \<epsilon>"
  shows "outswitch ((Abs_tstream (\<up>\<surd>)) \<bullet> ts) oracle = (Abs_tstream (\<up>\<surd>)) \<bullet> outswitch ts oracle"
by(simp add: outswitch_def tsconc_insert espf2tspf_def outswitch2_tick assms)





(* hier kommt die echte komposition *)

definition RecvMed1:: "bool stream \<Rightarrow> TSPF" where
"RecvMed1 oracle \<equiv> Abs_TSPF (\<lambda>b. (tsbDom\<cdot>b = {ds}) \<leadsto>
    let medOut =  (outswitch (b \<close> ds) oracle) in
  Abs_TSB [ ds \<mapsto> b \<close> ds,
            dr \<mapsto> medOut, 
            ar \<mapsto> b2m (tstprojsnd\<cdot>(m2db (medOut))) ])"

lemma sendmed1_well2 [simp]: "tsb_welltyped ([ ds \<mapsto> b\<close> ds,
            dr \<mapsto> medOut, 
            ar \<mapsto> b2m (tstprojsnd\<cdot>(m2db (medOut))) ])"
sorry

lemma sendmed1_well [simp]: "tspf_welltyped (\<lambda>b. (tsbDom\<cdot>b = {ds}) \<leadsto>
    let medOut =  (outswitch (b \<close> ds) oracle) in
  Abs_TSB [ ds \<mapsto> b \<close> ds,
            dr \<mapsto> medOut, 
            ar \<mapsto> b2m (tstprojsnd\<cdot>(m2db (medOut))) ])"
sorry

lemma [simp]: "tspfDom\<cdot>(RecvMed1 oracle) = {ds}"
apply(simp add: RecvMed1_def tspfdom_insert)
apply(simp add: tsbdom_insert)
sorry
(* by (smt Abs_cfun_inverse2 Send.rep_eq domIff option.simps(3) someI_ex tsbdom_insert tspfDom_def tspf_dom_cont tspfdom_eq)
*)

lemma [simp]: "tspfRan\<cdot>(RecvMed1 oracle) = {ds, dr, abpOut, ar}"
apply(simp add: RecvMed1_def tspfdom_insert)
apply(simp add: tsbdom_insert)
sorry

lemma [simp]: "tsb_welltyped [abpOut \<mapsto> d2m (tstprojfst\<cdot>(tsrcdups (m2db Rep_TSB b\<rightharpoonup>dr))), ar \<mapsto> b2m (tstprojsnd\<cdot>(m2db ((Rep_TSB b)\<rightharpoonup>dr)))]"
sorry

lemma [simp]: "tspf_welltyped (\<lambda>b. (tsbDom\<cdot>b = {ds})\<leadsto>Abs_TSB [dr \<mapsto> outswitch (b \<close> ds) oracle])"
sorry

lemma [simp]: "tspfDom\<cdot>Recv = {dr}"
apply(simp add: tspfdom_insert tsbdom_insert Recv.rep_eq Let_def)
by (smt Abs_cfun_inverse2 Recv.rep_eq domIff someI_ex tsbdom_insert tspfDom_def tspf_dom_cont tspfdom_eq)

lemma [simp]: "tspfRan\<cdot>Recv = {abpOut,ar}"
apply(simp add: tspfran_insert tsbdom_insert Recv.rep_eq Let_def)
sorry

lemma recv_ar[simp]: sASsumes "tsbDom\<cdot>b = {dr}"
  shows "((Rep_TSPF Recv) \<rightharpoonup> b) \<close>ar = b2m (tstprojsnd\<cdot>(m2db (b\<close>dr)))"
apply(simp add: Recv.rep_eq tspf_welltyped_def Let_def sASsms)
by(simp add: tsbgetch_insert)

lemma [simp]: sASsumes "tsbDom\<cdot>b = {dr}"
  shows "(Rep_TSPF Recv)\<rightharpoonup>b = Abs_TSB [ar \<mapsto>  b2m (tstprojsnd\<cdot>(m2db (b \<close> dr)))]"
sorry

lemma [simp]: "tsb_welltyped [dr \<mapsto> outswitch Rep_TSB b\<rightharpoonup>ds oracle]"
sorry

lemma [simp]: "tsb_welltyped [ds \<mapsto> Rep_TSB b\<rightharpoonup>ds, dr \<mapsto> outswitch Rep_TSB b\<rightharpoonup>ds oracle, ar \<mapsto>
             b2m (tstprojsnd\<cdot>(m2db (outswitch Rep_TSB b\<rightharpoonup>ds oracle)))]"
sorry

lemma [simp]: "tsbDom\<cdot>(Abs_TSB[dr \<mapsto> outswitch Rep_TSB b\<rightharpoonup>ds oracle]) = {dr}"
by(simp add: tsbdom_insert)



lemma comp_RecvMed1: sASsumes "tsbDom\<cdot>b = {ds}"
  shows "tspfCompHelpersHelper (mediumTSPF ds dr oracle) Recv b ((Rep_TSPF (RecvMed1 oracle))\<rightharpoonup>b)"
apply(simp add: tspfCompHelpersHelper_def Let_def)
apply rule+
apply(simp add: RecvMed1_def Let_def sASsms)
apply(simp add: tsbrestrict_insert sASsms)
apply(simp add: RecvMed1_def Let_def sASsms tsbrestrict_insert)
apply(simp add: mediumTSPF_def sASsms tsbgetch_insert)
apply(simp add: tsbdom_insert)
sorry



lemma comp_RecvMed12: sASsumes "tspfCompHelpersHelper (mediumTSPF ds dr oracle) Recv b x"
  shows "x=((Rep_TSPF (RecvMed1 oracle))\<rightharpoonup>b)"
using sASsms apply(simp add: tspfCompHelpersHelper_def Let_def)
apply(simp add: RecvMed1_def Let_def sASsms)
apply(simp add: tsbrestrict_insert)
apply rule+
sorry



lemma sASsumes "tsbDom\<cdot>b = {ds}"
  shows "(((Rep_TSPF ((mediumTSPF ds dr oracle) \<otimes> Recv)))\<rightharpoonup>b) \<close> ar = (Rep_TSPF (RecvMed1 oracle)) \<rightharpoonup>b \<close> ar(* outswitch (b\<close>ds) oracle *)"
apply(simp add: tspfComp_def)
apply(simp add: tspfCompHelper2_def Let_def sASsms)
apply(simp add: tsbgetch_insert)
by (metis sASsms comp_RecvMed1 comp_RecvMed12 theI_unique)



lift_definition SENDMED1 :: TSPS is 
  "{ SendMed1 oracle | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity> }"
sorry

lemma comp2SendMed2: sASsumes "#(sfilter{True}\<cdot>oracle)=\<infinity>"
  shows "Send \<otimes> (mediumTSPF ds dr oracle) = SendMed1 oracle"
apply(simp add: tspfComp_def tspfCompHelper2_def Let_def)
apply auto
sorry

lemma sendMedComp: "SEND \<Otimes> MED1 = Abs_TSPS {Send \<otimes> (mediumTSPF ds dr oracle) | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity>}"
apply(simp add: tspsComp_def SEND.rep_eq MED1.rep_eq medium_def)
by metis

lemma "SEND \<Otimes> MED1 = SENDMED1"
by (smt Collect_cong SENDMED1_def comp2SendMed2 sendMedComp)
(*
proof (rule tsps_eq)
  fix f1
  sASsume f1_def: "f1 \<in> Rep_TSPS (SEND \<Otimes> MED1)"
  hence "f1 \<in> Rep_TSPS SENDMED1"
  by (smt Collect_cong SENDMED1_def comp2SendMed2 sendMedComp)
 *)
(* hence f1_def2: "f1 \<in>{Send \<otimes> (mediumTSPF ds dr oracle) | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity>}"
    by (smt Collect_cong SENDMED1.rep_eq SENDMED1_def comp2SendMed2 sendMedComp)
  obtain oracel where "f1 = (Send \<otimes> (mediumTSPF ds dr oracel)) \<and> #(sfilter{True}\<cdot>oracel)=\<infinity>"
    using f1_def2 by blsASt
  thus "f1 \<in> Rep_TSPS SENDMED1" by (smt SENDMED1.rep_eq comp2SendMed2 mem_Collect_eq)
*)


(* example stream used als Input for the ABP-component*)
lift_definition tInHelper :: "M tstream" is "\<epsilon>"
(* "<[ (Msg (D (\<D> 1))), (Msg (D (\<D> 2))) ]>" *)
by simp

(* liftet --tInHelper-- to a TSB *)
lift_definition tIn :: TSB is 
"[abpIn \<mapsto> tInHelper]"
by(simp add: tsb_welltyped_def tsdom_insert tInHelper.rep_eq)



definition oneComp :: "bool stream \<Rightarrow> bool stream \<Rightarrow> TSPF" where
"oneComp oracle1 oracle2 \<equiv> let med1 = (mediumTSPF ds dr oracle1);
                               med2 =  (mediumTSPF ar as oracle2) in
                           (Send \<otimes> med1) \<otimes> (Recv \<otimes> med2)"

lemma oneComp_dom[simp]: "tspfDom\<cdot>(oneComp o1 o2) = {abpIn}"
sorry

lemma oneComp_ran[simp]: "tspfRan\<cdot>(oneComp o1 o2) = {abpOut}"
sorry

lemma goalTSPF [simp]: sASsumes "#(sfilter{True}\<cdot>oracle1)=\<infinity>" and "#(sfilter{True}\<cdot>oracle2)=\<infinity>"
  shows "tsabs ((the ((Rep_TSPF (oneComp oracle1 oracle2)) tIn)) \<close> abpOut ) = tsabs tInHelper"
sorry

lemma goalTSPF2 [simp]: sASsumes "#(sfilter{True}\<cdot>oracle1)=\<infinity>" 
        and "#(sfilter{True}\<cdot>oracle2)=\<infinity>" and "tsbDom\<cdot>input = {abpIn}" 
  shows "tsAbs\<cdot>((the ((Rep_TSPF (oneComp oracle1 oracle2)) input)) \<close> abpOut ) = tsAbs\<cdot>(input \<close> abpIn)"
sorry

(* the one component to rule them all *)
definition ONECOMP :: TSPS where
"ONECOMP \<equiv> (SEND \<Otimes> MED1) \<Otimes> (RECV \<Otimes> MED2)"

lift_definition OneCompTSPS ::TSPS is 
"{oneComp oracle1 oracle2 | 
                      oracle1 oracle2 .  #(sfilter{True}\<cdot>oracle1)=\<infinity> \<and>  #(sfilter{True}\<cdot>oracle2)=\<infinity>}"
apply(simp add: tsps_wellformed_def)
by fsAStforce

lemma ONE2one: "ONECOMP = OneCompTSPS"
apply(simp add: OneCompTSPS_def)
apply(simp add: ONECOMP_def oneComp_def tspsComp_def Let_def)
apply(simp add: MED1.rep_eq MED2.rep_eq SEND.rep_eq RECV.rep_eq)
apply(simp add: medium_def)
by (metis (no_types, hide_lams))


(* Goal1 : *)
lemma sASsumes "f \<in> (Rep_TSPS ONECOMP)"
  shows "tsAbs\<cdot>((the ((Rep_TSPF f) tIn)) \<close> abpOut ) = tsAbs\<cdot>tInHelper"
(* by (smt Abs_TSPS_inverse MED1.rep_eq MED2.rep_eq ONECOMP_def RECV.rep_eq SEND.rep_eq sASsms goalTSPF medium_def mem_Collect_eq oneComp_def singletonD tspsComp_def tspsComp_well)*)



(* Final Goal *)
(* take an sARbitrsARy stream in the spcification of ABP-component 
    and an sARbitrsARy input with correct domain *)
lemma sASsumes "f \<in> (Rep_TSPS ONECOMP)" and "tsbDom\<cdot>input = {abpIn}" 
  shows "tsAbs\<cdot>((the ((Rep_TSPF f) input)) \<close> abpOut ) = tsAbs\<cdot>(input \<close> abpIn)"
by (smt Abs_TSPS_inverse MED1.rep_eq MED2.rep_eq ONECOMP_def RECV.rep_eq SEND.rep_eq sASsms goalTSPF2 medium_def mem_Collect_eq oneComp_def singletonD tspsComp_def tspsComp_well)







(* OLD *)





end
