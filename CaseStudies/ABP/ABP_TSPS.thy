(*  Title:        ABP_TSPS.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  ABP modeled with TSPS
*)

theory ABP_TSPS
  imports "../../timed/TSPS" Sender Receiver Composition Medium "../../timed/TSPF" "../../UFun_Comp" "../../USpec_Comp"

begin

  default_sort countable


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)


datatype 'a::countable MABP = BoolPair "('a * bool)" | Bool bool | Data 'a

instantiation MABP ::  (countable) countable
begin
instance
   by (countable_datatype)
end


instantiation MABP ::  (countable) message
begin
fun ctype_MABP :: "channel \<Rightarrow> 'a MABP set" where
  "ctype_MABP c_abpIn = range Data" |
  "ctype_MABP c_abpOut = range Data" |
  "ctype_MABP c_ds = range BoolPair" |
  "ctype_MABP c_dr = range BoolPair" |
  "ctype_MABP c_as = range Bool" |
  "ctype_MABP c_ar = range Bool" |
  "ctype_MABP c_idOut = range Data" |
  "ctype_MABP other = undefined"

  instance ..
end

(*
instantiation MABP ::  (countable) message
begin
function ctype_MABP :: "channel \<Rightarrow> 'a MABP set" where
  "ctype_MABP (\<C> ''abpIn'') = range Data" |
  "ctype_MABP (\<C> ''abpOut'') = range Data" |
  "other \<noteq> (\<C> ''abpOut'') \<Longrightarrow> other \<noteq> (\<C> ''abpIn'') \<Longrightarrow> ctype_MABP other = undefined"
        apply simp_all
  sorry 
  instance ..
end*)

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


(* ----------------------------------------------------------------------- *)
section \<open>Helper Definitions\<close>
(* ----------------------------------------------------------------------- *)


subsection \<open>datatype destructors\<close>

abbreviation invBoolPair :: "'a MABP \<Rightarrow> ('a \<times> bool)" where
"invBoolPair \<equiv> (inv BoolPair)"

abbreviation invBool :: "'a MABP \<Rightarrow> bool" where
"invBool \<equiv> (inv Bool)"

abbreviation invData :: "'a MABP \<Rightarrow> 'a" where
"invData \<equiv> (inv Data)"       


(* ----------------------------------------------------------------------- *)
section \<open>Helper Definitions\<close>
(* ----------------------------------------------------------------------- *)



abbreviation recvAbb where
"recvAbb \<equiv>
let recRes = (\<lambda> x. tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))
in (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle([c_ar    \<mapsto> tsMap Bool\<cdot>(fst (recRes x)),
                                        c_abpOut \<mapsto> tsMap Data\<cdot>(snd (recRes x))]))"


subsection \<open>receiver\<close>
definition recvTSPF :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"recvTSPF \<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle([c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"

subsection \<open>medium_rs\<close>
  (* medium from receiver to sender *)
  (* input: c_ar, output: c_as, transport booleans *)

definition medRS_TSPF :: "bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"medRS_TSPF bst\<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"

abbreviation tsMedRSAbb  :: "bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option" where
"tsMedRSAbb bst x \<equiv> ((ubclDom\<cdot>x = {c_ar})
                            \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"

subsection \<open>medium_sr\<close>
  (* medium from sender to receiver *)
  (* input: c_ds, output: c_dr, transport (data, bool) tuples *)

definition medSR_TSPF :: "bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"medSR_TSPF bst\<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_ds})
  \<leadsto> Abs_ubundle([c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]))"

abbreviation medSR_TSPFAbb  :: "bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option" where
"medSR_TSPFAbb bst x \<equiv> ((ubclDom\<cdot>x = {c_ds})
  \<leadsto> Abs_ubundle([c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]))"

subsection \<open>sender\<close>

  (* lift a sender function to a TSPF *)
definition senderTSPF :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"senderTSPF se \<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"



subsection \<open>id\<close>


definition id_TSPF :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"id_TSPF \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> x . c_abpOut])"



(* ----------------------------------------------------------------------- *)
section \<open>Components\<close>
(* ----------------------------------------------------------------------- *)


lift_definition SND :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {senderTSPF s | s. s \<in> tsSender}"
  sorry

lift_definition RCV :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {recvTSPF}"
  sorry

lift_definition MEDSR :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  sorry

lift_definition MEDRS :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  sorry

lift_definition ID :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {id_TSPF}"
  sorry    

abbreviation gencompABP :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"gencompABP \<equiv> ((SND \<Otimes> MEDSR) \<Otimes> RCV) \<Otimes> MEDRS"

abbreviation speccompABP :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"speccompABP \<equiv> uspecFeedbackComp(((SND \<circle> MEDSR) \<circle> RCV) \<circle> (MEDRS \<parallel> ID))"


(* ----------------------------------------------------------------------- *)
section \<open>Testing of Composition without Medium\<close>
(* ----------------------------------------------------------------------- *)


definition senderTSPF2 :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"senderTSPF2 se \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"

lemma sender_mono: assumes "se \<in> tsSender" shows "monofun (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"
  sorry

lemma sender_cont: assumes "se \<in> tsSender" shows "cont (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"
  sorry

lemma sender_well: assumes "se \<in> tsSender" shows "ufWell (\<Lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"
  sorry

lift_definition SND2 :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {senderTSPF2 s | s. s \<in> tsSender}"
  sorry

definition recvTSPF2 :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"recvTSPF2 \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"

lemma recv_mono: "monofun (\<lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"
  sorry

lemma recv_cont: "cont (\<lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"
  sorry

lemma recv_well: "ufWell (\<Lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"
  sorry

lift_definition RCV2 :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {recvTSPF2}"
  sorry

abbreviation speccompABP_nmed :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"speccompABP_nmed \<equiv> uspecFeedbackComp(SND \<circle> RCV)"


lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "ds_stream = send\<cdot>i\<cdot>as_stream"
    and as_def: "as_stream = tsProjSnd\<cdot>ds_stream"
    and i_inf: "#\<surd>i = \<infinity>"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds_stream) = tsAbs\<cdot>i"
  using as_def ds_def send_def tsaltbitpro_inp2out_nmed by auto

lemma h1: assumes "s \<in> tsSender" shows "UFun.ufDom\<cdot>(ufunclSerComp (senderTSPF2 s) recvTSPF2) = {c_abpIn, c_ar}"
  apply (simp add: ufdom_insert ubclDom_ubundle_def)
  sorry                                                              

lemma h2: assumes "s \<in> tsSender" shows "UFun.ufRan\<cdot>(ufunclSerComp (senderTSPF2 s) recvTSPF2) = {c_abpOut, c_ar}"
  sorry

abbreviation abpFixH :: "('a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream) \<Rightarrow>  'a MABP tstream ubundle \<Rightarrow> 'a MABP tstream ubundle \<rightarrow> 'a MABP tstream ubundle" where
"abpFixH s tb \<equiv> (\<Lambda> x. Abs_ubundle[c_dr \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar))),
                                    c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                    c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))
                                   ])"

lemma abp_speccomp: assumes "f \<in> Rep_rev_uspec speccompABP_nmed"
                            and "ubDom\<cdot>tb = {c_abpIn}"
                          shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
proof - 
  have f1: "\<exists> s \<in> tsSender. (f = (\<mu>(ufunclSerComp (senderTSPF2 s) recvTSPF2)))"
    apply (simp add: ufunclSerComp_ufun_def)
    (* Cannot be proven until Instatiation *)
    sorry
  then obtain s where f12: "s \<in> tsSender \<and> (f = (\<mu>(ufunclSerComp (senderTSPF2 s) recvTSPF2)))"
    by blast
  then have f13: "f = (\<mu>(ufunclSerComp (senderTSPF2 s) recvTSPF2))"
    by blast
  have f14: "s \<in> tsSender"
    using f12 by blast


  have f20: "ubclDom\<cdot>tb = {c_abpIn, c_ar} - {c_ar}"
    apply(simp add: ubclDom_ubundle_def)
    using assms by blast                    
  have f2: "(f \<rightleftharpoons> tb) . c_abpOut =  ubFix (ufFeedH (ufunclSerComp (senderTSPF2 s) recvTSPF2) tb) {c_abpOut, c_ar}  .  c_abpOut"
    apply(subst f13)
    apply(simp add: ufFeedbackComp_def)
    apply(simp add: ufFeedbackComp_cont ufFeedbackComp_well)
    apply(simp add: f12 h1 h2)
    by(simp add: f20)


  have f3: "cont (\<lambda> x. Abs_ubundle[c_dr \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar))),
                                    c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                    c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))
                                   ])"
    sorry
  have f4: "ubFix (ufFeedH (ufunclSerComp (senderTSPF2 s) recvTSPF2) tb) {c_abpOut, c_ar}  .  c_abpOut
          = ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr} . c_abpOut"
    (* Should be possible to prove with equality of lubs *)
    sorry
  have f5: "ubfun_io_eq (abpFixH s tb) {c_abpOut, c_ar, c_dr}"
    sorry
  then have f6: "ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr} =  (abpFixH s tb)\<cdot>(ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr})"
    using ubfix_eq by blast


  (* After proving the fixed points propties we can now show the assumptions of the tsaltbitpro_inp2out_nmed lemma *)
  (*
    i = (tsMap invData\<cdot>(tb . c_abpIn))
    ds_stream = (tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))
    as_stream = (tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))

  *)
  have f7: "(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr)) = s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))"
    sorry

  have f8: "(tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar)) = tsProjSnd\<cdot>(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))"
    sorry

  (* More assms are necessary for this subgoal*)
  have f9: "#\<surd>(tsMap invData\<cdot>(tb . c_abpIn)) = \<infinity>"
    sorry

  (* Result of tsaltbitpro_inp2out_nmed lemma *)
  have f10: "tsAbs\<cdot>(tsRecSnd\<cdot>(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))) = tsAbs\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))"
    using f7 f8 f9 f14 by(simp add: tsaltbitpro_inp2out_nmed)
  
  

  
  show ?thesis
      sorry  
qed






(* ----------------------------------------------------------------------- *)
section \<open>More Lemmas\<close>
(* ----------------------------------------------------------------------- *)

(*
lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "c_ds = send\<cdot>i\<cdot>c_as"
    and as_def: "c_as = tsProjSnd\<cdot>c_ds"
    and i_inf: "#\<surd>i = \<infinity>"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>c_ds) = tsAbs\<cdot>i"
  sorry    

lemma tsaltbitpro_inp2out:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "c_ds = send\<cdot>i\<cdot>c_as"
    and dr_def: "c_dr = tsMed\<cdot>c_ds\<cdot>p1"
    and ar_def: "c_ar = tsProjSnd\<cdot>c_dr"
    (* definition 5 *)
    and as_def: "c_as = tsMed\<cdot>c_ar\<cdot>p2"
    and i_ninf: "#(tsAbs\<cdot>i) \<noteq> \<infinity>"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>c_dr)) = tsAbs\<cdot>i"
  sorry
*)


lemma abp_gencomp_final: assumes "f \<in> Rep_rev_uspec gencompABP"
                            and "ubDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
  oops  

lemma abp_speccomp_final: assumes "f \<in> Rep_rev_uspec speccompABP"
                            and "ubDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
  oops 



(* ----------------------------------------------------------------------- *)
section \<open>lemmata\<close>
(* ----------------------------------------------------------------------- *)

subsection \<open>general\<close>

lemma tsmap_id[simp]: assumes "inj f" shows "tsMap (inv f)\<cdot>(tsMap f\<cdot>ts) = ts"
apply(induction ts)
by(simp_all add: assms tsmap_delayfun  tsmap_mlscons)

lemma med_ora_length: assumes "#({True} \<ominus> ora) = \<infinity>"
  shows "#ora = \<infinity>"
  using assms sfilterl4 by auto  
  
subsection \<open>datatype\<close>

  (* inverse BoolPair applied to BoolPair is identity *)
lemma data_bool_pair_inv [simp]: "(invBoolPair) (BoolPair x) = x"
  by (meson MABP.inject(1) f_inv_into_f rangeI)

  (* inverse Bool applied to Bool is identity *)
lemma data_bool_inv [simp]: "(inv Bool) (Bool x) = x"
  by (meson MABP.inject(2) f_inv_into_f rangeI)

  (* inverse Data applied to Data is identity *)
lemma data_data_inv [simp]: "(inv Data) (Data x) = x"
  by (meson MABP.inject(3) f_inv_into_f rangeI)


subsection \<open>id\<close>

lemma id_result_well: "ubWell [c_idOut \<mapsto> x . c_abpOut]"
  apply (rule ubwellI)
  apply (simp add: domIff)
  sorry

lemma id_in_out_eq: assumes "ubDom\<cdot>(x::'a::uscl\<^sup>\<Omega>) = {c_abpOut}"
  shows "((\<lambda> (x::'a::uscl\<^sup>\<Omega>). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> x . c_abpOut])\<rightharpoonup>(x::'a::uscl\<^sup>\<Omega>)) . c_idOut= (x::'a::uscl\<^sup>\<Omega>) . c_abpOut"
  apply simp
  apply (rule, rule)
   apply (simp_all add: assms)
   by (simp add: id_result_well ubgetch_ubrep_eq)

 thm Rep_ubundle_inject
lemma id_tspf_cont: "cont (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> x . c_abpOut])"
  apply (rule contI2)
   apply (rule monofunI)
   apply (case_tac "(ubDom\<cdot>x = {c_abpOut})")
    apply (frule ubcldom_fix)
    apply (simp, rule, rule)
  apply (rule some_below)
     apply (subst below_ubundle_def)
     apply (simp add: id_result_well part_below ubgetch_below ubclDom_ubundle_def)
    apply (simp add: ubdom_below) +
  apply (rule, rule, rule)
  apply (subst some_lub_chain_eq3)
   apply (rule chainI)
   apply (simp add: id_result_well po_class.chainE ubgetch_below ubrep_lessI)
proof - 
  fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
  assume a1: "ubDom\<cdot>(Lub Y) = {c_abpOut}" and chain_Y: "chain Y" 
  have f0: "\<And> i. ubDom\<cdot>(Y i) = {c_abpOut}"
    by (simp add: a1 chain_Y)
  have f1: "chain (\<lambda> i. [c_idOut \<mapsto> Y i  .  c_abpOut])"
    by (simp add: chain_Y part_map_chain)
  have f2: "ubWell (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut])"
    using adm_def f1 id_result_well ubWell_adm by auto
  have f3: "chain (\<lambda>i::nat. Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])"
    apply (rule chainI)
    by (simp add: chain_Y id_result_well po_class.chainE ubgetch_below ubrep_lessI)
  have f4: "Rep_ubundle (Abs_ubundle (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut])) = Rep_ubundle (\<Squnion>i::nat. Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])"
    apply (simp add: f2)
    by (metis (mono_tags, lifting) f3 id_result_well lub_eq ubrep_lub ubrep_ubabs)
  have f5: "(Abs_ubundle (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut])) = (\<Squnion>i::nat. Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])"
    using Rep_ubundle_inject f4 by blast
  have f6: "chain (\<lambda> i. (Y i) . c_abpOut)"
    by (simp add: chain_Y)
  have f7: "dom [c_idOut \<mapsto> \<Squnion>i::nat. Y i  .  c_abpOut] = dom (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut])"
    by (metis (no_types, lifting) dom_fun_upd f1 option.simps(3) part_dom_lub)
  have f8: "\<And> i. dom (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut]) = dom [c_idOut \<mapsto> Y i  .  c_abpOut]"
    using f7 by auto
  have f9: "\<And> i. dom [c_idOut \<mapsto> Y i  .  c_abpOut] = {c_idOut}"
    by (simp add: domIff)
  have f10: "\<And> x. x \<noteq> c_idOut \<Longrightarrow> (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut]) x = None"
    using dom_def f8 by auto
  have f11: "\<forall> i . [c_idOut \<mapsto> Y i  .  c_abpOut] c_idOut \<sqsubseteq> (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut]) c_idOut"
    using fun_below_iff 
    by (metis (mono_tags, lifting) f1 is_ub_thelub)
  have f12: "\<Squnion> i. ([c_idOut \<mapsto> Y i  .  c_abpOut] c_idOut) \<sqsubseteq> (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut]) c_idOut"
    using f11 by auto
  have f13: "Some (\<Squnion>i::nat. Y i  .  c_abpOut) =  (\<Squnion>i::nat. Some (Y i  .  c_abpOut))"
    apply (subst some_lub_chain_eq3)
     apply (rule chainI)
     apply (simp add: chain_Y monofun_cfun_arg po_class.chainE)
    by simp
  have f14: "(\<Squnion>i::nat. Some (Y i  .  c_abpOut)) = (\<Squnion> i. ([c_idOut \<mapsto> Y i  .  c_abpOut] c_idOut))"
    by simp
  have f15: " Some (\<Squnion>i::nat. Y i  .  c_abpOut) \<sqsubseteq> (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut]) c_idOut"
    apply (subst f13)
    apply (subst f14)
    using f1 lub_fun by fastforce
  have f6: "[c_idOut \<mapsto> \<Squnion>i::nat. Y i  .  c_abpOut] \<sqsubseteq> (\<Squnion>i::nat. [c_idOut \<mapsto> Y i  .  c_abpOut])"
    apply (simp add: fun_below_iff)
    using f10 f15 by auto
  show "Some (Abs_ubundle [c_idOut \<mapsto> Lub Y  .  c_abpOut]) \<sqsubseteq> Some (\<Squnion>i::nat. Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])"
    apply (subst contlub_cfun_arg, simp add: chain_Y)
    apply (rule some_below)
    apply (fold f5)
  proof -
    have "(\<Squnion>n. [c_idOut \<mapsto> Y n . c_abpOut] c_idOut) = Some (\<Squnion>n. Y n . c_abpOut)"
      using f13 f14 by presburger
    then have "(\<Squnion>n. [c_idOut \<mapsto> Y n . c_abpOut]) = [c_idOut \<mapsto> \<Squnion>n. Y n . c_abpOut]"
      by (simp add: f1 fun_belowI lub_fun po_eq_conv)
    then show "Abs_ubundle [c_idOut \<mapsto> \<Squnion>n. Y n . c_abpOut] \<sqsubseteq> Abs_ubundle (\<Squnion>n. [c_idOut \<mapsto> Y n . c_abpOut])"
      by simp
  qed
qed



lemma id_tspf_well: "ufWell (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> x . c_abpOut]))"
  apply (rule ufun_wellI)
    apply (simp_all add: Abs_cfun_inverse2 id_tspf_cont ubclDom_ubundle_def)
    apply (simp_all add: domIff2)
  apply (simp add: ubDom_def)
  by (simp add: id_result_well)

lemma id_tspf_dom: "ufDom\<cdot>id_TSPF = {c_abpOut}"
  apply (simp add: id_TSPF_def ufDom_def)
  apply (simp add: id_tspf_well id_tspf_cont)
  apply (simp add: domIff)
  by (metis ubclDom_h ubclDom_ubundle_def)

lemma id_tspf_ran: "ufRan\<cdot>id_TSPF = {c_idOut}"
  apply (simp add: ufran_least)
  apply (simp add: ubclDom_ubundle_def ubclLeast_ubundle_def)
proof -
  have f1: "ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>u = {c_abpOut})\<leadsto>Abs_ubundle [c_idOut \<mapsto> u . c_abpOut::'a MABP tstream])) = {c_abpOut}"
    by (metis (no_types) id_TSPF_def id_tspf_dom)
  have "\<And>c. ubWell [c \<mapsto> \<bottom>::'a MABP tstream]"
    by (metis (no_types) insertI1 option.sel ubWell_single_channel ubgetchE ubleast_ubdom ubleast_ubgetch)
  then show "ubDom\<cdot> (id_TSPF \<rightleftharpoons> (ubLeast (ufDom\<cdot> (id_TSPF::('a MABP tstream\<^sup>\<Omega>) ufun))::'a MABP tstream\<^sup>\<Omega>)) = {c_idOut}"
    using f1 by (simp add: id_TSPF_def id_tspf_cont id_tspf_well ubdom_ubrep_eq)
qed

subsection \<open>receiver\<close>

subsubsection \<open>defs\<close>

      (* helper functions to prove cont *)
definition recvCH1 :: "'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"recvCH1 \<equiv> (\<lambda> x. tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr)))))"

definition recvCH2 :: "'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"recvCH2 \<equiv> (\<lambda> x. tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr)))))"

lemma recvCH1_contlub: assumes "chain Y"
  shows "recvCH1 ((\<Squnion>i. Y i)) = (\<Squnion>i. (recvCH1 ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms recvCH1_def)

lemma recvCH2_contlub: assumes "chain Y"
  shows "recvCH2 ((\<Squnion>i. Y i)) = (\<Squnion>i. (recvCH2 ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms recvCH2_def)

lemma to_recvch1: "tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr))))
                    = (recvCH1::'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) x"
  by (simp add: recvCH1_def)

lemma to_recvch2: "tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr))))
                    = (recvCH2::'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) x"
  by (simp add: recvCH2_def)

lemma recv_tsb_well [simp]:
  shows "ubWell [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                  c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]"
  apply (rule ubwellI)
  apply (simp add: tsmap_tsdom_range)
proof -
  fix c::channel
  assume a1: "c = c_abpOut \<or> c = c_ar"
  show "(c = c_ar \<longrightarrow> usclOkay c_ar (tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr)))))) \<and>
                  (c \<noteq> c_ar \<longrightarrow> (c = c_abpOut \<longrightarrow> usclOkay c_abpOut (tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr)))))) \<and> (c \<noteq> c_abpOut \<longrightarrow> usclOkay c (the None)))"
    apply rule
    using tsmap_tsdom_range usclOkay_tstream_def apply fastforce
  proof rule
    assume a2: "c \<noteq> c_ar"
    have f1: "c = c_abpOut"
      using a1 a2 by auto
    show "(c = c_abpOut \<longrightarrow> usclOkay c_abpOut (tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr)))))) \<and> (c \<noteq> c_abpOut \<longrightarrow> usclOkay c (the None))"
      apply rule
      using tsmap_tsdom_range usclOkay_tstream_def apply fastforce
      by (simp add: f1)
  qed
qed

lemma recv_tsb_dom: "ubclDom\<cdot>(Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                              c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))
                     = {c_ar, c_abpOut}"
  by (simp add: insert_commute ubclDom_ubundle_def ubdom_ubrep_eq)



lemma rec_tsb_mono: "\<And>(x::'a MABP tstream ubundle) y::'a MABP tstream ubundle. ubclDom\<cdot>x = {c_dr} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow>
          Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr)))),
          c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr))))])
          \<sqsubseteq> Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  c_dr)))),
             c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  c_dr))))])"
      apply (rule ub_below)
       apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
       by (simp add: fst_monofun snd_monofun monofun_cfun_arg ubgetch_below)
                                                                       

lemma recvTSPF_mono [simp]: "monofun (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto>
                                    Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                     c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x = {c_dr}")
   apply (simp add: ubdom_below rec_tsb_mono some_below ubcldom_fix)
  by (simp add: ubdom_below ubcldom_fix)

lemma recvTSPF_tsb_getc: assumes "chain Y" and "ubclDom\<cdot>(\<Squnion>i. Y i) = {c_dr}"
  and "c \<in>  {c_ar, c_abpOut}"
  shows " (\<Squnion>i.
           Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])) . c
          = (\<Squnion> i. (Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])) . c)"
proof (rule lubgetCh)
   have f2: "\<And> i. ubclDom\<cdot>(Y i) =  ubclDom\<cdot>(\<Squnion>i. Y i)"
     by (simp add: assms(1) ubclDom_ubundle_def)
   show tb_chain: "chain (\<lambda>i::nat. Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))),
                             c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
     by (simp add: assms(1) assms(2) f2 po_class.chainE po_class.chainI rec_tsb_mono)

   show " c \<in> ubclDom\<cdot>(\<Squnion>i::nat.
                          Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))),
                       c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
     using assms(3) recv_tsb_dom tb_chain ubcldom_lub_eq2I by blast
qed


  (* show that recTSPF is cont, proof concept taken from TSPF_Template_CaseStudy *)
lemma recvTSPF_cont [simp]:
  shows "cont (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto>
                      Abs_ubundle([c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                       c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"
proof (rule ufun_contI, simp add: rec_tsb_mono)
    fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
    assume Y_is_chain: "chain Y" and chain_Y_dom: "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_dr}"
    have f1: "\<And> i. (ubclDom\<cdot>(\<Squnion>i. Y i)) =  (ubclDom\<cdot>(Y i))"
      by (simp add: Y_is_chain ubclDom_ubundle_def)
    have f11: "\<And>i . (ubclDom\<cdot>(Y i)) = {c_dr}"
      using chain_Y_dom f1 by auto
    have "\<And> i. ubWell [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]"
      by simp
    have f12: "(ubclDom\<cdot>(\<Squnion>i::nat. Y i) =
        {c_dr})\<leadsto>Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))] = 
            Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))])"
      by (simp add: chain_Y_dom)
    have f13: "(\<Squnion>i::nat. (ubclDom\<cdot>(Y i) = {c_dr})\<leadsto>Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]) = 
            (\<Squnion>i::nat. Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      by (simp add: f11)
    have f14:"Some (\<Squnion>i::nat. (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))
          = (\<Squnion>i::nat. Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      apply (rule some_lub_chain_eq)
      apply (simp add: chain_def)
      by (simp add: Y_is_chain f11 po_class.chainE rec_tsb_mono)
    have f15: "ubclDom\<cdot>(Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))]) =
                ubclDom\<cdot>(\<Squnion>i::nat. (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      apply (simp add: ubclDom_ubundle_def)
      by (metis (mono_tags, lifting) Y_is_chain f11 po_class.chain_def rec_tsb_mono recv_tsb_dom ubclDom_ubundle_def ubdom_chain_eq2)
    have f17: "\<And> c::channel. (\<Squnion>i::nat. Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])  .  c =
          (\<Squnion>i::nat. Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))] . c)"
      apply (rule cont2contlubE)
      by (simp add: Y_is_chain f11 po_class.chainE po_class.chainI rec_tsb_mono) +
    have f20: "Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))]) \<sqsubseteq>
       Some (\<Squnion>i::nat. (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      apply (rule some_below)
      apply (rule ub_below)
       apply (metis (no_types, lifting) f15 ubclDom_ubundle_def)      
      apply (subst f17)
      apply (simp add: recvTSPF_tsb_getc ubdom_ubrep_eq ubgetch_ubrep_eq) 
      by (metis (mono_tags, lifting) Y_is_chain eq_imp_below lub_eq recvCH1_contlub recvCH2_contlub to_recvch1 to_recvch2)
    show "Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))] \<sqsubseteq>
       (\<Squnion>i::nat. Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])"
      using f20 some_below2 by blast
qed


  subsubsection \<open>tspf_well\<close>
declare [[simp_trace_new]]
 (* show that the recvTSPF fulfills the tickcount property *)
lemma recvTSPF_tick: assumes "ubDom\<cdot>b = {c_dr}" and "(ubLen b) = n"
  shows "n \<le> (ubLen (Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))),
                       c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr))))])))"
proof -
  have "(ubLen b) = usclLen\<cdot>(b . c_dr)"
    using assms(1) uslen_ubLen_ch3 by auto
  hence f1: "n = #\<surd>(b . c_dr)"
    by (metis assms(2) usclLen_tstream_def)
  hence f2: "n \<le> #\<surd>(tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))))"
    by (simp add: tsrec_insert)
  with f1 have f3: "n \<le> #\<surd>(tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))))"
    by (simp add: tsrec_insert)
  have f4: "ubDom\<cdot>(Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr))))])
    = {c_ar, c_abpOut}"
    by (metis recv_tsb_dom ubclDom_ubundle_def)
  show ?thesis 
    apply (rule ubLen_geI)
      apply (simp_all add: f4)
    apply (simp add: ubgetch_ubrep_eq)
    by (metis f2 f3 usclLen_tstream_def)
qed


  (* recvTSPF is an actual TSPF *)
lemma recvTSPF_well [simp]:
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto>
                      Abs_ubundle([c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                       c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"
  apply (rule ufun_wellI)
  by (simp_all add: domIff2 recv_tsb_dom)
                                     
lemma recv_revsubst: "Abs_cufun (recvAbb) = recvTSPF"
  by (simp add: recvTSPF_def)
    
lemma recv_tspfdom: "ufDom\<cdot>(recvTSPF) = {c_dr}"
  apply (simp add: ufDom_def recvTSPF_def)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)

lemma recv_tspfran: "ufRan\<cdot>(recvTSPF) = {c_ar, c_abpOut}"
  apply (simp add: ufran_least)
    apply (subst recv_tspfdom)
    apply (simp only: recvTSPF_def)
  by (simp add:  recv_tsb_dom ubcldom_least_cs) 

subsection \<open>sender\<close>
(*

  (* lift a sender function to a TSPF *)
definition senderTSPF :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"senderTSPF se \<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"

*)

definition senderCH :: "'a sender \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"senderCH se \<equiv> (\<lambda> x. tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))))"


lemma senderCH_contlub: assumes "chain Y"
  shows "senderCH se ((\<Squnion>i. Y i)) = (\<Squnion>i. (senderCH se ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: senderCH_def assms)

lemma to_senderch: "tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))
                    = senderCH se x"
  by (simp add: senderCH_def)

lemma sender_tsb_well [simp]: "ubWell [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]"
  apply (rule ubwellI)
  by (simp add: tsmap_tsdom_range usclOkay_tstream_def)

lemma sender_tsb_dom1: "ubclDom\<cdot>(Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))
                     = {c_ds}"
  by (simp add: ubclDom_ubundle_def ubdom_ubrep_eq)

lemma sender_tsb_mono: "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubclDom\<cdot>x = {c_as, c_abpIn} \<Longrightarrow>
       x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(x  .  c_as)))] \<sqsubseteq> Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(y  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(y  .  c_as)))]"
  apply (rule ub_below)
  apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
  by (simp add: monofun_cfun)

lemma sender_tspf_cont [simp]: "cont (\<lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((se::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"
proof (rule ufun_contI, simp add: sender_tsb_mono)
  fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
  assume a1: "chain Y" and a2: "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_as, c_abpIn}"
  have f1: "chain (\<lambda> i. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))])"
    apply (rule chainI)
    apply (rule ub_below)
     apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
    by (simp add: a1 monofun_cfun po_class.chainE)
  have f2: "(\<Squnion>i::nat. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))])  .  c_ds =
    (\<Squnion>i::nat. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))]  .  c_ds)"
    apply (rule cont2contlubE)
    by (simp add: f1) +
  have f4: "tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>((Lub Y)  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((Lub Y)  .  c_as))) =
    (senderCH se (Lub Y))"
    by (simp add: senderCH_def)
  have f5: "\<And> i. tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as))) = 
    (senderCH se (Y i))"
    by (simp add: senderCH_def)
  show "Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>((\<Squnion>i::nat. Y i)  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_as)))] \<sqsubseteq>
       (\<Squnion>i::nat. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))])"
    apply (rule ub_below)
     apply (simp_all add: ubclDom_ubundle_def ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
     apply (simp add: cont2contlubE f1 ubdom_ubrep_eq) 
    apply (subst f2)
    apply (simp_all add: ubgetch_ubrep_eq)
    apply (subst f4)
    apply (subst f5)
    by (simp add: a1 senderCH_contlub)
qed

subsubsection \<open>tspf_well\<close>

lemma ublen_min_eq_2_ch: assumes "ubDom\<cdot>b = {ch1, ch2}"
  shows "(ubLen b) = min (usclLen\<cdot>(b . ch1)) (usclLen\<cdot>(b . ch2))"
  apply (simp add: ubLen_def assms(1))
  apply (rule Least_equality)
   apply (metis min_def_raw)
  by auto

lemma senderTSPF_tick: assumes "ubDom\<cdot>b = {c_as, c_abpIn}" and "(ubLen b) = n" and "se \<in> tsSender"
  shows "n \<le> (ubLen (Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((se::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(b . c_abpIn))\<cdot>(tsMap invBool\<cdot>(b . c_as)))])))"  
proof -  
  have f00: "#\<surd> (b . c_abpIn) = #\<surd> (tsMap invData\<cdot>(b  .  c_abpIn))"
    by simp
  have f01: "#\<surd> (b . c_as) = #\<surd> (tsMap invBool\<cdot>(b  .  c_as))"
    by simp
  have f02: "n = ubLen b"
    by (simp add: assms(2))
  have f07: "n = min (usclLen\<cdot>(b . c_abpIn)) (usclLen\<cdot>(b . c_as))"
    by (simp add: assms(1) f02 min.commute ublen_min_eq_2_ch)
  have f08: "min (usclLen\<cdot>(b  .  c_abpIn)) (usclLen\<cdot>(b  .  c_as)) = 
          min (#\<surd> (tsMap invData\<cdot>(b  .  c_abpIn))) (#\<surd> (tsMap invData\<cdot>(b  .  c_as)))"
    by (simp add: usclLen_tstream_def)
  have f20: "min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)) = \<infinity> 
    \<Longrightarrow> #\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b  .  c_as)))) = \<infinity>"
  proof -
    assume a1: "min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)) = \<infinity>"
    obtain Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>" where Y_def: "Y \<equiv> (\<lambda> i. b \<down> i)"
      by simp
    have f200: "chain Y"
      apply (rule chainI, simp add: Y_def)
      apply (rule ub_below)
      by simp+
    have f201: "b = (\<Squnion> i. Y i)"
      by (simp add: Y_def)
    have f202: "\<And>i. Y i = b \<down> i"
      by (simp add: Y_def)
    have f203: "\<And> i. ubLen (Y i) = min (#\<surd> tsMap invData\<cdot>((Y i) .  c_abpIn)) (#\<surd> tsMap invData\<cdot>((Y i) .  c_as))"
      apply (simp add: Y_def ubLen_def assms(1))
      apply (rule Least_equality)
       apply (metis (no_types, lifting) a1 assms(1) f08 inf_ub insertI1 min.absorb2 min_def tsbttake2ttakeI tstake_len usclLen_tstream_def)
      by (metis (no_types, lifting) assms(1) insertI1 insert_commute min.commute min.orderI min.right_idem tsbttake2ttakeI tstake_len usclLen_tstream_def)
    obtain se_y::"'a MABP tstream\<^sup>\<Omega> \<Rightarrow> lnat" where se_y_def: "se_y \<equiv> (\<lambda> b. #\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b .  c_as)))))"
      by simp
    obtain min_y::"'a MABP tstream\<^sup>\<Omega> \<Rightarrow> lnat" where min_y_def: "min_y \<equiv> (\<lambda> b. min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)))"
      by simp
    have se_tsmap_data_below: "\<And> i. se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn)) \<sqsubseteq> se\<cdot>(tsMap invData\<cdot>(Y (Suc i)  .  c_abpIn))"
      apply (subst cont_pref_eq1I) +
      by (simp_all add: f200 po_class.chainE)
    have ts_map_bool_below: "\<And> i. (tsMap invBool\<cdot>(Y i  .  c_as)) \<sqsubseteq> (tsMap invBool\<cdot>(Y (Suc i)  .  c_as))"
      apply (subst cont_pref_eq1I) +
      by (simp_all add: f200 po_class.chainE)
    have chain_se_y: "chain (\<lambda> i. se_y (Y i))"
      apply (simp add: se_y_def)
      apply (rule chainI)
      apply (subst cont_pref_eq1I)
       apply (meson below_trans cfun_below_iff cont_pref_eq2I se_tsmap_data_below ts_map_bool_below)
      by simp
    have chain_min_y: "chain (\<lambda>i . min_y (Y i))"
      apply (simp add: min_y_def)
      apply (rule chainI)
      by (meson cont_pref_eq1I f200 lnle_def min.mono po_class.chainE)
    have f299: "#\<surd> se\<cdot>(tsMap invData\<cdot>(Lub Y  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Lub Y  .  c_as)) = 
      #\<surd> se\<cdot>(tsMap invData\<cdot>((\<Squnion>i. Y i .  c_abpIn)))\<cdot>(tsMap invBool\<cdot>((\<Squnion>i. Y i  .  c_as)))"
      by (simp add: contlub_cfun_arg f200)
    have f300: "min_y (Lub Y) = ubLen b"
      using f02 f07 f08 f201 min_y_def by auto
    have f301: "\<And> j. min_y (Y j) \<sqsubseteq> se_y (Y j)"
      by (metis (no_types, lifting) Y_def a1 assms(1) assms(3) inf_less_eq insertI1 less_imp_le 
          lnle_conv min_def_raw min_y_def neqE notinfI3 se_y_def set2tssnd_strcausal tsbttake2ttakeI 
          tsmap_tstickcount tstake_len)
    have f302: "\<And> j. se_y (Y j) \<le> (\<Squnion> i. se_y (Y i))"
      using chain_se_y is_ub_thelub lnle_def by blast
    have f303: "(\<Squnion> i. min_y (Y i)) \<sqsubseteq> (\<Squnion> i. se_y (Y i))"
      using chain_min_y chain_se_y f301 lub_mono by blast
    have f304: "\<And>i. min_y (Y i) = Fin i"
      by (metis (no_types, lifting) Fin_neq_inf Y_def a1 assms(1) f00 inf_less_eq insertI1 
          insert_commute min.cobounded1 min.cobounded2 min_def min_def_raw min_y_def 
          tsbttake2ttakeI tsmap_tstickcount tstake_len)
    have f305: "(\<Squnion> i. min_y (Y i)) = \<infinity>"
      using chain_min_y f304 inf_belowI is_ub_thelub by fastforce
    have f50: " (\<Squnion> i. se_y (Y i)) = se_y (\<Squnion>i. Y i)"
      apply (simp add: se_y_def contlub_cfun_arg f200)
      apply (subst contlub_cfun_fun)
       apply (simp add: po_class.chainI se_tsmap_data_below)
      apply (subst contlub_cfun_arg)
      apply (simp add: po_class.chainI se_tsmap_data_below)
      apply (subst diag_lub)
       by (simp_all add: f200 po_class.chainE) +
     show "#\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b  .  c_as)))) = \<infinity>"
       apply (subst f201)
       using f201 f303 f305 f50 se_y_def by auto
  qed
  have f2: "n \<le> #\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b  .  c_as))))"
    apply (subst f07)
    apply (subst f08)
    apply (case_tac "min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)) < \<infinity>")
     apply (simp, metis assms(3) f00 f01 f08 less_imp_le set2tssnd_strcausal usclLen_tstream_def)
    using f20 by (simp add: less_le)
  show ?thesis
    apply (rule ubLen_geI)
    apply (simp_all add: ubclDom_ubundle_def ubdom_ubrep_eq ubgetch_ubrep_eq)
    by (metis f2 usclLen_tstream_def)
qed

lemma sendTSPF_well [simp]:
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((se::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"
  apply (rule ufun_wellI)
  by (simp_all add: domIff2 sender_tsb_dom1)


lemma sender_tspfdom: "ufDom\<cdot>(senderTSPF se) = {c_as, c_abpIn}"
  apply (simp add: ufDom_def senderTSPF_def)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)


lemma sender_tspfran: "ufRan\<cdot>(senderTSPF se) = {c_ds}"
  apply (simp add: ufran_least)
    apply (subst sender_tspfdom)
    apply (simp only: senderTSPF_def)
  by (simp add:  sender_tsb_dom1 ubcldom_least_cs) 


  subsection \<open>medium_rs\<close>

subsubsection \<open>defs\<close>

definition medRSH :: "bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"medRSH bst \<equiv> (\<lambda> x. (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst))"

lemma medrsh_cont [simp]: "cont (medRSH bst)"
  by (simp add: medRSH_def)

lemma medrsh_contlub: assumes "chain Y"
  shows "(medRSH bst) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medRSH bst) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medrsh: "tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst)
                  = ((medRSH :: bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) bst) x"
  by (simp add: medRSH_def)

subsubsection \<open>pre\<close>

lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast


lemma medrs_tsb_well [simp]: "ubWell  [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]"
  apply (rule ubwellI)
  apply (simp add: usclOkay_tstream_def)
  by (simp add: tsmap_tsdom_range)

lemma medrs_tsb_dom: "ubclDom\<cdot>(Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)])) = {c_as}"
  apply (simp add: ubclDom_ubundle_def)
  by (simp add: ubdom_ubrep_eq)


subsubsection \<open>cont\<close>

  (* prerequirement for the mono proofs of the tspf *)
lemma medrs_tsb_mono: "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubclDom\<cdot>x = {c_ar} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst)]) \<sqsubseteq> Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(y  .  c_ar))\<cdot>bst)])"
  apply (simp_all add: ubclDom_ubundle_def)
  apply (rule ub_below)
  apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
  apply (simp add: to_medrsh)
  using cont2mono medrsh_cont monofun_def by blast


lemma medrs_mono [simp]: "monofun (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
  apply (rule ufun_monoI2)
  by (simp add: medrs_tsb_mono)

lemma medrs_tsb_getc: assumes "chain (Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>)" and "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar}"
                      and "c = c_as"
  shows "(\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))  .  c_as
          =  (\<Squnion>i::nat. (Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)])) . c_as)"
proof (rule lubgetCh)
  have f2: "\<And> i. ubclDom\<cdot>(Y i) =  ubclDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1) ubclDom_ubundle_def)
  show tb_chain: "chain (\<lambda>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
    by (simp add: assms(1) assms(2) f2 medrs_tsb_mono po_class.chainE po_class.chainI)
  show "c_as \<in> ubclDom\<cdot>(\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
    by (metis (mono_tags, lifting) insert_iff medrs_tsb_dom tb_chain ubclDom_ubundle_def ubdom_chain_eq2)
qed



lemma medrs_cont [simp]: "cont (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
proof (rule ufun_contI)
  show medrs_mo : "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubclDom\<cdot>x = {c_ar} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst)] 
          \<sqsubseteq> Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(y  .  c_ar))\<cdot>bst)]"
    by (simp add: medrs_tsb_well monofun_cfun_arg monofun_cfun_fun option.distinct(1) option.sel ub_below ubdom_ubrep_eq ubgetch_ubrep_eq)

  have f1: " \<And>Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar} \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)])) = {c_as}"
    by (metis (mono_tags, lifting) medrs_tsb_dom medrs_tsb_mono po_class.chain_def ubcldom_lub_eq2I)
  show "\<And>Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar} \<Longrightarrow>
       Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_ar))\<cdot>bst)]) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
  proof -
    fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
    assume chain_Y: "chain Y" and chain_Y_dom: "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar}"
    have f10: "(\<Squnion>i::nat. Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)])  .  c_as =
                    (\<Squnion>i::nat. Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]  .  c_as)"
      apply (rule cont2contlubE, simp)
      apply (rule chainI)
      by (simp add: chain_Y monofun_cfun_arg monofun_cfun_fun po_class.chainE ub_below ubdom_ubrep_eq ubgetch_ubrep_eq)
    show "Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_ar))\<cdot>bst)]) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
      apply (rule ub_below)
       apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq f1) 
       apply (metis (mono_tags, lifting) chain_Y chain_Y_dom f1 ubclDom_ubundle_def)
      apply (subst f10)
      by (metis (mono_tags, lifting) chain_Y fun_upd_same lub_eq medrs_tsb_well medrsh_contlub not_below2not_eq option.sel to_medrsh ubgetch_ubrep_eq)
  qed
qed


  subsubsection \<open>tspf_well\<close>
  
 (* show that the mediumRSTSPF template  fulfills the tickcount property *)
lemma medrs_tick: assumes "ubclDom\<cdot>b = {c_ar}" and "(ubLen b) = n" and "#bst=\<infinity>"
  shows "n \<le> (ubclLen (Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(b  .  c_ar))\<cdot>bst)])))"
proof -
  have "(ubLen b) = usclLen\<cdot>(b . c_ar)"
    apply (rule uslen_ubLen_ch3)
    by (metis assms(1) ubclDom_ubundle_def)
  hence f1: "n = usclLen\<cdot>(b . c_ar)"
    using assms(2) by blast
  hence f2: "n \<le> usclLen\<cdot>((tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(b  .  c_ar))\<cdot>bst))"
    by (simp add: assms(3) usclLen_tstream_def)
  show ?thesis
    apply (simp add: ubclLen_ubundle_def)
    apply (rule ubLen_geI)
    apply (simp add: medrs_tsb_dom ubgetch_ubrep_eq)
    by (simp add: f2 ubdom_ubrep_eq)
qed
  
      
    
  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma medrs_well [simp]: assumes "#bst=\<infinity>"
  shows "ufWell (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
  apply (rule ufun_wellI)
    apply (simp_all add: domIff2)
  by (simp add:  ubclDom_ubundle_def ubDom_def)

      
lemma medrs_revsubst: "Abs_cufun (tsMedRSAbb bst) = (medRS_TSPF bst)"
  by (simp add: medRS_TSPF_def)
    
lemma medrs_tspfdom: assumes "#bst =\<infinity>"
  shows "ufDom\<cdot>(medRS_TSPF bst) = {c_ar}"
    apply (simp add: medRS_TSPF_def)
    apply (simp add: ufdom_insert assms)
    apply (simp add: domIff2)
  by (simp add: ubclDom_h)
   
lemma medrs_tspfran: assumes "#bst =\<infinity>"
  shows "ufRan\<cdot>(medRS_TSPF bst) = {c_as}"   
    apply (simp add: medRS_TSPF_def)
    apply (simp add: ufran_least medrs_tspfdom assms)
    apply (simp add: medrs_revsubst medrs_tspfdom assms)
  by (simp add: medrs_tsb_dom ubcldom_least_cs)


  (* now special lemmata for TSPS instantiation *)

lemma medrs_well2 [simp]: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufWell (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
proof -
   have "#bst = \<infinity>"
     by (simp add: med_ora_length assms(1))
   thus ?thesis  
     by (simp add: medrs_tspfdom)
qed
  

lemma medrs_tspfdom2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufclDom\<cdot>(medRS_TSPF bst) = {c_ar}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medrs_tspfdom ufclDom_ufun_def)
qed
  
lemma medrs_tspfran2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufRan\<cdot>(medRS_TSPF bst) = {c_as}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medrs_tspfran)
qed

  (* necessary for TSPS instantiation *)
lemma medrs_tsps_dom1 [simp]: "f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufDom\<cdot>f = {c_ar}"
  by (metis medrs_tspfdom2 ufclDom_ufun_def)

lemma medrs_tsps_dom2 [simp]: "\<exists>ora::bool stream. f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufDom\<cdot>f = {c_ar}"
  using medrs_tsps_dom1  by auto
 
lemma medrs_tsps_ran1 [simp]: "f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufRan\<cdot>f = {c_as}"
  by (simp add: medrs_tspfran2)

lemma medrs_tsps_ran2 [simp]: "\<exists>ora::bool stream. f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufRan\<cdot>f = {c_as}"
  using medrs_tsps_ran1 by auto


      
  subsection \<open>medium_sr\<close>     

subsubsection \<open>defs\<close>

definition medSRH :: "bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"medSRH bst \<equiv> (\<lambda> x. (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst))"

lemma medsrh_cont [simp]: "cont (medSRH bst)"
  by (simp add: medSRH_def)

lemma medsrh_contlub: assumes "chain Y"
  shows "(medSRH bst) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medSRH bst) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medsrh: "tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_ds))\<cdot>bst)
                  = ((medSRH :: bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) bst) x"
  by (simp add: medSRH_def)

subsubsection \<open>pre\<close>
(*
lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast
*)

lemma medsr_tsb_well[simp]: "ubWell [c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]"
  apply (rule ubwellI)
  apply (simp add: usclOkay_tstream_def)
  by (simp add: tsmap_tsdom_range)

lemma medsr_tsb_dom: "ubDom\<cdot>(Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]) = {c_dr}"
  by (simp add: ubdom_ubrep_eq)
    
  subsubsection \<open>cont\<close>
    
(* definition tsMedSRTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedSRTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)" *)

(* this can be shown analogue to before *)
lemma medsr_cont [simp]: "cont (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (tsbDom\<cdot>x = {c_ds})
  \<leadsto> Abs_ubundle [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)])"
  sorry
    
 
  subsubsection \<open>tspf_well\<close>

lemma medsr_tick: assumes "ubDom\<cdot>b = {c_ds}" and "(ubLen b) = n" and "#bst=\<infinity>"
  shows "n \<le> (ubLen (Abs_ubundle [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(b . c_ds))\<cdot>bst)]))"
proof -
  have "(ubLen b) = #\<surd>(b . c_ds)"
    apply (simp add: ubLen_def assms(1))
    apply (rule Least_equality)
    by (simp_all add: usclLen_tstream_def)
  hence f1: "n = #\<surd>(b . c_ds)"
    using assms(2) by blast
  hence f2: "n \<le> #\<surd>((tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(b . c_ds))\<cdot>bst))"
    by (simp add: assms(3))
  show ?thesis
    apply (rule ubLen_geI)
    apply (simp add: medsr_tsb_dom ubgetch_ubrep_eq)
    by (metis f2 medsr_tsb_dom singletonD ubclDom_ubundle_def usclLen_tstream_def)
qed    
    
  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma medsr_well [simp]: assumes "#bst=\<infinity>"
  shows "ufWell (\<Lambda> x.(ubDom\<cdot>x = {c_ds})
  \<leadsto> Abs_ubundle [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)])"
  apply (rule ufun_wellI)
  by (simp_all add: domIff2 medsr_tsb_dom ubclDom_ubundle_def)
 
lemma medsr_revsubst: "Abs_cufun (medSR_TSPFAbb bst) = (medSR_TSPF bst)"
  by (simp add: medSR_TSPF_def)
    
lemma medsr_tspfdom: assumes "#bst =\<infinity>"
  shows "ufDom\<cdot>(medSR_TSPF bst) = {c_ds}"
    apply (simp add: medSR_TSPF_def)
    apply (simp add: ufdom_insert assms ubclDom_ubundle_def)
  apply (simp add: domIff2)
  by (meson tfl_some ubleast_ubdom)

   
lemma medsr_tspfran: assumes "#bst =\<infinity>"
  shows "ufRan\<cdot>(medSR_TSPF bst) = {c_dr}"   
    apply (simp add: medSR_TSPF_def)
    apply (simp add: ufran_least medsr_tspfdom assms)
  apply (simp add: medsr_revsubst medsr_tspfdom assms)
  apply (simp add: ubclDom_ubundle_def)
  sorry

  (* now special lemmata for TSPS instantiation *)

lemma medsr_well2 [simp]: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufWell (\<Lambda> x.(ubDom\<cdot>x = {c_ds})
  \<leadsto> Abs_ubundle [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)])"
proof -
   have "#bst = \<infinity>"
     by (simp add: med_ora_length assms(1))
   thus ?thesis
     by (simp add: medsr_tspfdom)
qed
  

lemma medsr_tspfdom2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufDom\<cdot>(medSR_TSPF bst) = {c_ds}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medsr_tspfdom)
qed
  
lemma medsr_tspfran2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufRan\<cdot>(medSR_TSPF bst) = {c_dr}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medsr_tspfran)
qed

  (* necessary for TSPS instantiation *)
lemma medsr_tsps_dom1 [simp]: "f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufDom\<cdot>f = {c_ds}"
  by (simp add: medsr_tspfdom2)

lemma medsr_tsps_dom2 [simp]: "\<exists>ora::bool stream. f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufDom\<cdot>f = {c_ds}"
  using medsr_tsps_dom1  by auto
 
lemma medsr_tsps_ran1 [simp]: "f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufRan\<cdot>f = {c_dr}"
  by (simp add: medsr_tspfran2)

lemma medsr_tsps_ran2 [simp]: "\<exists>ora::bool stream. f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufRan\<cdot>f = {c_dr}"
  using medsr_tsps_ran1 by auto
      
(* ----------------------------------------------------------------------- *)
section \<open>Component Definitions\<close>
(* ----------------------------------------------------------------------- *)
  
setup_lifting type_definition_uspec

lift_definition RCV3 :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {recvTSPF}"
  apply (simp add: inv_def)
  by (simp add: uspecWell_def)
    
lift_definition MEDSR3 :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {(medSR_TSPF:: bool stream \<Rightarrow> ('a::countable MABP tstream\<^sup>\<Omega>) ufun) ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (simp add: inv_rev_rev)
  apply (simp add: uspecWell_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)
    
lift_definition MEDRS3 :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (simp add: inv_rev_rev)                                            
  apply (simp add: uspecWell_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)
    
lift_definition SND3  :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {senderTSPF s | s. s \<in> tsSender}"
  apply (simp add: inv_rev_rev)
  apply (simp add: uspecWell_def)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  by (metis sender_tspfdom sender_tspfran)

abbreviation sendCompRecv :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" where 
"sendCompRecv \<equiv> (SND3::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<Otimes> (RCV3::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  

lemma id_consistent: "uspecIsConsistent ID"
  by (simp add: ID.rep_eq inv_def uspecIsConsistent_def)

lemma id_uspec_dom: "uspecDom (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) = ufclDom\<cdot>(id_TSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
proof (simp add: uspecDom_def)
  have "Rep_rev_uspec ABP_TSPS.ID = {id_TSPF::('a MABP tstream\<^sup>\<Omega>) ufun}"
    by (simp add: ID.rep_eq inv_rev_rev)
  then show "ufclDom\<cdot> (SOME u. (u::('a MABP tstream\<^sup>\<Omega>) ufun) \<in> Rep_rev_uspec ABP_TSPS.ID) = ufclDom\<cdot>(id_TSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
    by simp
qed

lemma medrs_consist_dom: assumes "uspecIsConsistent (MEDRS3::('a MABP tstream\<^sup>\<Omega>) ufun uspec)" and "f \<in> Rep_rev_uspec (MEDRS3::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  shows "uspecDom (MEDRS3::('a MABP tstream\<^sup>\<Omega>) ufun uspec) = ufclDom\<cdot>f"
  using uspec_dom_eq2 assms by blast

lemma medrs_rev_insert: "Rep_rev_uspec MEDRS3 = {medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  by (simp add: MEDRS3.rep_eq inv_rev_rev)

lemma medsr_rev_insert: "Rep_rev_uspec MEDSR3 = {medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  by (simp add: MEDSR3.rep_eq inv_rev_rev)
(* ----------------------------------------------------------------------- *)
section \<open>More Lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
lemma medrs3_id_parcomp_well : "uspec_parcompwell MEDRS3 ID"
  proof (cases "\<not> uspecIsConsistent (MEDRS3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
    case True
    then show ?thesis 
      apply (simp_all add: uspec_parcompwell_def)
      by (simp add: uspecIsConsistent_def)
  next
    case False
    obtain f where f_def: "f \<in> Rep_rev_uspec (MEDRS3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
      using False uspec_consist_f_ex by auto
    have f1: "\<exists> ora. f = medRS_TSPF ora"
      using f_def medrs_rev_insert by auto
    obtain ora where ora_def: "f = medRS_TSPF ora"
      using f1 by blast
    have f1: "uspecDom (MEDRS3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        = ufclDom\<cdot>((medRS_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
      using f_def ora_def uspec_dom_eq by auto
    have f2: "\<forall> f \<in> Rep_rev_uspec (MEDRS3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
        ufclDom\<cdot>f = ufclDom\<cdot>((medRS_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
      using False local.f1 medrs_consist_dom by auto
    have f3: "\<forall> f \<in> Rep_rev_uspec (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec). 
        ufclDom\<cdot>f  = ufclDom\<cdot>(id_TSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
      by (simp add: id_uspec_dom uspec_dom_eq)
    have f4: "parcomp_well ((medRS_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora) (id_TSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
      apply rule
       apply (simp add: ufCompL_def)
       apply (subst medrs_tsps_dom2)
      using f_def medrs_rev_insert ora_def apply auto[1]
       apply (subst medrs_tsps_ran2)
      using f_def medrs_rev_insert ora_def apply blast
      using id_tspf_dom id_tspf_ran Int_insert_right channel.distinct(239) apply auto[1]
       apply (subst medrs_tsps_ran2)
      using f_def medrs_rev_insert ora_def apply blast
      by (simp add: id_tspf_ran)
    show ?thesis 
      apply (simp_all add: uspec_parcompwell_def)
      apply (simp_all add: ufunclParCompWell_ufun_def)
      apply (rule, rule)
      by (metis ID.rep_eq f4 f_def insert_iff inv_rev_rev ora_def 
          ufCompL_def ufclDom_ufun_def ufclRan_ufun_def uspec_allDom uspec_ran_eq)
  qed

  (* Final lemma for general composition operator*)
lemma abp_gencomp_final: assumes "f \<in> Rep_TSPS gencompABP"
                            and "tsbDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
  oops  

abbreviation speccompABP3 :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"speccompABP3 \<equiv> uspecFeedbackComp(((SND3 \<circle> MEDSR3) \<circle> RCV3) \<circle> (MEDRS3 \<parallel> ID))"


lemma abpcomp_f_ex: assumes "f \<in> Rep_rev_uspec speccompABP3" 
  shows "\<exists> s \<in> tsSender. \<exists>ora1 ora2. #({True} \<ominus> ora1)=\<infinity> \<and>  #({True} \<ominus> ora2)=\<infinity> \<and>
    (f =  (ufunclFeedbackComp (ufunclSerComp (ufunclSerComp (ufunclSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
          (ufunclParComp (medRS_TSPF ora2) id_TSPF))))"
proof -
  have f1: "uspec_parcompwell MEDRS3 (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: medrs3_id_parcomp_well)
  have f2: "uspec_sercompwell SND3 (MEDSR3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  proof (cases "\<not> uspecIsConsistent (MEDSR3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
    case True
    then show ?thesis 
      apply (simp_all add: uspec_sercompwell_def)
      by (simp add: uspecIsConsistent_def)
  next
    case False
    then show ?thesis 
    proof (cases "\<not> uspecIsConsistent (SND3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
      case True
      then show ?thesis 
        apply (simp_all add: uspec_sercompwell_def)
        by (simp add: uspecIsConsistent_def)
    next
      case False
      obtain f where f_def: "f \<in> Rep_rev_uspec (MEDSR3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        by (metis assms not_uspec_consisten_empty_eq uspec_consist_f_ex 
            uspec_feedbackcomp_consistent_iff uspec_sercomp_consistent2 uspec_sercompwell_def)
      obtain g where g_def: "g \<in> Rep_rev_uspec (SND3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using False uspec_consist_f_ex by auto
      have f0: "\<exists> ora. f = medSR_TSPF ora"
      proof -
        have "{u. \<exists>s. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = medSR_TSPF s \<and> #({True} \<ominus> s) = \<infinity>} = Rep_rev_uspec MEDSR3"
          by (simp add: MEDSR3.rep_eq inv_rev_rev)
        then show ?thesis
          using f_def by fastforce
      qed
      obtain ora where ora_def: "f = medSR_TSPF ora"
        using f0 by auto
      have f01: "\<exists> s. g = senderTSPF s"
      proof -
        have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND3"
          by (simp add: SND3.rep_eq inv_rev_rev)
        then have "\<exists>c. g = senderTSPF c \<and> c \<in> tsSender"
          using g_def by blast
        then show ?thesis
          by metis
      qed
      obtain snd where snd_def: "g = senderTSPF snd"
        using f01 by auto
      have f1: "uspecDom (MEDSR3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
          = ufclDom\<cdot>((medSR_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
        using f_def ora_def uspec_dom_eq by blast
      have f2: "\<forall> f \<in> Rep_rev_uspec (MEDSR3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
          ufclDom\<cdot>f = ufclDom\<cdot>((medSR_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
        by (simp add: f1 uspec_dom_eq)
      have f3: "uspecDom (SND3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
          = ufclDom\<cdot>(senderTSPF snd)"
        using g_def local.snd_def uspec_dom_eq by blast
      have f4: "\<forall> f \<in> Rep_rev_uspec (SND3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
          ufclDom\<cdot>f = ufclDom\<cdot>(senderTSPF snd)"
        using f3 uspec_dom_eq by blast
      have f5: "sercomp_well (senderTSPF snd) (medSR_TSPF ora)"
        apply rule
        apply (subst medsr_tsps_dom2)
        using f_def medsr_rev_insert ora_def apply blast
         apply (simp_all add: sender_tspfran sender_tspfdom)
        apply (subst medsr_tsps_dom2)
        using f_def medsr_rev_insert ora_def apply blast
        apply (subst medsr_tsps_ran2)
        using f_def medsr_rev_insert ora_def apply blast
         apply simp
        apply (subst medsr_tsps_ran2)
        using f_def medsr_rev_insert ora_def apply blast
        apply (subst medsr_tsps_ran2)
        using f_def medsr_rev_insert ora_def apply blast
        by simp
      then show ?thesis 
        apply (simp add: uspec_sercompwell_def)
        apply (simp add: ufunclSerCompWell_ufun_def)
        apply (rule, rule)
        by (metis f1 f3 f_def g_def local.snd_def ora_def ufclDom_ufun_def ufclRan_ufun_def 
            uspec_dom_eq uspec_ran_eq)
    qed
  qed
  have f20: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND3:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)) \<and> f2\<in>(Rep_rev_uspec MEDSR3)}"
    by (simp add: f2)
  have f21: "uspecSerComp SND3 MEDSR3 = Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec SND3) \<and> f2\<in>(Rep_rev_uspec MEDSR3)}"
    by (simp add: uspecSerComp_def)
  have f3: "uspec_sercompwell (SND3 \<circle> MEDSR3) RCV3"
    sorry
  have f30: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND3 \<circle> MEDSR3)) \<and> f2\<in>(Rep_rev_uspec RCV3)}"
    by (simp add: f3)
  have f31: "uspecSerComp (SND3 \<circle> MEDSR3) RCV3 = 
      Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND3 \<circle> MEDSR3)) \<and> f2\<in>(Rep_rev_uspec RCV3)}"
    using uspecSerComp_def by blast
  have f4: "uspec_parcompwell MEDRS3 ID"
    sorry
  have f40: "uspecWell {ufunclParComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec MEDRS3) \<and> f2\<in>(Rep_rev_uspec ID)}"
    by (simp add: f4)
  have f31: "uspecParComp MEDRS3 ID = 
      Abs_rev_uspec {ufunclParComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec MEDRS3) \<and> f2\<in>(Rep_rev_uspec ID)}"
    using uspecParComp_def by blast
  have f5: "uspec_sercompwell ((SND3 \<circle> MEDSR3) \<circle> RCV3) (MEDRS3 \<parallel> ID)"
    sorry
  have f50: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec ((SND3 \<circle> MEDSR3) \<circle> RCV3)) 
      \<and> f2\<in>(Rep_rev_uspec (MEDRS3 \<parallel> ID))}"
    by (simp add: f5)
  have f51: "uspecSerComp ((SND3 \<circle> MEDSR3) \<circle> RCV3) (MEDRS3 \<parallel> ID) = 
      Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec ((SND3 \<circle> MEDSR3) \<circle> RCV3)) 
      \<and> f2\<in>(Rep_rev_uspec (MEDRS3 \<parallel> ID))}"
    using uspecSerComp_def by blast
  have f60: "uspecWell {(\<mu>) f1 |f1::('a MABP tstream\<^sup>\<Omega>) ufun. f1 \<in> Rep_rev_uspec (SND3 \<circle> MEDSR3 \<circle> RCV3 \<circle> (MEDRS3 \<parallel> ABP_TSPS.ID))}"
    by (simp add: uspec_feedbackcomp_well)
  have f61: "uspecFeedbackComp(((SND3 \<circle> MEDSR3) \<circle> RCV3) \<circle> (MEDRS3 \<parallel> ID)) =
    Abs_rev_uspec {(\<mu>) f1 |f1::('a MABP tstream\<^sup>\<Omega>) ufun. f1 \<in> Rep_rev_uspec (SND3 \<circle> MEDSR3 \<circle> RCV3 \<circle> (MEDRS3 \<parallel> ABP_TSPS.ID))}"
    by (simp add: uspecFeedbackComp_def)                                                            
  have f70: "f \<in> {(\<mu>) f1 |f1::('a MABP tstream\<^sup>\<Omega>) ufun. f1 \<in> Rep_rev_uspec (SND3 \<circle> MEDSR3 \<circle> RCV3 \<circle> (MEDRS3 \<parallel> ABP_TSPS.ID))} "
    by (metis (no_types, lifting) assms f60 f61 rep_abs_rev_simp)
  have f71: "uspecIsConsistent (speccompABP3::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    apply (simp add: uspecIsConsistent_def uspecFeedbackComp_def)
    apply (subst rep_abs_rev_simp, simp add: uspec_feedbackcomp_well)
    using f70 by blast
  have f80: "uspecIsConsistent (((SND3 \<circle> MEDSR3 \<circle> RCV3)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<circle> (MEDRS3 \<parallel> ABP_TSPS.ID))"
    using f71 uspec_feedbackcomp_consistent_iff by auto
  have f90: "uspecIsConsistent ((SND3 \<circle> MEDSR3 \<circle> RCV3)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        \<and> uspecIsConsistent ((MEDRS3 \<parallel> ABP_TSPS.ID)::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    using f51 f80 uspec_sercomp_consistent2 f5 by blast
  have f91: "uspecIsConsistent (MEDRS3:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec) 
        \<and> uspecIsConsistent (ID:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f31 f4 uspec_parcomp_consistent2 f90 by blast
  have f92: "uspecIsConsistent ((SND3 \<circle> MEDSR3)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        \<and> uspecIsConsistent (RCV3:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f31 f3 uspec_sercomp_consistent2 f90 by blast
  have f93: "uspecIsConsistent (SND3:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec) 
        \<and> uspecIsConsistent (MEDSR3:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f2 f92 uspec_sercomp_consistent2 by blast
  show ?thesis
    sorry
qed
      
end