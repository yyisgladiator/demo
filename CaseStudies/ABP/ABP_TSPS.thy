(*  Title:        ABP_TSPS.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  ABP modeled with TSPS
*)

theory ABP_TSPS
  imports "../../timed/TSPS" Receiver Composition Medium "../../timed/TSPF" "../../UFun_Comp" "../../USpec_Comp"

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



instantiation ufun :: (ubcl_comp) ufuncl_comp
begin

definition ufunclComp_ufun_def: "ufunclComp \<equiv> ufComp"
definition ufunclParComp_ufun_def: "ufunclParComp \<equiv> ufParComp"
definition ufunclSerComp_ufun_def: "ufunclSerComp \<equiv> ufSerComp"
definition ufunclFeedbackComp_ufun_def:"ufunclFeedbackComp = ufFeedbackComp"

definition ufunclCompWell_ufun_def: "ufunclCompWell = comp_well"
definition ufunclSerCompWell_ufun_def: "ufunclSerCompWell = sercomp_well"
definition ufunclParCompWell_ufun_def: "ufunclParCompWell = parcomp_well"

instance
  apply intro_classes
             apply (simp add: inf_sup_aci(1) ufcomp_L_commu ufunclParCompWell_ufun_def)
            apply (simp add: inf_sup_aci(1) ufunclCompWell_ufun_def)
           apply (simp add: ufunclParComp_ufun_def ufParComp_dom ufclDom_ufun_def ufunclParCompWell_ufun_def)
          apply (simp add: ufunclParComp_ufun_def ufParComp_ran ufclRan_ufun_def ufunclParCompWell_ufun_def)
         apply (simp add: ufunclSerCompWell_ufun_def ufunclSerComp_ufun_def ufclDom_ufun_def ufclRan_ufun_def)
  using ufSerComp_dom apply auto[1]
        apply (simp add: ufunclSerCompWell_ufun_def ufunclSerComp_ufun_def ufclDom_ufun_def ufclRan_ufun_def)
  using ufSerComp_ran apply auto[1]
       apply (metis ufunclComp_ufun_def ufcomp_commu ufunclCompWell_ufun_def)
      apply (metis ufunclParComp_ufun_def ufParComp_commutativity ufunclParCompWell_ufun_def)
     apply (simp add: ufParComp_associativity ufunclParCompWell_ufun_def ufunclParComp_ufun_def)
    apply (simp add:  ufunclSerComp_ufun_def)
    apply (subst ufSerComp_asso)
       apply (meson ufunclSerCompWell_ufun_def) + 
     apply (simp add: ufclDom_ufun_def ufclRan_ufun_def, simp)
   apply (simp add: ufunclParComp_ufun_def ufParCompWell_asso ufunclParCompWell_ufun_def)
  apply (simp add: ufunclSerCompWell_ufun_def ufunclSerComp_ufun_def ufclDom_ufun_def ufclRan_ufun_def)
  by (metis (no_types, hide_lams) ufSerComp_dom ufSerComp_ran)
end





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
definition sender_TSPF :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"sender_TSPF se \<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"



subsection \<open>id\<close>


definition id_TSPF :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"id_TSPF \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_abpOut \<mapsto> x . c_abpOut])"



(* ----------------------------------------------------------------------- *)
section \<open>Components\<close>
(* ----------------------------------------------------------------------- *)


lift_definition SND :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {sender_TSPF s | s. s \<in> tsSender}"
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


definition sender_TSPF2 :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"sender_TSPF2 se \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
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
"Rev {sender_TSPF2 s | s. s \<in> tsSender}"
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
  sorry 

lemma h1: assumes "s \<in> tsSender" shows "UFun.ufDom\<cdot>(ufunclSerComp (sender_TSPF2 s) recvTSPF2) = {c_abpIn, c_ar}"
  sorry                                                              

lemma h2: assumes "s \<in> tsSender" shows "UFun.ufRan\<cdot>(ufunclSerComp (sender_TSPF2 s) recvTSPF2) = {c_abpOut, c_ar}"
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
  have f1: "\<exists> s \<in> tsSender. (f = (\<mu>(ufunclSerComp (sender_TSPF2 s) recvTSPF2)))"
    (* Cannot be proven until Instatiation *)
    sorry
  then obtain s where f12: "s \<in> tsSender \<and> (f = (\<mu>(ufunclSerComp (sender_TSPF2 s) recvTSPF2)))"
    by blast
  then have f13: "f = (\<mu>(ufunclSerComp (sender_TSPF2 s) recvTSPF2))"
    by blast
  have f14: "s \<in> tsSender"
    using f12 by blast


  have f20: "ubclDom\<cdot>tb = {c_abpIn, c_ar} - {c_ar}"
    apply(simp add: ubclDom_ubundle_def)
    using assms by blast                    
  have f2: "(f \<rightleftharpoons> tb) . c_abpOut =  ubFix (ufFeedH (ufunclSerComp (sender_TSPF2 s) recvTSPF2) tb) {c_abpOut, c_ar}  .  c_abpOut"
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
  have f4: "ubFix (ufFeedH (ufunclSerComp (sender_TSPF2 s) recvTSPF2) tb) {c_abpOut, c_ar}  .  c_abpOut
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
  by (metis ctype_MABP.simps(2) ctype_MABP.simps(6) tsmap_tsdom_range usclOkay_tstream_def)

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

 (* show that the recvTSPF fulfills the tickcount property *)
lemma recvTSPF_tick: assumes "ubDom\<cdot>b = {c_dr}" and "(ubLen b) = n"
  shows "n \<le> (ubLen (Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))),
                       c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr))))])))"
proof -
  have "(ubLen b) = usclLen\<cdot>(b . c_dr)"
  proof (simp add: ubLen_def)
    have "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b} \<or> ubDom\<cdot>b = {}"
      using ublen_least_in_set by blast
    then have "{c_dr} = {} \<or> (\<exists>c. (LEAST l. \<exists>c. l = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b) = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b)"
      by (simp add: assms(1))
    then show "(ubDom\<cdot>b \<noteq> {} \<longrightarrow> (LEAST l. \<exists>c. l = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b) = usclLen\<cdot>(b . c_dr)) \<and> (ubDom\<cdot>b = {} \<longrightarrow> \<infinity> = usclLen\<cdot>(b . c_dr))"
      by (simp add: assms(1))
  qed
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

(*
  subsection \<open>medium_rs\<close>

(*

definition tsMedRSTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedRSTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {c_ar})
                           \<leadsto> [c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]\<Omega>)"

abbreviation tsMedRSAbb  :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP TSB option" where
"tsMedRSAbb bst x \<equiv> ((tsbDom\<cdot>x = {c_ar})
                           \<leadsto> [c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]\<Omega>)"

*)
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

definition medSRH :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP tstream"  where
"medSRH bst \<equiv> (\<lambda> x. (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst))"

lemma medsrh_cont [simp]: "cont (medSRH bst)"
  by (simp add: medSRH_def)

lemma medsrh_contlub: assumes "chain Y"
  shows "(medSRH bst) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medSRH bst) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medsrh: "tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_ds))\<cdot>bst)
                  = ((medSRH :: bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP tstream) bst) x"
  by (simp add: medSRH_def)

subsubsection \<open>pre\<close>
(*
lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast
*)

lemma medsr_tsb_well[simp]: "tsb_well [c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]"
  apply (rule tsb_wellI)
  by (simp add: tsmap_tsdom_range)

lemma medsr_tsb_dom: "tsbDom\<cdot>([c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>) = {c_dr}"
  by (simp add: tsbdom_rep_eq)
    
  subsubsection \<open>cont\<close>
    
(* definition tsMedSRTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedSRTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)" *)

(* this can be shown analogue to before *)
lemma medsr_cont [simp]: "cont (\<lambda> x::'a MABP TSB. (tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)"
  sorry
    
 
  subsubsection \<open>tspf_well\<close>

lemma medsr_tick: assumes "tsbDom\<cdot>b = {c_ds}" and "(#\<surd>tsb b) = n" and "#bst=\<infinity>"
  shows "n \<le> (#\<surd>tsb [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(b . c_ds))\<cdot>bst)]\<Omega>)"
proof -
  have "(#\<surd>tsb b) = #\<surd>(b . c_ds)"
    apply (rule tsbtick_single_ch2)
    by (simp add: assms(1))
  hence f1: "n = #\<surd>(b . c_ds)"
    using assms(2) by blast
  hence f2: "n \<le> #\<surd>((tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(b . c_ds))\<cdot>bst))"
    by (simp add: assms(3))
  show ?thesis
    apply (rule tsbtick_geI)
    apply (simp add: medsr_tsb_dom tsbgetch_rep_eq)
    using f2 by force
qed    
    
  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma medsr_well [simp]: assumes "#bst=\<infinity>"
  shows "tspf_well (\<Lambda> x.(tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)"
  apply (rule tspf_wellI)
    apply (simp_all add: domIff2 medsr_tsb_dom)
    apply (subst tsbtick_single_ch1, simp)
    by (simp add: assms tsbtick_single_ch2)    
 
lemma medsr_revsubst: "Abs_CTSPF (medSR_TSPFAbb bst) = (medSR_TSPF bst)"
  by (simp add: medSR_TSPF_def)
    
lemma medsr_tspfdom: assumes "#bst =\<infinity>"
  shows "tspfDom\<cdot>(medSR_TSPF bst) = {c_ds}"
    apply (simp add: medSR_TSPF_def)
    apply (simp add: tspf_dom_insert assms)
    apply (simp add: domIff2)
    by (meson tsbleast_tsdom someI)
   
lemma medsr_tspfran: assumes "#bst =\<infinity>"
  shows "tspfRan\<cdot>(medSR_TSPF bst) = {c_dr}"   
    apply (simp add: medSR_TSPF_def)
    apply (simp add: tspfran_least medsr_tspfdom assms)
    apply (simp add: medsr_revsubst medsr_tspfdom assms)
    by (metis singletonI tsb_newMap_id tsbleast_getch tsbleast_tsdom)

  (* now special lemmata for TSPS instantiation *)

lemma medsr_well2 [simp]: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "tspf_well (\<Lambda> x.(tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)"
proof -
   have "#bst = \<infinity>"
     by (simp add: med_ora_length assms(1))
   thus ?thesis
     by (simp add: medsr_tspfdom)
qed
  

lemma medsr_tspfdom2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "tspfDom\<cdot>(medSR_TSPF bst) = {c_ds}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medsr_tspfdom)
qed
  
lemma medsr_tspfran2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "tspfRan\<cdot>(medSR_TSPF bst) = {c_dr}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medsr_tspfran)
qed

  (* necessary for TSPS instantiation *)
lemma medsr_tsps_dom1 [simp]: "f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> tspfDom\<cdot>f = {c_ds}"
  by (simp add: medsr_tspfdom2)

lemma medsr_tsps_dom2 [simp]: "\<exists>ora::bool stream. f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> tspfDom\<cdot>f = {c_ds}"
  using medsr_tsps_dom1  by auto
 
lemma medsr_tsps_ran1 [simp]: "f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> tspfRan\<cdot>f = {c_dr}"
  by (simp add: medsr_tspfran2)

lemma medsr_tsps_ran2 [simp]: "\<exists>ora::bool stream. f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> tspfRan\<cdot>f = {c_dr}"
  using medsr_tsps_ran1 by auto
      
(* ----------------------------------------------------------------------- *)
section \<open>Component Definitions\<close>
(* ----------------------------------------------------------------------- *)
  
lift_definition RCV :: "('a MABP tstream\<^sup>\<Omega> , 'a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {recvTSPF}"
  apply (simp add: inv_def)
  by (simp add: uspecWell_def)
    
lift_definition MEDSR :: "'a MABP TSPS" is "{medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (rule tsps_wellI)
   by (simp_all)
    
lift_definition MEDRS :: "'a MABP TSPS" is "{medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (rule tsps_wellI)
   by (simp_all) (* proof uses the special medrs_tsps lemmata *)
    
lift_definition SND  :: "'a MABP TSPS" is "{sender_TSPF s | s. s \<in> tsSender}"
  apply (rule tsps_wellI)
   apply (simp_all)
    (* instantiation analogue to MEDRS *)
    sorry

abbreviation sendCompRecv :: "'a MABP TSPS" where 
"sendCompRecv \<equiv> (SND::'a MABP TSPS) \<Otimes> (RCV::'a MABP TSPS)"
  
      
abbreviation gencompABP :: "'a MABP TSPS" where
"gencompABP \<equiv> ((SND \<Otimes> MEDSR) \<Otimes> RCV) \<Otimes> MEDRS"
  
  

(* ----------------------------------------------------------------------- *)
section \<open>More Lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
  (* Final lemma for general composition operator*)
lemma abp_gencomp_final: assumes "f \<in> Rep_TSPS gencompABP"
                            and "tsbDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
  oops                          
      

*)