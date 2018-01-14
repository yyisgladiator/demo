(*  Title:        SPF
    Author:       Sebastian Stüber
    Author:       Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Defines "Stream Processing Functions"
*)

theory SPF
imports SB "../UBundle" "../UFun" "../UFun_Comp"

begin
  
  default_sort message 


(* ----------------------------------------------------------------------- *)
  section \<open>Definitions on 'm SPF's\<close>
(* ----------------------------------------------------------------------- *)

(* Should be ported from SPF_Templates
subsection \<open>spfLift\<close>
  (* example for SPF instantiations can also be found in SPF_Templates *)

text {* "spflift" takes a "simple stream processing function" and two channel 
         names where the streams flow, and lifts it to a stream bundle processing function.*}
definition spfLift :: "('m stream \<rightarrow> 'm stream) => channel => channel => ('m stream\<^sup>\<Omega>, 'm stream\<^sup>\<Omega>) ufun" where
"spfLift f ch1 ch2  \<equiv> Abs_cufun (\<lambda>b. ( (b\<in>{sb . (ubDom\<cdot>sb = {ch1})}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(b . ch1)])))" 

(* takes a fully defined 'm SPF-function and changes it to an 
    'm SPF with given In & Out channels *)
definition spfSbLift:: "('m stream\<^sup>\<Omega> \<rightarrow> 'm stream\<^sup>\<Omega>) \<Rightarrow> channel set \<Rightarrow> channel set \<Rightarrow> ('m stream\<^sup>\<Omega>,'m stream\<^sup>\<Omega>) ufun" where
"spfSbLift f In Out \<equiv> Abs_cufun (\<lambda>b. (ubDom\<cdot>b = In) \<leadsto> ((f\<cdot>b) \<bar> Out))"
*)

subsection \<open>hide\<close>

(* Hide has to be ported to Universal
definition hide :: "('m stream\<^sup>\<Omega>,'m stream\<^sup>\<Omega>) ufun \<Rightarrow>  channel set \<Rightarrow> ('m stream\<^sup>\<Omega>,'m stream\<^sup>\<Omega>) ufun" ("_\<h>_") where
"hide f cs \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(ufRan\<cdot>f - cs)))"
*)

(* ----------------------------------------------------------------------- *)
  section \<open>Lemmas on 'm SPF's\<close>
(* ----------------------------------------------------------------------- *)


(* Shpuld be ported from SPF_Templates
  subsection \<open>spfSbLift\<close>

(* continuity of spfSbLift is allready in simp *)
  (* I define it nevertheless, to be used by sledgi *)
lemma spfsblift_cont[simp]: "cont (\<lambda>b. (ubDom\<cdot>b=In) \<leadsto> ((f\<cdot>b) \<bar> Out))"
  by simp

(* the function produced by spfSbLift is wellformed *)
lemma spfsblift_well[simp]: "ufWell  (\<Lambda> b. (ubDom\<cdot>b=In) \<leadsto> ((f\<cdot>b) \<bar> Out))"
  by (rule ubeqcommon_id)


lemma spfsblift_sbdom[simp]: "ufDom\<cdot>(spfSbLift F In Out) = In"
  by (rule ubeqcommon_id)

lemma if_then_ran:
  assumes "d \<in> ran (\<lambda>b. (P b)\<leadsto>(((F b))\<bar> Out))"
  shows "ubDom\<cdot>d = Out" 
  by (rule ubeqcommon_id)

lemma spfsblift_dom [simp]: "(\<exists> d. (d \<in> (dom (\<lambda>b::('a::uscl_pcpo)\<^sup>\<Omega>. (ubDom\<cdot>b = In)\<leadsto>(((F\<cdot>b))\<bar>Out)))))"
  proof
  show "(ubLeast In) \<in> (dom (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>(((F\<cdot>b))\<bar>Out)))" by auto
qed

*)

(* Hide has to be ported to Universal
subsection \<open>hide\<close>  
  
lemma hide_cont[simp]:  
  shows "cont (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(ufRan\<cdot>f - cs)))"
  apply(subst if_then_cont, simp_all)
  by (simp add: cont_compose)

lemma hidespfwell_helper: assumes "ubDom\<cdot>b = ufDom\<cdot>f" shows "ubDom\<cdot>(f\<rightleftharpoons>b) = ufRan\<cdot>f"
  by (metis assms ubDom_ubundle_def ufran_2_ubdom2)

lemma hide_spfwell[simp]: "ufWell ((\<Lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(ufRan\<cdot>f - cs))))"
  by (rule ubeqcommon_id)


lemma spfDomHide: "ufDom\<cdot>(f \<h> cs) = ufDom\<cdot>f"
  by (rule ubeqcommon_id)


(*
  apply(simp add: ufun_ufdom_abs hide_cont hide_spfwell) *)

lemma hideSbRestrict: assumes "ubDom\<cdot>sb = ufDom\<cdot>f" 
   shows "(hide f cs)\<rightleftharpoons>sb = (f\<rightleftharpoons>sb)\<bar>(ufRan\<cdot>f - cs)"
  apply(simp add: hide_def)
  by (simp add: assms)

lemma hideSbRestrictCh: assumes "ubDom\<cdot>sb = ufDom\<cdot>f" and "c \<notin> cs"
   shows "((hide f cs)\<rightleftharpoons>sb) . c = (f\<rightleftharpoons>sb) . c"
  apply(simp add: hide_def)
  apply(simp add: assms) 
  by (metis (no_types, lifting) Diff_iff IntE assms(1) assms(2) domIff sbrestrict2sbgetch ubDom_ubundle_def ubdom_insert ubgetch_insert ubrestrict_dom ufran_2_ubdom2)
   
lemma hideSpfRan: "ufRan\<cdot>(hide f cs) = ufRan\<cdot>f - cs"
by (rule ubeqcommon_id)


lemma hideSubset: "ufRan\<cdot>(hide f cs) \<subseteq> ufRan\<cdot>f"
  using hideSpfRan by auto  
*)  

end