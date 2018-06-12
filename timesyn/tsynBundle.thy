(*  Title:        tsynBundle.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous stream bundles.
*)

chapter {* Time-Synchronous Stream Bundles *}

theory tsynBundle
imports tsynStream "../untimed/SB"

begin

default_sort message

(* ----------------------------------------------------------------------- *)
  section {* tsynbNull - Automaton *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lift_definition tsynbNull :: "channel \<Rightarrow> 'm tsyn SB" is
  "\<lambda>c. [c \<mapsto> \<up>null]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
    
definition tsynbAbs :: "'a tsyn stream ubundle \<rightarrow> 'a stream ubundle option" where 
  "tsynbAbs  \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle[c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"

lemma tsynbnull_ubdom [simp]: "ubDom\<cdot>(tsynbNull c) = {c}"
  by (simp add:tsynbNull.rep_eq ubdom_insert)

lemma tsynbnull_ubgetch [simp]: "tsynbNull c  .  c = \<up>null"
  by (simp add: tsynbNull.rep_eq ubgetch_insert)

lemma tsynbnull_ubconc [simp]:
  assumes "c \<in> ubDom\<cdot>sb"
  shows "ubConc (tsynbNull c)\<cdot>sb  .  c = \<up>null \<bullet> (sb  .  c)"
  by (simp add: assms ubConc_usclConc_eq usclConc_stream_def)
    
lemma tsynbnull_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {c}"
  shows "sbRt\<cdot>(ubConc (tsynbNull c)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: assms sbRt_def)+
   
instantiation nat :: message 
begin
  fun ctype_nat :: "channel \<Rightarrow> nat set" where 
  "ctype_nat c = range nat" 

  instance
  by(intro_classes)
end
 
lift_definition sbun :: "nat stream ubundle " is "[c2 \<mapsto> <[(1::nat),2,1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def)
  by (metis nat_1 nat_2 numeral_2_eq_2 range_eqI)  
    
lift_definition tsynbun :: "nat tsyn stream ubundle " is "[c1 \<mapsto> <[Msg (1::nat), null, Msg 2, Msg 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
  by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)
  
lemma conttsynbabs:
 "cont(\<lambda> sb. (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle[c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  apply (simp add: ubclDom_ubundle_def)
  apply(rule contI2)
  apply(rule monofunI)
  apply (simp add: below_option_def)
  sorry
    
lemma nbhj:"ubWell([c1 \<mapsto> \<up>(\<M> Suc (0::nat)) \<bullet> \<up>- \<bullet> \<up>(\<M> 2::nat) \<bullet> \<up>(\<M> Suc (0::nat))])"
  apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
  by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)
    
lemma kk:"ubclDom\<cdot>(Abs_ubundle [c1 \<mapsto> \<up>(\<M> Suc (0::nat)) \<bullet> \<up>- \<bullet> \<up>(\<M> 2::nat) \<bullet> \<up>(\<M> Suc (0::nat))]) = {c1}"
  apply(simp add: ubclDom_ubundle_def)
  by(simp add:ubdom_ubrep_eq nbhj)
 
lemma tsynrec_test_finstream:
  "tsynbAbs\<cdot>(tsynbun) = Some(sbun)"
  apply(simp add: tsynbAbs_def tsynbun_def sbun_def)
  apply(simp add: conttsynbabs)
  apply(simp add: kk)
  by(simp add: ubgetch_ubrep_eq nbhj tsynabs_insert)
  
    
end