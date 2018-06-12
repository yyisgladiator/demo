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

(* ----------------------------------------------------------------------- *)
  section {* Definitions on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)

definition tsynbAbs :: "'a tsyn stream ubundle \<rightarrow> 'a stream ubundle option" where 
  "tsynbAbs  \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"

(* ----------------------------------------------------------------------- *)
  section {* Definitions of Time-Synchronous Test Bundles *}
(* ----------------------------------------------------------------------- *)

instantiation nat :: message
begin
  fun ctype_nat :: "channel \<Rightarrow> nat set" where 
  "ctype_nat c = range nat" 
  instance
    by (intro_classes)
end
 
lift_definition tsynbabs_test_input :: "nat tsyn stream ubundle " is 
  "[c1 \<mapsto> <[Msg (1 :: nat), null, Msg 2, Msg 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
  by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)

lift_definition tsynbabs_test_output :: "nat stream ubundle " is 
  "[c2 \<mapsto> <[(1 :: nat), 2, 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def)
  by (metis nat_1 nat_2 numeral_2_eq_2 range_eqI)

lemma tsynbabs_test_input_ubdom: "ubDom\<cdot>tsynbabs_test_input = {c1}"
  sorry

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)

lemma tsynbabs_mono:
  "monofun (\<lambda> sb. (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  sorry

lemma tsynbabs_cont:
  "cont (\<lambda> sb. (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  apply (simp add: ubclDom_ubundle_def)
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: tsynbabs_mono)
  sorry

lemma tsynbabs_insert: 
  "tsynbAbs\<cdot>sb = (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"
  sorry
    
lemma tsynbabs_test_finstream:
  "tsynbAbs\<cdot>(tsynbabs_test_input) = Some (tsynbabs_test_output)"
  apply (simp add: tsynbabs_insert ubclDom_ubundle_def tsynbabs_test_input_ubdom)
  apply (simp only: tsynbabs_test_input_def tsynbabs_test_output_def)
  apply (subst ubgetch_ubrep_eq)
  apply (metis tsynbabs_test_input.rep_eq ubrep_well)
  by (simp add: tsynbabs_insert tsynabs_insert)
    
end