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
  section {* tsynNullSB - Automaton *}
(* ----------------------------------------------------------------------- *)

lift_definition tsynNullSB :: "channel \<Rightarrow> 'm tsyn SB" is
  "\<lambda>c. [c \<mapsto> \<up>null]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)

lemma tsynnullsb_ubdom [simp]: "ubDom\<cdot>(tsynNullSB c) = {c}"
  by (simp add: tsynNullSB.rep_eq ubdom_insert)

lemma tsynnullsb_ubgetch [simp]: "tsynNullSB c  .  c = \<up>null"
  by (simp add: tsynNullSB.rep_eq ubgetch_insert)

lemma tsynnullsb_ubconc [simp]: 
  assumes "c \<in> ubDom\<cdot>sb" 
  shows "ubConc (tsynNullSB c)\<cdot>sb  .  c = \<up>null \<bullet> (sb  .  c)"
  by (simp add: assms ubConc_usclConc_eq usclConc_stream_def)
    
lemma tsynnullsb_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {c}"
  shows "sbRt\<cdot>(ubConc (tsynNullSB c)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: assms sbRt_def)+



    
end