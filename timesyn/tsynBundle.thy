(*  Title:        tsynBundle.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous stream bundles.
*)

chapter {* Time-Synchronous Stream Bundles *}

theory tsynBundle
imports tsynStream "../untimed/SB" "../UFun_Templates"

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
  by (simp add: assms sbRt_def usclConc_stream_def)+

(* ----------------------------------------------------------------------- *)
  section {* Definitions on Time-Synchronous Bundles *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynbRemDups} removes all duplicates of the time-synchronous stream on channel c1. 
        The resulting stream is on channel c2. *}
definition tsynbRemDups :: "'a tsyn stream ubundle \<rightarrow> 'a tsyn stream ubundle option" where 
  "tsynbRemDups \<equiv> \<Lambda> sb. (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)]"

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Bundles *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynbRemDups *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynbRemDups} is monotonic. *}
lemma tsynbremdups_mono [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "monofun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                    \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)])"
  apply (rule uf_1x1_mono)
  by (simp add: assms map_io_well_def)

text {* @{term tsynbRemDups} is continous. *}
lemma tsynbremdups_cont [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "cont (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                  \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)])"
  apply (rule uf_1x1_cont)
  by (simp add: assms map_io_well_def)

text {* @{term tsynbRemDups} insertion lemma. *}
lemma tsynbremdups_insert:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "tsynbRemDups\<cdot>(sb ::'a tsyn stream\<^sup>\<Omega>) 
           = (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)]"
  by (simp add: assms tsynbRemDups_def)

text {* @{term tsynbRemDups} satisfies well condition for universal functions. *}
lemma tsynbremdups_ufwell [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufWell (Abs_cfun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                             \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)])))"
  apply (rule uf_1x1_well)
  by (simp add: assms map_io_well_def)

text {* Domain of @{term tsynbRemDups} is {c1}. *}
lemma tsynbremdups_ufdom:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufDom\<cdot>(Abs_cufun (\<lambda> sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                              \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)]))) = {c1}"
  apply (rule uf_1x1_dom)
  by (simp add: assms map_io_well_def)

text {* Range of @{term tsynbRemDups} is {c2}. *}
lemma tsynbremdups_ufran [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufRan\<cdot>(Abs_cufun (\<lambda> sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                              \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)]))) = {c2}"
  apply (rule uf_1x1_ran)
  by (simp add: assms map_io_well_def)

text {* Domain of the @{term tsynbRemDups} output bundle is {c2}. *}
lemma tsynbremdups_ubdom:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
    and "c1 \<in> ubDom\<cdot>sb"
  shows "ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>((sb :: 'a tsyn stream ubundle)  .  c1)]) = {c2}"
  using assms
  by (metis (full_types) dom_eq_singleton_conv fun_upd_upd ubclDom_ubundle_def ubdom_channel_usokay
      ubdom_insert ubdom_ubrep_eq ubgetch_insert ubsetch_well ubundle_ex)

text {* @{term tsynbRemDups} is strict.*}
lemma tsynbremdups_strict [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "tsynbRemDups\<cdot>(ubLeast {c1} :: 'a tsyn stream ubundle) = Some (ubLeast {c2})"
  proof -
    have "ubDom\<cdot>(ubLeast {c1}) = {c1}" 
      by simp
    hence insert_bundle: 
      "tsynbRemDups\<cdot>(ubLeast {c1} ::'a tsyn stream ubundle) 
         = Some (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(ubLeast {c1} . c1)])"
      by (simp add: assms tsynbremdups_insert)
    have "tsynRemDups\<cdot>(ubLeast {c1} . c1) = \<epsilon>" by (simp add: ubdom_insert)
    hence "Some (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(ubLeast {c1} . c1)]) 
             = Some (Abs_ubundle [c2 \<mapsto> \<epsilon>])" by simp
    have "Abs_ubundle [c2 \<mapsto> \<epsilon>] = Abs_ubundle (\<lambda>c. (c \<in> {c2}) \<leadsto> \<epsilon>)" 
      by (metis (full_types) fun_upd_apply fun_upd_same insertI1 singletonD)
    hence "Abs_ubundle [c2 \<mapsto> \<epsilon>] = ubLeast {c2}" 
      by (simp add: ubLeast_def)
    hence "Some (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(ubLeast {c1} . c1)]) 
             = Some (ubLeast {c2})" by simp
    then show ?thesis
      by (simp add: insert_bundle)
  qed
    
end