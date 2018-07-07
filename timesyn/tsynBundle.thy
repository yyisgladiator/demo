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



text {* Function @{term tsynbRemDups} removes all duplicates of the time synchronous stream
        in channel c1. The resulting stream is on channel c2. *}
definition tsynbRemDups :: "'a tsyn stream ubundle \<rightarrow> 'a tsyn stream ubundle option" where 
  "tsynbRemDups \<equiv> \<Lambda> sb. (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)]"


text {* Function @{term tsynbRemDups} is monotonic.*}
lemma tsynbRemDups_mono [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "monofun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                    \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)])"
  apply (rule uf_1x1_mono)
  by (simp add: assms map_io_well_def)


text {* Function @{term tsynbRemDups} is continous.*}
lemma tsynbRemDups_cont [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "cont (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                    \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)])"
  apply (rule uf_1x1_cont)
  by (simp add: assms map_io_well_def)

text {* Insertion Lemma for function @{term tsynbRemDups}*}
lemma tsynbRemDups_insert:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "tsynbRemDups\<cdot>(sb ::'a tsyn stream\<^sup>\<Omega>) 
           = (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb  .  c1)]"
  by (simp add: assms tsynbRemDups_def)


lemma tsynbRemDups_ufwell [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufWell (Abs_cfun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)])))"
  apply (rule uf_1x1_well)
  by (simp add: assms map_io_well_def)

lemma tsynbRemDups_ufdom [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufDom\<cdot>(Abs_cufun(\<lambda> sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)]))) = {c1}"
  apply (rule uf_1x1_dom)
  by (simp add: assms map_io_well_def)

lemma tsynbRemDups_ufran [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufRan\<cdot>(Abs_cufun(\<lambda> sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)]))) = {c2}"
  apply (rule uf_1x1_ran)
  by (simp add: assms map_io_well_def)

lemma tsynbRemDups_ubdom:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
    and "c1 \<in> ubDom\<cdot>sb"
  shows "ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>((sb :: 'a tsyn stream ubundle)  .  c1)]) = {c2}"
  using assms
  by (metis (full_types) dom_eq_singleton_conv fun_upd_upd ubclDom_ubundle_def ubdom_channel_usokay
      ubdom_insert ubdom_ubrep_eq ubgetch_insert ubsetch_well ubundle_ex)

lemma tsynbRemDups_strict:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "tsynbRemDups\<cdot>((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle) 
         = Some ((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle)"
proof -
  have 1:"tsynbRemDups\<cdot>((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle )
        = (ubDom\<cdot>((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle) = {c1}) 
           \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle) . c1)]" 
    using assms by (simp add: tsynbRemDups_insert)
  have 2:"(ubDom\<cdot>((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle)) = {c1}" sorry
  hence "(ubDom\<cdot>((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle) = {c1}) 
           \<leadsto> Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle) . c1)]
          = Some (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(((Abs_ubundle [c1 \<mapsto> \<epsilon>])::'a tsyn stream ubundle) . c1)])" by simp
 
qed
    
end