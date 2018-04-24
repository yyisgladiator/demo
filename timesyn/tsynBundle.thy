theory tsynBundle

imports tsynStream "../untimed/SB"

begin

default_sort message


lift_definition tsynbOneTick:: "channel \<Rightarrow> 'm event SB" is
"\<lambda>c. [c \<mapsto> \<up>Tick]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_event_def
  by simp



lemma tsynbonetick_dom [simp]: "ubDom\<cdot>(tsynbOneTick c) = {c}"
  by (simp add: tsynbOneTick.rep_eq ubdom_insert)

lemma tsynbonetick_ubgetch[simp]: "tsynbOneTick c  .  c = \<up>Tick"
  by (metis fun_upd_same option.sel tsynbOneTick.rep_eq ubgetch_insert)

lemma tsynbonetick_ubconc_tick[simp]:assumes "c \<in> ubDom\<cdot>sb" 
  shows "ubConc (tsynbOneTick c)\<cdot>sb  .  c = \<up>\<surd> \<bullet> (sb .c)"
  apply (simp only: ubConc_def)
  apply (simp only:  Abs_cfun_inverse2 ubconc_cont)
  apply (simp add: ubgetch_ubrep_eq)
  by (simp add: assms usclConc_stream_def)
    
lemma sbrt_ubconc_dom[simp]:assumes "ubDom\<cdot>sb = {c}" 
  shows "sbRt\<cdot>(ubConc (tsynbOneTick c)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: sbRt_def assms) +
    
end