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

lemma tsynbonetick_ubgetch[simp]: "tsynbOneTick c1  .  c1 = \<up>Tick"
  by (metis fun_upd_same option.sel tsynbOneTick.rep_eq tsynbOneTick_def ubgetch_insert)

end