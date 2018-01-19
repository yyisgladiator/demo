theory tsynBundle

imports tsynStream "../untimed/SB"

begin

default_sort message


lift_definition tsynbOneTick:: "channel \<Rightarrow> 'm event SB" is
"\<lambda>c. [c \<mapsto> \<up>Tick]"
  unfolding ubWell_def
  unfolding usOkay_stream_def
  unfolding ctype_event_def
  by simp



lemma tsynbonetick_dom [simp]: "ubDom\<cdot>(tsynbOneTick c) = {c}"
  by (simp add: tsynbOneTick.rep_eq ubdom_insert)

lemma tsynbonetick_len [simp]: "ubLen (tsynbOneTick c) = Fin 1"
  unfolding ubLen_def
  apply auto
  unfolding ubGetCh_def
  apply auto
  apply(simp add: tsynbOneTick.rep_eq)
  by (metis (mono_tags, lifting) Fin_02bot Fin_Suc LeastI_ex One_nat_def bot_is_0 lscons_conv slen_scons strict_slen sup'_def usLen_stream_def)

end