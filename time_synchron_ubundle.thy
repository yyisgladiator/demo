theory time_synchron_ubundle
  imports UBundle "untimed/Streams" "timed/TStream" "inc/OptionCpo"

begin

default_sort countable

(*
definition tsynWell :: "'a event stream \<Rightarrow> bool" where
"tsynWell s \<equiv> ts_well s \<and> (\<forall> n. Fin n < #s \<longrightarrow> tslen\<cdot>(tsNth n\<cdot>(Abs_tstream(s))) \<le> Fin 1)"
*)

pcpodef 'a tsynstream = "{t :: 'a event stream. True}"
  by auto

definition tsynDom :: "'a tsynstream \<rightarrow> 'a set" where
"tsynDom \<equiv> \<Lambda> ts . {a | a::'a . (Msg a) \<in> sdom\<cdot>(Rep_tsynstream ts)}"

definition tsynlen:: "'a tsynstream \<rightarrow> lnat" where 
"tsynlen \<equiv> \<Lambda> ts. #(Rep_tsynstream ts)"

instantiation tsynstream :: (message) uscl
begin

definition usOkay_tsynstream :: "channel \<Rightarrow> 'm::message tsynstream \<Rightarrow> bool" where
"usOkay_tsynstream c ts \<equiv> (tsynDom\<cdot>ts \<subseteq> ctype c)"

definition usLen_tsynstream :: "'a tsynstream \<rightarrow> lnat" where 
"usLen_tsynstream = tsynlen"

instance
  apply intro_classes 
  apply (simp add: adm_def)
proof 
  fix c :: "channel" and Y :: "nat \<Rightarrow> 'a tsynstream"
  have " chain Y \<Longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<Longrightarrow> usOkay c (\<Squnion>i::nat. Y i)"
  proof -
    assume a0:"chain Y" and a1:"(\<forall>i::nat. usOkay c (Y i))"
  have 1: "\<forall> i. tsynDom\<cdot>(Y i) \<subseteq> tsynDom\<cdot>(\<Squnion> i. Y i)"
    by (metis SetPcpo.less_set_def a0 is_ub_thelub monofun_cfun_arg)
  show "usOkay c (\<Squnion>i::nat. Y i)"
    using "1" a1 usOkay_tsynstream_def
    by (simp add: usOkay_tsynstream_def a0 subset_cont)
  qed
  then show "chain Y \<longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<longrightarrow> usOkay c (\<Squnion>i::nat. Y i)" by blast
  qed
end

(* lshd etc *)

definition tsynLshd :: "'a tsynstream \<rightarrow> 'a event discr u" where
"tsynLshd \<equiv> \<Lambda> s.  lshd\<cdot>(Rep_tsynstream s)"

definition tsynRt :: "'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynRt \<equiv> \<Lambda> s. Abs_tsynstream (srt\<cdot>(Rep_tsynstream s))"


definition tsynLscons :: "'a event discr u \<rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynLscons \<equiv> \<Lambda> t ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else Abs_tsynstream((lscons\<cdot>t)\<cdot>(Rep_tsynstream ts))"


definition tsynMLscons :: "'a discr u \<rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynMLscons \<equiv> \<Lambda> t ts. tsynLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"



end