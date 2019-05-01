theory StreamInf
  imports "untimed/Streams" UnivClasses UBundle

begin
default_sort message

definition streaminf_well :: "'a stream \<Rightarrow> bool" where
"streaminf_well s \<equiv> (#s = \<infinity>)"

cpodef 'a stream_inf = "{s :: 'a stream . streaminf_well s}"
  apply (simp add: streaminf_well_def)
  apply (metis fix_eq2 inf_ub ln_less order_less_le slen_scons)
  by (simp add: streaminf_well_def)
setup_lifting datatype_definition_stream_inf
definition sinfDom :: "'a stream_inf \<rightarrow> 'a set" where
"sinfDom \<equiv> (\<Lambda> s. sdom\<cdot>(Rep_stream_inf s))"

instantiation stream_inf :: (message) uscl
begin

definition usOkay_stream_inf :: "channel \<Rightarrow> 'a stream_inf \<Rightarrow> bool" where
"usOkay_stream_inf c s \<equiv>  (sinfDom\<cdot>s \<subseteq> ctype c)"

definition usLen_stream_inf :: "'a stream_inf \<rightarrow> lnat" where
"usLen_stream_inf \<equiv> \<Lambda> s. \<infinity>"

instance
  apply intro_classes
  apply (simp add: adm_def)
proof
  fix c :: "channel" and Y :: "nat \<Rightarrow> 'a stream_inf"
  have " chain Y \<Longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<Longrightarrow> usOkay c (\<Squnion>i::nat. Y i)"
  proof -
    assume a0:"chain Y" and a1:"(\<forall>i::nat. usOkay c (Y i))"
  have 1: "\<forall> i. sinfDom\<cdot>(Y i) \<subseteq> sinfDom\<cdot>(\<Squnion> i. Y i)"
    by (metis SetPcpo.less_set_def a0 is_ub_thelub monofun_cfun_arg)
  show "usOkay c (\<Squnion>i::nat. Y i)"
    using "1" a1 usOkay_stream_inf_def a0
    by (simp add: subset_cont)
  qed
  then show "chain Y \<longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<longrightarrow> usOkay c (\<Squnion>i::nat. Y i)" by blast
  qed
end

cpodef 'a infbundle = "UNIV :: 'a stream_inf ubundle set"
  apply simp
  by auto

end