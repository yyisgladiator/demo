theory time_synchron_ubundle
  imports UBundle "untimed/Streams" "timed/TStream" "inc/OptionCpo"

begin

default_sort countable

definition tsyn :: "'a event stream \<Rightarrow> bool" where 
"tsyn s \<equiv> (\<forall> n. Fin n < #s \<longrightarrow> tslen\<cdot>(tsNth n\<cdot>(Abs_tstream(s))) \<le> Fin 1)"


definition tsyn_well :: "'a event stream \<Rightarrow> bool" where
"tsyn_well s \<equiv> ts_well s \<and> tsyn s"

pcpodef 'a tsynstream = "{t :: 'a event stream. tsyn_well t}"
   apply auto
   apply (simp add: tsyn_well_def tslen_bottom)
   apply (metis Fin_02bot lnle_Fin_0 lnzero_def order_less_le strict_slen tsyn_def)
   apply (simp add: adm_def) sorry

definition tsynDom :: "'a tsynstream \<rightarrow> 'a set" where
"tsynDom \<equiv> \<Lambda> ts . {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tsynstream ts)}"

definition tsynlen:: "'a tsynstream \<rightarrow> lnat" where 
"tsynlen \<equiv> \<Lambda> ts. #(Rep_tsynstream ts)"

instantiation tsynstream :: (message) uscl
begin

definition usOkay_tsynstream :: "channel \<Rightarrow> 'm::message tsynstream \<Rightarrow> bool" where
"usOkay_tsynstream c ts \<equiv> (ctype c = tsynDom\<cdot>ts)"

definition usLen_tsynstream :: "'a tsynstream \<rightarrow> lnat" where 
"usLen_tsynstream = tsynlen"

instance
  apply intro_classes apply (simp add: adm_def)
proof 
  fix c :: "channel" and Y :: "nat \<Rightarrow> 'a tsynstream"
  have " chain Y \<Longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<Longrightarrow> usOkay c (\<Squnion>i::nat. Y i)"
  proof -
    fix Y :: "nat \<Rightarrow> 'a tsynstream" assume a0:"chain Y" and a1:"(\<forall>i::nat. usOkay c (Y i))"
  have 1: "\<forall> i. tsynDom\<cdot>(Y i) = tsynDom\<cdot>(\<Squnion> i. Y i)"
    by (smt a0 a1 chain_monofun contlub_cfun_arg is_ub_thelub lub_below po_eq_conv usOkay_tsynstream_def)
  show "usOkay c (\<Squnion>i::nat. Y i)"
    using "1" a1 usOkay_tsynstream_def by blast
  qed
  then show "chain Y \<longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<longrightarrow> usOkay c (\<Squnion>i::nat. Y i)" by blast
  qed
end


end