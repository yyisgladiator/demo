theory StreamInf
  imports "untimed/Streams" UnivClasses

begin
default_sort countable

definition streaminf_well :: "'a stream \<Rightarrow> bool" where
"streaminf_well s \<equiv> (#s = \<infinity>)"

cpodef 'a stream_inf = "{s :: 'a stream . streaminf_well s}"
   apply auto
  apply (simp add: streaminf_well_def)
   apply (metis fix_eq2 inf_ub ln_less order_less_le slen_scons)
  apply (simp add: adm_def)
  using inf_chainl4 l42 streaminf_well_def by fastforce


instantiation stream_inf :: (message) uscl
begin

definition usOkay_stream_inf :: "channel \<Rightarrow> 'a stream_inf \<Rightarrow> bool" where
"usOkay_stream_inf c s \<equiv> (ctype c = sdom\<cdot>(Rep_stream_inf s))"

definition usLen_stream_inf :: "'a stream_inf \<rightarrow> lnat" where
"usLen_stream_inf \<equiv> \<Lambda> s. \<infinity>"

instance
  apply intro_classes
  sorry

end

end