theory time_synchron_ubundle
  imports UBundle "untimed/Streams" "timed/TStream" "inc/OptionCpo"

begin

default_sort countable

definition tsynWell :: "'a event stream \<Rightarrow> bool" where
"tsynWell s \<equiv> ts_well s \<and> (\<forall> n. Fin n < #s \<longrightarrow> tslen\<cdot>(tsNth n\<cdot>(Abs_tstream(s))) \<le> Fin 1)"

pcpodef 'a tsynstream = "{t :: 'a event stream. tsynWell t}"
   apply auto
   apply (simp add: tsynWell_def tslen_bottom)
  sorry


definition tsynDom :: "'a tsynstream \<rightarrow> 'a set" where
"tsynDom \<equiv> \<Lambda> ts . {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tsynstream ts)}"

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
    sorry
end

end