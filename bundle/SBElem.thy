theory SBElem

imports SB tsynBundle

begin
default_sort message


lemma sbelemwell_empty: "sbElemWell Map.empty"
  by(simp add: sbElemWell_def)

typedef 'm sbElem = "{x :: (channel\<rightharpoonup>'m::message) . sbElemWell x}"
  using sbelemwell_empty by blast

setup_lifting type_definition_sbElem


lift_definition sbeNull :: "channel set \<Rightarrow> 'a::message tsyn sbElem" is
"\<lambda>cs. (\<lambda>c. (c\<in>cs) \<leadsto> -)"
 unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition sbe2SB::"'a::message sbElem \<Rightarrow> 'a SB" is
"\<lambda> elem. (\<lambda>c. (c\<in>dom (Rep_sbElem elem)) \<leadsto> \<up>(Rep_sbElem elem)\<rightharpoonup>c)"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  apply simp
  using Rep_sbElem sbElemWell_def by auto

definition sbeDom :: "'a sbElem \<Rightarrow> channel set" where
"sbeDom sbe = dom (Rep_sbElem sbe)"




lemma sbe2sb_dom [simp]: "ubDom\<cdot>(sbe2SB sbe) = sbeDom sbe"
  by(simp add: sbeDom_def ubdom_insert sbe2SB.rep_eq)

lemma sbedom_null[simp]: "sbeDom (sbeNull cs) = cs"
  by(simp add: sbeDom_def sbeNull.rep_eq)


end