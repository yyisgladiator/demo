theory Data_inc
  imports bundle.SB_fin
begin
default_sort type

lemma cmsg_empty: "cMsg c = {} \<longleftrightarrow> c=c3"
  by(cases c; simp add: ctype_def)

lemma cempty[simp]: "cEmpty = {c3}"
  using ctype_empty_iff cEmpty_def cmsg_empty by simp

lemma rangecin1[simp]:"range (Tsyn o (map_option) \<B>) = ctype cin1"
  apply(auto simp add: ctype_def)
 by (metis option.simps(9) range_eqI)

lemma rangecin2[simp]:"range (Tsyn o (map_option) \<B>) = ctype cin2"
  apply(auto simp add: ctype_def)
  by (metis option.simps(9) range_eqI)

lemma rangecout[simp]:"range (Tsyn o (map_option) \<B>) = ctype cout"
  apply(auto simp add: ctype_def)
  by (metis option.simps(9) range_eqI)

end