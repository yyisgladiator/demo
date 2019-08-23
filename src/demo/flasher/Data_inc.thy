(*<*)
theory Data_inc
  imports bundle.SB_fin
begin
default_sort type


text\<open>General ctype information for simp\<close>
lemma cmsg_empty: "cMsg c = {} \<longleftrightarrow> c=cempty"
  by(cases c; simp add: ctype_def)

lemma cempty[simp]: "cEmpty = {cempty}"
  using ctype_empty_iff cEmpty_def cmsg_empty by simp

lemma rangecin[simp]:"range (Tsyn o (map_option) \<B>) = ctype cin"
  apply(auto simp add: ctype_def)
 by (metis option.simps(9) range_eqI)

lemma rangecintern[simp]:"range (Tsyn o (map_option) \<B>) = ctype cintern"
  apply(auto simp add: ctype_def)
  by (metis option.simps(9) range_eqI)

lemma rangecout[simp]:"range (Tsyn o (map_option) \<B>) = ctype cout"
  apply(auto simp add: ctype_def)
  by (metis option.simps(9) range_eqI)

end
(*>*)