theory Data_inc
  imports bundle.SB_fin
begin
default_sort type

lemma cmsg_empty: "cMsg c = {} \<longleftrightarrow> c=c3"
  by(cases c; simp add: ctype_def)


lemma cempty[simp]: "cEmpty = {c3}"
  using ctype_empty_iff cEmpty_def cmsg_empty by simp

end