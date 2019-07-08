theory notAutomat_inc

imports inNotData outNotData bundle.SB_fin
begin

(*State datatype*)
datatype S_not = Single

instance S_not::countable
  by(countable_datatype)
(*interpretations And*)

interpretation notInSBE: sbeGen "buildNotinSBE"
  apply(unfold_locales)
  apply(simp add: buildnotin_ctype)
  apply (simp add: buildnotin_inj)
  apply (simp add: buildnotin_surj)
  by simp

interpretation notOutSBE: sbeGen "buildNotoutSBE"
  apply(unfold_locales)
  apply(simp add: buildnotout_ctype)
  apply (simp add: buildnotout_inj)
  apply (simp add: buildnotout_surj)
  by simp

end