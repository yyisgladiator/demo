theory evenAutomat_inc

imports inEvenData outEvenData bundle.SB_fin
begin

(*State datatype*)
datatype S_even =  S bool

instance S_even::countable
  by(countable_datatype)
(*interpretations And*)

interpretation evenInSBE: sbeGen "buildEveninSBE"
  apply(unfold_locales)
  apply(simp add: buildevenin_ctype)
  apply (simp add: buildevenin_inj)
  apply (simp add: buildevenin_surj)
  by simp

interpretation evenInSB: sbGen "buildEveninSB"
  apply(unfold_locales)
  sorry

interpretation evenOutSBE: sbeGen "buildEvenoutSBE"
  apply(unfold_locales)
  apply(simp add: buildevenout_ctype)
  apply (simp add: buildevenout_inj)
  apply (simp add: buildevenout_surj)
  by simp


interpretation evenOutSB: sbGen "buildEvenoutSB"
  apply(unfold_locales)
  sorry

end