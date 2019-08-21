theory sumUpAutomat_inc

imports inSumUpData outSumUpData bundle.SB_fin
begin

(*State datatype*)
datatype S_sumUp =  S nat

instance S_sumUp::countable
  by(countable_datatype)
(*interpretations And*)

interpretation sumUpInSBE: sbeGen "buildSumUpinSBE"
  apply(unfold_locales)
  apply(simp add: buildsumUpin_ctype)
  apply (simp add: buildsumUpin_inj)
  apply (simp add: buildsumUpin_surj)
  by simp

interpretation sumUpInSB: sbGen "buildSumUpinSB"
  apply(unfold_locales)
  sorry

interpretation sumUpOutSBE: sbeGen "buildSumUpoutSBE"
  apply(unfold_locales)
  apply(simp add: buildsumUpout_ctype)
  apply (simp add: buildsumUpout_inj)
  apply (simp add: buildsumUpout_surj)
  by simp


interpretation sumUpOutSB: sbGen "buildSumUpoutSB"
  apply(unfold_locales)
  sorry

end