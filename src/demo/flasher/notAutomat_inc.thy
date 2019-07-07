theory notAutomat_inc

imports inNotData outNotData bundle.SB_fin
begin

(*State datatype*)
datatype S_not = Single

instance S_not::countable
  by(countable_datatype)
(*interpretations And*)

interpretation notInSBE: sbeGen "buildNotinSBE"
  sorry

interpretation notOutSBE: sbeGen "buildNotoutSBE"
  sorry

end