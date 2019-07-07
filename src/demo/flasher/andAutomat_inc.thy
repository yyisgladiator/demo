theory andAutomat_inc

imports inAndData outAndData bundle.SB_fin emptychanData
begin

(*State datatype*)
datatype S_and = Single

instance S_and::countable
  by(countable_datatype)
(*interpretations And*)

interpretation andInSBE: sbeGen "buildAndinSBE"
  sorry

interpretation andOutSBE: sbeGen "buildAndoutSBE"
  sorry

end