theory andAutomat_inc

imports inAndData outAndData bundle.SB_fin
begin

(*State datatype*)
datatype S_and = Single

instance S_and::countable
  by(countable_datatype)


end