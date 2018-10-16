theory medUnfairStep

imports medUnfairAut

begin

(* Do not use this, look in "medUnfairAut" *)



(* counter not null, drop every message and count one down *)
lemma "spsConcIn (mediumIn_i (Msg m)) (medUnfair ) = spsConcOut (mediumOut_o -)(medUnfair )"
  oops

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (mediumIn_i -) (medUnfair ) = spsConcOut (mediumOut_o -)(medUnfair )"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (mediumIn_i (Msg m)) (medUnfair ) 
  = uspecUnion\<cdot>
      (spsConcOut (mediumOut_o (Msg m))(uspecFlatten mediumDom mediumRan (Rev {medUnfair })))\<cdot>
      (spsConcOut (mediumOut_o (Msg m))(medUnfair ))"
  oops


lemma "uspecIsConsistent (medUnfair)"
  oops  (* ToDo: Prove this by using the consistent lemma over medFair *)



end
