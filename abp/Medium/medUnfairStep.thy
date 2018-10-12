theory medUnfairStep

imports medUnfairAut

begin


(* counter not null, drop every message and count one down *)
lemma "spsConcIn (mediumIn_i (Msg m)) (medUnfair (Suc n)) = spsConcOut (mediumOut_o -)(medUnfair n)"
  oops

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (mediumIn_i -) (medUnfair state) = spsConcOut (mediumOut_o -)(medUnfair state)"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (mediumIn_i (Msg m)) (medUnfair 0) 
  = uspecUnion\<cdot>
      (spsConcOut (mediumOut_o (Msg m))(uspecFlatten mediumDom mediumRan (Rev {medUnfair n |  n. True})))\<cdot>
      (spsConcOut (mediumOut_o (Msg m))(medUnfair 0))"
  oops


lemma "uspecIsConsistent (medUnfair state)"
  oops  (* ToDo: Prove this by using the consistent lemma over medFair *)



end
