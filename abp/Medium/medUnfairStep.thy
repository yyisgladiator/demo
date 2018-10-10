theory medUnfairStep

imports medUnfairAut

begin


(* counter not null, drop every message and count one down *)
lemma "spsConcIn (mediumIn_ar (Msg m)) (medUnfair (Suc n)) = spsConcOut (mediumOut_as -)(medUnfair n)"
  oops

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (mediumIn_ar -) (medUnfair state) = spsConcOut (mediumOut_as -)(medUnfair state)"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (mediumIn_ar (Msg m)) (medUnfair 0) 
  = uspecUnion\<cdot>
      (spsConcOut (mediumOut_as (Msg m))(uspecFlatten mediumDom mediumRan (Rev {medUnfair n |  n. True})))\<cdot>
      (spsConcOut (mediumOut_as (Msg m))(medUnfair 0))"
  oops


lemma "uspecIsConsistent (medUnfair state)"
  oops  (* ToDo: Prove this by using the consistent lemma over medFair *)



end
