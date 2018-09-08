theory medUnfairStep

imports medUnfairAut

begin


(* counter not null, drop every message and count one down *)
lemma "spsConcIn (medIn (Msg m)) (medUnfair (Suc n)) = spsConcOut (medOut -)\<cdot>(medUnfair n)"
  oops

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (medIn -) (medUnfair state) = spsConcOut (medOut -)\<cdot>(medUnfair state)"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (medIn (Msg m)) (medUnfair 0) 
  = uspecUnion\<cdot>
      (spsConcOut (medOut (Msg m))\<cdot>(uspecFlatten medInDom medOutDom (Rev {medUnfair n |  n. True})))\<cdot>
      (spsConcOut (medOut (Msg m))\<cdot>(medUnfair 0))"
  oops


lemma "uspecIsConsistent (medUnfair state)"
  oops  (* ToDo: Prove this by using the consistent lemma over medFair *)



end
