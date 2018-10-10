theory medFairStep

imports medFairAut

begin


(* counter not null, drop every message and count one down *)
lemma "spsConcIn (medIn (Msg m)) (medFair (Suc n)) = spsConcOut (medOut -) (medFair n)"
  oops  (* ToDo: Prove this by using the medUnfairStep lemma *)

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (medIn -) (medFair state) = spsConcOut (medOut -) (medFair state)"
  oops  (* ToDo: Prove this by using the medUnfairStep lemma *)

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (medIn (Msg m)) (medFair 0) = spsConcOut (medOut (Msg m)) (uspecFlatten medInDom medOutDom (Rev {medFair n |  n. True}))"
  oops  (* ToDo: Prove this by using the medUnfairStep lemma (and additional lemma here)*)

lemma "uspecIsConsistent (medFair state)"
  oops

end