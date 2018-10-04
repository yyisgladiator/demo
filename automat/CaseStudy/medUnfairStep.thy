theory medUnfairStep

imports medUnfairAut

begin


(* counter not null, drop every message and count one down *)
lemma "spsConcIn (medIn (Msg m)) (medUnfair) = spsConcOut (medOut -)(medUnfair)"
  oops

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (medIn -) (medUnfair) = spsConcOut (medOut -)(medUnfair)"
  oops

lemma "uspecIsConsistent (medUnfair state)"
  oops  (* ToDo: Prove this by using the consistent lemma over medFair *)



end
