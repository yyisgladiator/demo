theory PasswordFun

imports PasswordAutomaton
begin

lemma sbedom_S0[simp]: "sbeDom (passwordElemIn_i -) = daDom passwordAutomaton"
  by auto

lemma output_S0[simp]: "daNextOutput passwordAutomaton (PasswordState S0 []) (passwordElemIn_i -) = passwordOut_b_o - -"
  by (simp add: daNextOutput_def)

lemma state_S0[simp]:"daNextState passwordAutomaton (PasswordState S0 []) (passwordElemIn_i -) = PasswordState S0 []"
  by (simp add:daNextState_def)


(* Schlecht, unten ist schöner *)
lemma "spfConcIn (passwordIn_list_i [(Msg a), null, (Msg b)])\<cdot>(passwordStep (undefined (* initial state *))) = 
      spfConcOut (passwordIn_list_i [-,-,-])\<cdot>(passwordStep (undefined (* PasswordSaved state, lastVar = b *)))"
  oops

lemma "\<forall> a b. spfConcIn (ubConcEq a b) spf = spfConcIn b (spfConcIn a spf)"

(* 7. Näher an soll *)
lemma "spfConcIn (passwordIn_list_i [(Msg a), null, (Msg b)])\<cdot>(passwordStep (PasswordState Initial)) = 
      spfConcOut (passwordIn_list_i [-,-])\<cdot>(spfConcIn (passwordIn_list_i [Msg b]) \<cdot>(passwordStep (undefined (*initial *))))"
  apply simp
  oops

(* 
* List zu "passwordIn_i - ubConcEq" form (einfach definition anwenden) 
* spfConcIn zu 2 spfConcIn
   * spfConcIn (ubConcEq a b) spf = spfConcIn b (spfconcIn a spf)
* simp
*)


end