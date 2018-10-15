theory PasswordFun

imports PasswordAutomaton
begin

lemma sbedom_S0[simp]: "sbeDom (passwordElemIn_i -) = daDom passwordAutomaton"
  by auto

lemma output_S0[simp]: "daNextOutput passwordAutomaton (PasswordState S Buf) (passwordElemIn_i -) = passwordOut_o -"
  apply (simp add: daNextOutput_def)
  by (metis PasswordSubstate.exhaust passwordTransition_1_0 passwordTransition_3_0 passwordTransition_5_0 snd_conv)

lemma state_S0[simp]:"daNextState passwordAutomaton (PasswordState Initial Buf) (passwordElemIn_i -) = PasswordState Initial Buf"
  by (simp add:daNextState_def)

lemma spfconcin_split:"spfConcIn (ubConcEq a\<cdot>b)\<cdot>spf = spfConcIn b\<cdot>(spfConcIn a\<cdot>spf)"
  apply (simp add:ubConcEq_def)
  sorry


lemma spfconcout_split:"spfConcOut (ubConcEq a\<cdot>b)\<cdot>spf = spfConcOut a\<cdot>(spfConcOut b\<cdot>spf)"
  sorry

lemma spfconcout_least [simp]: "spfConcOut (ubLeast cs)\<cdot>spf = spf"
  sorry

lemma spfconcin_least [simp]: "spfConcIn (ubLeast cs)\<cdot>spf = spf"
  apply (simp add:ubLeast_def)
  sorry

lemma spfconcin_out_switch: "spfConcIn a\<cdot>(spfConcOut b\<cdot>spf) = spfConcOut b\<cdot>(spfConcIn a\<cdot>spf)"
  sorry



(* 1. f(null) = null *)
lemma (* SWS: lemma muss einen Namen haben *)
"spfConcIn (passwordIn_list_i [null])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add:  passwordStep_1_0)   
  sorry
(* SWS: 3 Varianten. 
- Du änderst das MAA-Modell und der buffer wird bei der Transition auf "" gesetzt        
   die hier: Initial -> Initial   {i==null};
- Oder einfacher: anstatt '''' ist der wieder "Buf" 
*)


(* 2. f(a ) = null *)
lemma 
"spfConcIn (passwordIn_list_i [Msg a])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add:  passwordStep_0_0)
  sorry

lemma (* SWS: so sieht das 2. lemma eigentlich aus. wenn man (spfConcIn) verwendet hat man immer den rekursiven aufruf drin *)
"(passwordStep (PasswordState Initial Buf)) \<rightleftharpoons> (passwordIn_i (Msg a)) = 
      passwordOut_o -"
  sorry

(* 3. f(null x ) = null f(x) *)
lemma 
"spfConcIn (passwordIn_list_i [null])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0  passwordStep_1_0)
  sorry


(* 4. f(a a x ) = null a f(x) *)
lemma 
"spfConcIn (passwordIn_list_i [(Msg a),(Msg a)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-, Msg a])\<cdot>(passwordStep( PasswordState Initial a))"  (* SWS: Das "a" im Buffer sollte '''' sein. MAA-Modell anpassen *)
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_2_0)


(* 5. f(a b x ) = null f(b x) *)
lemma 
"a\<noteq>b \<Longrightarrow> spfConcIn (passwordIn_list_i [(Msg a), (Msg b)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>(spfConcIn (passwordIn_list_i [Msg b]) \<cdot>(passwordStep( PasswordState Initial Buf2)))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_2_1)

(* 6. f(a null a x ) = null null a f(x) *)
lemma 
"spfConcIn (passwordIn_list_i [(Msg a), null, (Msg a)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-, Msg a])\<cdot>(passwordStep( PasswordState Initial ''''))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_4_1)


(* 7. f(a null b x ) = null null f(b x) *)
lemma 
"a\<noteq>b \<Longrightarrow> spfConcIn (passwordIn_list_i [(Msg a), null, (Msg b)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-])\<cdot>(spfConcIn (passwordIn_list_i [Msg b]) \<cdot>(passwordStep( PasswordState Initial Buf2)))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_4_0)


(* 8. f(a null null x ) = null null null f(x) *)
lemma 
"spfConcIn (passwordIn_list_i [(Msg a), null, null])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-,-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_5_0)

end