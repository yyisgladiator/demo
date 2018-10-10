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
  sorry

lemma spfconcout_split:"spfConcOut (ubConcEq a\<cdot>b)\<cdot>spf = spfConcOut a\<cdot>(spfConcOut b\<cdot>spf)"
  sorry

lemma spfconcout_least [simp]: "spfConcOut (ubLeast cs)\<cdot>spf = spf"
  sorry

lemma spfconcin_least [simp]: "spfConcIn (ubLeast cs)\<cdot>spf = spf"
  sorry
lemma spfconcin_out_switch: "spfConcIn a\<cdot>(spfConcOut b\<cdot>spf) = spfConcOut b\<cdot>(spfConcIn a\<cdot>spf)"
  sorry

(* 7. *)
lemma 
"a\<noteq>b \<Longrightarrow> spfConcIn (passwordIn_list_i [(Msg a), null, (Msg b)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-])\<cdot>(spfConcIn (passwordIn_list_i [Msg b]) \<cdot>(passwordStep( PasswordState Initial Buf2)))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_4_0)


end