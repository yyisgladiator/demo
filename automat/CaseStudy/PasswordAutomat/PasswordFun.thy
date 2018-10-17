theory PasswordFun

imports PasswordAutomaton
begin

lemma sbedom_S0[simp]: "sbeDom (passwordElemIn_i -) = daDom passwordAutomaton"
  by auto

lemma output_S0[simp]: "daNextOutput passwordAutomaton (PasswordState S Buf) (passwordElemIn_i -) = passwordOut_o -"
  apply (simp add: daNextOutput_def)
  by (metis PasswordSubstate.exhaust passwordTransition_1_0 passwordTransition_3_0 passwordTransition_5_0 snd_conv)

lemma state_S0[simp]:"daNextState passwordAutomaton (PasswordState Initial Buf) (passwordElemIn_i -) = PasswordState Initial ''''"
  by (simp add:daNextState_def)

lemma help_dom:"(ubDom\<cdot>b \<union> ubDom\<cdot>(y)) \<inter> ubDom\<cdot>(y) = ubDom\<cdot>(y)"
  by auto

lemma spfconcin_split:"spfConcIn (ubConcEq a\<cdot>b)\<cdot>spf = spfConcIn b\<cdot>(spfConcIn a\<cdot>spf)"
  apply(rule ufun_eqI)
   apply(simp)
  apply (subst spfConcIn_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply (subst spfConcIn_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply (subst spfConcIn_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
   apply auto
  apply (subst help_dom)
  apply (simp add: ubclDom_ubundle_def)
  
  sorry



lemma spfconcout_split:"spfConcOut (ubConcEq a\<cdot>b)\<cdot>spf = spfConcOut a\<cdot>(spfConcOut b\<cdot>spf)"
  apply(rule ufun_eqI)
   apply(simp)
  apply (subst spfConcOut_step)  (* subst wendet es genau einmal an... simp klappt gerade irgendwie nicht *)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply simp
  apply (subst spfConcOut_step) 
    apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply (subst spfConcOut_step) 
   apply (simp add: ubclDom_ubundle_def) 
  apply simp
  apply (subst help_dom)
  apply (simp add: ubclDom_ubundle_def) 
  
  sorry
(*
lemma "ubConc (ubConc a\<cdot>b)\<cdot>(spf \<rightleftharpoons> x) = ubConc a\<cdot>(ubConc b\<cdot>(spf \<rightleftharpoons> x))"
*)
lemma spfconcout_least [simp]: "spfConcOut (ubLeast cs)\<cdot>spf = spf"
  apply(rule ufun_eqI)
   apply(simp)
  apply (subst spfConcOut_step)
  apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply simp
  apply (simp add: ubclDom_ubundle_def)
  
  sorry

lemma spfconcin_least [simp]: "spfConcIn (ubLeast cs)\<cdot>spf = spf"
  apply(rule ufun_eqI)
   apply(simp)
  apply (subst spfConcIn_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply simp
  apply (simp add: ubclDom_ubundle_def)
  by (metis (no_types, lifting) spfConcOut_def spfconcout_least ubclDom_ubundle_def ubclLeast_ubundle_def ubconc_sbhdrt ubconc_ubleast ubconceq_dom ubconceq_insert ubrestrict_ubdom2 ubrestrict_ubleast_inter ufapplyout_apply uflift_apply uflift_dom uflift_ran_h)

lemma spfconcin_out_switch: "spfConcIn a\<cdot>(spfConcOut b\<cdot>spf) = spfConcOut b\<cdot>(spfConcIn a\<cdot>spf)"
  apply(rule ufun_eqI)
   apply(simp)
  apply (subst spfConcIn_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply simp
  apply (subst spfConcOut_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply blast
  apply (subst spfConcOut_step)
   apply simp+
   apply (simp add: ubclDom_ubundle_def)
  apply (subst spfConcIn_step)
  apply (simp add: ubclDom_ubundle_def)
   by (simp add: ubclDom_ubundle_def)


(* 1. f(null) = null *)
lemma verif_rule_1:
"spfConcIn (passwordIn_list_i [null])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  by(simp add:  passwordStep_1_0)   


(* 2. f(a ) = null *)
lemma  verif_rule_2:
"spfConcIn (passwordIn_list_i [Msg a])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>((passwordStep( PasswordState Initial Buf)))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  sorry


lemma (* SWS: so sieht das 2. lemma eigentlich aus. wenn man (spfConcIn) verwendet hat man immer den rekursiven aufruf drin *)
"(passwordStep (PasswordState Initial Buf)) \<rightleftharpoons> (passwordIn_i (Msg a)) = 
      passwordOut_o -"
  apply (simp add: passwordStep_def)
  sorry

(* 3. f(null x ) = null f(x) *)
lemma  verif_rule_3:
"spfConcIn (passwordIn_list_i [null])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  by(simp add: passwordStep_0_0  passwordStep_1_0)


(* 4. f(a a x ) = null a f(x) *)
lemma  verif_rule_4:
"spfConcIn (passwordIn_list_i [(Msg a),(Msg a)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-, Msg a])\<cdot>(passwordStep( PasswordState Initial ''''))" 
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_2_0)

(* 5. f(a b x ) = null f(b x) *)
lemma  verif_rule_5:
"a\<noteq>b \<Longrightarrow> spfConcIn (passwordIn_list_i [(Msg a), (Msg b)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-])\<cdot>(spfConcIn (passwordIn_list_i [Msg b]) \<cdot>(passwordStep( PasswordState Initial Buf2)))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_2_1)

(* 6. f(a null a x ) = null null a f(x) *)
lemma  verif_rule_6:
"spfConcIn (passwordIn_list_i [(Msg a), null, (Msg a)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-, Msg a])\<cdot>(passwordStep( PasswordState Initial ''''))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_4_1)


(* 7. f(a null b x ) = null null f(b x) *)
lemma  verif_rule_7:
"a\<noteq>b \<Longrightarrow> spfConcIn (passwordIn_list_i [(Msg a), null, (Msg b)])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-])\<cdot>(spfConcIn (passwordIn_list_i [Msg b]) \<cdot>(passwordStep( PasswordState Initial Buf2)))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_4_0)


(* 8. f(a null null x ) = null null null f(x) *)
lemma  verif_rule_8:
"spfConcIn (passwordIn_list_i [(Msg a), null, null])\<cdot>(passwordStep (PasswordState Initial Buf)) = 
      spfConcOut (passwordOut_list_o [-,-,-])\<cdot>((passwordStep( PasswordState Initial '''')))"
  apply (simp add: spfconcin_split spfconcout_split del: ubconceq_insert)
  apply(simp add: passwordStep_0_0)
  apply(simp add: spfconcin_out_switch)
  apply(simp add: passwordStep_3_0)
  apply(simp add: spfconcin_out_switch)
  by(simp add: passwordStep_0_0 passwordStep_5_0)

end