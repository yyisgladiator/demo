(*
 * DO NOT MODIFY!
 * This file was generated from Password.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 18, 2018 7:47:14 PM by isartransformer 3.1.0
 *)
theory PasswordAutomaton
  imports PasswordDatatype PasswordStates automat.dAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun passwordTransitionH :: "(PasswordState \<times> (string tsyn)) \<Rightarrow> (PasswordState \<times> passwordMessage tsyn SB)" where
"passwordTransitionH (PasswordState Initial var_lastB, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (PasswordState PasswortSaved port_i, (passwordOut_o null))" |

"passwordTransitionH (PasswordState Initial var_lastB, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (PasswordState Initial '''', (passwordOut_o null))" |

"passwordTransitionH (PasswordState PasswortSaved var_lastB, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(port_i=var_lastB) then ((PasswordState Initial '''', (passwordOut_o (Msg (port_i)))))
   else if(port_i\<noteq>var_lastB) then ((PasswordState PasswortSaved port_i, (passwordOut_o null)))
   else (PasswordState PasswortSaved var_lastB, (passwordOut_o null)))" |

"passwordTransitionH (PasswordState PasswortSaved var_lastB, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (PasswordState OneTick var_lastB, (passwordOut_o null))" |

"passwordTransitionH (PasswordState OneTick var_lastB, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(port_i\<noteq>var_lastB) then ((PasswordState PasswortSaved port_i, (passwordOut_o null)))
   else if(port_i=var_lastB) then ((PasswordState Initial '''', (passwordOut_o (Msg (port_i)))))
   else (PasswordState OneTick var_lastB, (passwordOut_o null)))" |

"passwordTransitionH (PasswordState OneTick var_lastB, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (PasswordState Initial '''', (passwordOut_o null))"

(* Transition function *)
definition passwordTransition :: "(PasswordState \<times> passwordMessage tsyn sbElem) \<Rightarrow> (PasswordState \<times> passwordMessage tsyn SB)" where
"passwordTransition = (\<lambda> (s,b). (if (sbeDom b) = passwordDom then passwordTransitionH (s, (passwordElem_get_i b)) else undefined))"

(* Initial state *)
definition passwordInitialState :: "PasswordState" where
"passwordInitialState = PasswordState Initial (''''::string)"

(* Initial output *)
definition passwordInitialOutput :: "passwordMessage tsyn SB" where
"passwordInitialOutput = passwordOut_o null"

(* The final automaton *)
lift_definition passwordAutomaton :: "(PasswordState, passwordMessage tsyn) dAutomaton" is
"(passwordTransition, passwordInitialState, passwordInitialOutput, passwordDom, passwordRan)"
  by (simp add: passwordDom_def passwordRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition passwordStep :: "(PasswordState \<Rightarrow> (passwordMessage tsyn, passwordMessage tsyn) SPF)" where
"passwordStep = da_h passwordAutomaton"

(* The final SPF *)
definition passwordSPF :: "(passwordMessage tsyn, passwordMessage tsyn) SPF" where
"passwordSPF = da_H (passwordAutomaton::(PasswordState, passwordMessage tsyn) dAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma passwordautomaton_trans[simp]: "daTransition passwordAutomaton = passwordTransition"
  unfolding daTransition_def
  by(simp add: passwordAutomaton.rep_eq)

lemma passwordautomaton_initialstate[simp]: "daInitialState passwordAutomaton = passwordInitialState"
  unfolding daInitialState_def
  by(simp add: passwordAutomaton.rep_eq)

lemma passwordautomaton_initialoutput[simp]: "daInitialOutput passwordAutomaton = passwordInitialOutput"
  unfolding daInitialOutput_def
  by(simp add: passwordAutomaton.rep_eq)

lemma passwordautomaton_dom[simp]: "daDom passwordAutomaton = passwordDom"
  unfolding daDom_def
  by(simp add: passwordAutomaton.rep_eq)

lemma passwordautomaton_ran[simp]: "daRan passwordAutomaton = passwordRan"
  unfolding daRan_def
  by(simp add: passwordAutomaton.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Initial -> PasswortSaved [i!=null] / {lastB=i}; *)
lemma passwordTransition_0_0[simp]:
  assumes "True"
    shows "passwordTransition ((PasswordState Initial var_lastB), (passwordElemIn_i (Msg port_i)))
         = (PasswordState PasswortSaved port_i, (passwordOut_o null))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 14:  Initial -> Initial {i==null} / {lastB=""}; *)
lemma passwordTransition_1_0[simp]:
  assumes "True"
    shows "passwordTransition ((PasswordState Initial var_lastB), (passwordElemIn_i null))
         = (PasswordState Initial '''', (passwordOut_o null))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 16:  PasswortSaved -> Initial {i==lastB} / {o=i, lastB=""}; *)
lemma passwordTransition_2_0[simp]:
  assumes "port_i=var_lastB"
    shows "passwordTransition ((PasswordState PasswortSaved var_lastB), (passwordElemIn_i (Msg port_i)))
         = (PasswordState Initial '''', (passwordOut_o (Msg (port_i))))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 17:  PasswortSaved -> PasswortSaved [i!=lastB && i!=null] / {lastB=i}; *)
lemma passwordTransition_2_1[simp]:
  assumes "port_i\<noteq>var_lastB"
    shows "passwordTransition ((PasswordState PasswortSaved var_lastB), (passwordElemIn_i (Msg port_i)))
         = (PasswordState PasswortSaved port_i, (passwordOut_o null))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 18:  PasswortSaved -> OneTick {i==null}; *)
lemma passwordTransition_3_0[simp]:
  assumes "True"
    shows "passwordTransition ((PasswordState PasswortSaved var_lastB), (passwordElemIn_i null))
         = (PasswordState OneTick var_lastB, (passwordOut_o null))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 19:  OneTick -> PasswortSaved [i!=lastB && i!=null] / {lastB=i}; *)
lemma passwordTransition_4_0[simp]:
  assumes "port_i\<noteq>var_lastB"
    shows "passwordTransition ((PasswordState OneTick var_lastB), (passwordElemIn_i (Msg port_i)))
         = (PasswordState PasswortSaved port_i, (passwordOut_o null))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 20:  OneTick -> Initial {i==lastB} / {o=i, lastB=""}; *)
lemma passwordTransition_4_1[simp]:
  assumes "port_i=var_lastB"
    shows "passwordTransition ((PasswordState OneTick var_lastB), (passwordElemIn_i (Msg port_i)))
         = (PasswordState Initial '''', (passwordOut_o (Msg (port_i))))"
  using assms by(auto simp add: passwordTransition_def assms)

(* Line 21:  OneTick -> Initial {i==null} / {lastB=""}; *)
lemma passwordTransition_5_0[simp]:
  assumes "True"
    shows "passwordTransition ((PasswordState OneTick var_lastB), (passwordElemIn_i null))
         = (PasswordState Initial '''', (passwordOut_o null))"
  using assms by(auto simp add: passwordTransition_def assms)


section \<open>Step-wise lemmata for the SPF\<close>

(* Convert the SPF to step notation *)
lemma passwordSpf2Step: "passwordSPF = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState Initial (''''::string)))"
  by(simp add: passwordSPF_def da_H_def passwordInitialOutput_def passwordInitialState_def passwordStep_def)

(* Line 15:  Initial -> PasswortSaved [i!=null] / {lastB=i}; *)
lemma passwordStep_0_0:
  assumes "True"
    shows "spfConcIn  (passwordIn_i (Msg port_i))\<cdot>(passwordStep (PasswordState Initial var_lastB))
         = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState PasswortSaved port_i))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 14:  Initial -> Initial {i==null} / {lastB=""}; *)
lemma passwordStep_1_0:
  assumes "True"
    shows "spfConcIn  (passwordIn_i null)\<cdot>(passwordStep (PasswordState Initial var_lastB))
         = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState Initial ''''))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 16:  PasswortSaved -> Initial {i==lastB} / {o=i, lastB=""}; *)
lemma passwordStep_2_0:
  assumes "port_i=var_lastB"
    shows "spfConcIn  (passwordIn_i (Msg port_i))\<cdot>(passwordStep (PasswordState PasswortSaved var_lastB))
         = spfConcOut (passwordOut_o (Msg (port_i)))\<cdot>(passwordStep (PasswordState Initial ''''))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 17:  PasswortSaved -> PasswortSaved [i!=lastB && i!=null] / {lastB=i}; *)
lemma passwordStep_2_1:
  assumes "port_i\<noteq>var_lastB"
    shows "spfConcIn  (passwordIn_i (Msg port_i))\<cdot>(passwordStep (PasswordState PasswortSaved var_lastB))
         = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState PasswortSaved port_i))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 18:  PasswortSaved -> OneTick {i==null}; *)
lemma passwordStep_3_0:
  assumes "True"
    shows "spfConcIn  (passwordIn_i null)\<cdot>(passwordStep (PasswordState PasswortSaved var_lastB))
         = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState OneTick var_lastB))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 19:  OneTick -> PasswortSaved [i!=lastB && i!=null] / {lastB=i}; *)
lemma passwordStep_4_0:
  assumes "port_i\<noteq>var_lastB"
    shows "spfConcIn  (passwordIn_i (Msg port_i))\<cdot>(passwordStep (PasswordState OneTick var_lastB))
         = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState PasswortSaved port_i))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 20:  OneTick -> Initial {i==lastB} / {o=i, lastB=""}; *)
lemma passwordStep_4_1:
  assumes "port_i=var_lastB"
    shows "spfConcIn  (passwordIn_i (Msg port_i))\<cdot>(passwordStep (PasswordState OneTick var_lastB))
         = spfConcOut (passwordOut_o (Msg (port_i)))\<cdot>(passwordStep (PasswordState Initial ''''))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 21:  OneTick -> Initial {i==null} / {lastB=""}; *)
lemma passwordStep_5_0:
  assumes "True"
    shows "spfConcIn  (passwordIn_i null)\<cdot>(passwordStep (PasswordState OneTick var_lastB))
         = spfConcOut (passwordOut_o null)\<cdot>(passwordStep (PasswordState Initial ''''))"
  apply(simp add: passwordStep_def passwordIn_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

lemmas passwordSteps = passwordStep_0_0 passwordStep_1_0 passwordStep_2_0 passwordStep_2_1 passwordStep_3_0 passwordStep_4_0 passwordStep_4_1 passwordStep_5_0

end