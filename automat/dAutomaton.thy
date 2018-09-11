(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
    Abbreviation: "da" for deterministic automaton
*)

theory dAutomaton
  imports fun.SPF NewSpfStep

begin

  default_sort type

(* VERY Basic automaton wellformed condition *)
fun daWell::"((('state \<times>'m sbElem) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set) \<Rightarrow> bool " where
"daWell (transition, initialState, initialOut, chIn, chOut) = (finite chIn (* \<and> (\<forall>s f. (dom f = chIn \<and> sbElemWell f) \<longrightarrow> ubDom\<cdot>(snd(transition (s,f))) = chOut)*))"

lemma dawellI: assumes "finite In" 
                         (*   and "\<And>s f. (dom f = In \<and> sbElemWell f) \<Longrightarrow> ubDom\<cdot>(snd(transition (s,f))) = Out"  *)
                         shows "daWell (transition, initialState, initialOut, In, Out)"
  by(simp add: assms)


lemma automaton_ex:"daWell ((\<lambda>f. (myState, ubLeast {})), State, ubLeast {}, {}, {})"
  by(rule dawellI,auto)




(* The content is:
  transition function \<times> initial state \<times> initial Output \<times> input domain \<times> output domain *)
typedef ('state::type, 'm::message) dAutomaton =
  "{f::(('state \<times>'m sbElem) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set. daWell f}"
  by auto

setup_lifting type_definition_dAutomaton





(*******************************************************************)
  section \<open>Definitions\<close>
(*******************************************************************)

definition daTransition :: "('s, 'm::message) dAutomaton \<Rightarrow> (('s \<times>'m sbElem) \<Rightarrow> ('s \<times> 'm SB))" where
"daTransition automat = fst (Rep_dAutomaton automat)"

definition daInitialState :: "('s, 'm::message) dAutomaton \<Rightarrow> 's" where
"daInitialState automat = fst (snd (Rep_dAutomaton automat))"

definition daInitialOutput :: "('s, 'm::message) dAutomaton \<Rightarrow> 'm SB" where
"daInitialOutput automat = fst (snd (snd (Rep_dAutomaton automat)))"

definition daDom :: "('s, 'm::message) dAutomaton \<Rightarrow> channel set" where
"daDom automat = fst (snd (snd (snd (Rep_dAutomaton automat))))"

definition daRan :: "('s, 'm::message) dAutomaton \<Rightarrow> channel set" where
"daRan automat = (snd (snd (snd (snd (Rep_dAutomaton automat)))))"


(* Given a state and an input it returns the next state *)
definition daNextState:: "('s::type, 'm::message) dAutomaton \<Rightarrow> 's \<Rightarrow>  ('m sbElem) \<Rightarrow> 's" where
"daNextState aut s m = fst ((daTransition aut) (s,m))"

(* Given a state and an input it returns the next output *)
definition daNextOutput:: "('s::type, 'm::message) dAutomaton \<Rightarrow> 's \<Rightarrow>  ('m sbElem) \<Rightarrow>  'm SB" where
"daNextOutput aut s m = snd ((daTransition aut) (s,m))"




definition da_helper:: "(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message  SB)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 'm SPF) \<rightarrow> ('e \<Rightarrow> 'm SPF)" where
"da_helper f s \<equiv> \<Lambda> h. (\<lambda> e. spfRtIn\<cdot>(spfConcOut (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))"

(* As defined in Rum96 *)
definition da_h :: "('s::type, 'm::message) dAutomaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"da_h automat = spfStateFix (daDom automat)(daRan automat)\<cdot>
     (\<Lambda> h. (\<lambda>s. spfStep  (daDom automat) (daRan automat)\<cdot>(da_helper (daTransition automat) s\<cdot>h)))"

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition da_H :: "('s, 'm::message) dAutomaton \<Rightarrow> 'm SPF" where
"da_H automat = spfConcOut (daInitialOutput automat)\<cdot>(da_h automat (daInitialState automat))"





(*******************************************************************)
  section \<open>Lemma\<close>
(*******************************************************************)


lemma da_rep_well[simp]:"daWell (Rep_dAutomaton automat)"
  using Rep_dAutomaton by auto

lemma da_dom_finite[simp]:"finite (daDom automat)"
  by (metis da_rep_well daWell.simps daDom_def surjective_pairing)



  section \<open>Lemma about helper\<close>
  
lemma da_helper_dom [simp]:"ufDom\<cdot>((da_helper (daTransition automat) s\<cdot>(da_h automat)) f) = ufDom\<cdot>((da_h automat) s)"
  by(simp add: da_helper_def da_h_def spfstatefix_dom)

lemma da_helper_ran:"ufRan\<cdot>((da_helper (daTransition automat) s\<cdot>(da_h automat)) f) = ufRan\<cdot>((da_h automat) s)"
  by(simp add: da_helper_def da_h_def spfstatefix_ran)




  section \<open>Lemma about h\<close>

lemma da_h_dom [simp]:"ufDom\<cdot>(da_h automat s) = daDom automat"
  by(simp add: da_h_def spfstatefix_dom)

lemma da_h_ran [simp]:"ufRan\<cdot>(da_h automat s) = daRan automat"
  by(simp add: da_h_def spfstatefix_ran)

lemma da_dom_ran_well[simp]:assumes "ubDom\<cdot>sb = daDom automat" 
  shows "ufDom\<cdot>((da_helper (daTransition automat) s\<cdot>(da_h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = daDom automat \<and>
         ufRan\<cdot>((da_helper (daTransition automat) s\<cdot>(da_h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = daRan automat"
  apply rule
   apply simp
  by(simp add: da_helper_ran)


lemma da_h_unfolding: "(da_h automat s) = spfStep (daDom automat) (daRan automat)\<cdot>(da_helper (daTransition automat) s\<cdot>(da_h automat))"
  apply(simp add: da_h_def)
  by(subst spfStateFix_fix,simp_all)

lemma da_h_step: assumes "ubDom\<cdot>sb = daDom automat" and "\<forall>c\<in>daDom automat. sb  .  c \<noteq> \<epsilon>"
            shows "(da_h automat s)\<rightleftharpoons>sb = ((da_helper (daTransition automat) s\<cdot>(da_h automat)) (Abs_sbElem((inv convDiscrUp)(sbHdElem\<cdot>sb)))) \<rightleftharpoons>sb"
  apply (simp add: da_h_unfolding)
  apply(rule NewSpfStep.spfstep_step)
  by (simp_all add: assms sbHdElemWell_def da_helper_ran)

(* see below for a readable version *)
lemma da_h_final:
  assumes "ubDom\<cdot>sb = daDom automat" 
      and "\<forall>c\<in>daDom automat. sb  .  c \<noteq> \<epsilon>"
  shows "(da_h automat s)\<rightleftharpoons>sb =
  spfConcOut (daNextOutput automat s (Abs_sbElem((inv convDiscrUp)(sbHdElem\<cdot>sb))))\<cdot>(spfRtIn\<cdot>(da_h automat (daNextState automat s (Abs_sbElem((inv convDiscrUp)(sbHdElem\<cdot>sb)))))) \<rightleftharpoons>sb"
  apply(subst da_h_step, simp_all add: assms)
  by (simp add: assms(1) daNextOutput_def daNextState_def da_helper_def spfRtIn_spfConcOut)

lemma da_h_final_h2:
  assumes "sbeDom sbe = daDom automat" and "ubDom\<cdot>sb = daDom automat"
  shows "(da_h automat s)\<rightleftharpoons> (ubConcEq (sbe2SB sbe)\<cdot>sb) =
  spfConcOut (daNextOutput automat s sbe)\<cdot>(spfRtIn\<cdot>(da_h automat (daNextState automat s sbe))) \<rightleftharpoons> (ubConcEq (sbe2SB sbe)\<cdot>sb)"
  apply(subst da_h_final)
  using assms(2) ubconceq_dom apply blast
  apply (metis assms(1) assms(2) sbHdElem_bottom_exI sbHdElem_channel sbe2sb_dom sbe2sb_hdelem_conc sbe2sb_nbot ubconceq_dom)
  by (metis assms(1) assms(2) sbe2sb_hdelem4)

lemma da_h_final_h3:
  assumes "sbeDom sbe = daDom automat" and "ubDom\<cdot>sb = daDom automat"
  shows "(da_h automat s)\<rightleftharpoons> (ubConcEq (sbe2SB sbe)\<cdot>sb) =
  spfConcOut (daNextOutput automat s sbe)\<cdot>((da_h automat (daNextState automat s sbe))) \<rightleftharpoons> (sb)"
  using assms(1) assms(2) da_h_final_h2 sbe2sb_rt by fastforce

(* Use this ! *)
lemma da_h_final2: assumes "sbeDom sbe = daDom da"
  shows "spfConcIn (sbe2SB sbe)\<cdot>(da_h da s) = spfConcOut (daNextOutput da s sbe)\<cdot>((da_h da (daNextState da s sbe)))"
  by (metis (no_types) assms da_h_dom da_h_final_h3 spfConcIn_dom spfConcIn_step spfConcOut_dom spf_eq)

lemma da_h_bottom: assumes "ubDom\<cdot>sb = daDom automat" and "\<exists>c\<in>daDom automat. sb  .  c = \<epsilon>"
  shows "(da_h automat s)\<rightleftharpoons>sb = ubclLeast (daRan automat)"
  apply(simp add: da_h_unfolding spfStep_def assms)
  apply (simp add: spfStep_inj_def sbHdElemWell_def)
  by (metis assms(1) assms(2) ubclDom_ubundle_def ufleast_apply) 


section \<open>Lemma about H\<close>
  
lemma da_H_unfolding:
  "da_H automat = spfConcOut (daInitialOutput automat)\<cdot>(da_h automat (daInitialState automat))"
  by (simp add: da_H_def)
    
lemma ubundle_if_eq:
  "Abs_ubundle (\<lambda>x::channel. if x \<in> dom sb then sb x else None) = Abs_ubundle sb"
  by (metis domIff)

lemma ubconceq_ubleast:
  assumes "ubDom\<cdot>(sb::('m::message  SB)) = c" 
  shows "ubConcEq (sb)\<cdot>(ubclLeast c) =  sb"
  proof-
    have ubdom_intersec:"(ubDom\<cdot>sb \<union> c) \<inter> c = c"
      by auto
    have if_if:" (\<lambda>x::channel. if x \<in> ubDom\<cdot>sb then if x \<in> ubDom\<cdot>sb then Rep_ubundle sb x else Some \<epsilon> else None) = 
            (\<lambda>x::channel. if x \<in> ubDom\<cdot>sb then Rep_ubundle sb x else None)"
      by auto
    have ubundle_if_eq2:"Abs_ubundle (\<lambda>x::channel. if x \<in> ubDom\<cdot>sb then Rep_ubundle sb x else None) = sb"    
      by (metis (no_types) assms ubundle_if_eq ubabs_ubrep ubdom_insert)
    have ubundle_if_eq3:"Abs_ubundle (\<lambda>x::channel. if x \<in> c then if x \<in> ubDom\<cdot>sb then Rep_ubundle sb x else Some \<epsilon> else None) = sb"
      by (fold assms, simp add: if_if ubundle_if_eq2)
    have if_bundle_neq:"\<And>x::channel. (if x \<in> ubDom\<cdot>sb then Rep_ubundle sb x else Some \<epsilon>) \<noteq> None"
      by (metis assms option.simps(3) ubgetchE)
    have bundle_restrict_eq:"Abs_ubundle ((\<lambda>c::channel. Some Rep_ubundle (ubUp\<cdot>sb)\<rightharpoonup>c) |` c) = sb"
      by (simp add: ubup_insert restrict_map_def, subst option.collapse,  
          simp add: if_bundle_neq, simp add: ubundle_if_eq3)
    have bundle_restrict_eq2:"Abs_ubundle (Rep_ubundle (Abs_ubundle (\<lambda>c::channel. Some (ubUp\<cdot>sb  .  c))) |` c) = sb"
      by (simp add: ubWell_def ubgetch_insert ubrestrict_insert bundle_restrict_eq)
    show ?thesis
      by (simp add: ubclLeast_ubundle_def ubconc_insert ubdom_intersec
         ubrestrict_insert usclConc_stream_def bundle_restrict_eq2)
  qed
    
lemma da_H_bottom:
  assumes dadom_automat: "daDom automat = c"
    and datom_automat_nempty: "\<exists>c::channel. c \<in> daDom automat" 
    and "ubDom\<cdot>(daInitialOutput automat) = daRan automat"
  shows "da_H automat \<rightleftharpoons> ubclLeast c = daInitialOutput automat"
  apply (simp add: da_H_unfolding)
  apply (subst spfConcOut_step)
  apply (simp add: ubclLeast_ubundle_def assms)
  apply (subst da_h_bottom)
  apply (simp add: ubclLeast_ubundle_def assms)
  apply (simp add: ubclLeast_ubundle_def assms)
  apply (fold dadom_automat, simp add: datom_automat_nempty)
  by (subst ubconceq_ubleast,simp_all add: assms)

end