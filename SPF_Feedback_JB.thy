(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: production ready lemmata for the feedback operator
                 based on Feedback_MW
*)

theory SPF_Feedback_JB
imports Streams SB SPF ParComp_MW_JB SerComp_JB SPF_Templates SPF_MW SPF_Composition_JB
    
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)
  
(* definition from Feedback_MW *)
definition spfFeedbackOperator :: "'a SPF \<Rightarrow> 'a SPF" ("\<mu>_" 50) where
"spfFeedbackOperator f \<equiv>
let I  = spfDom\<cdot>f - spfRan\<cdot>f;
    I1 = spfDom\<cdot>f;
    C  = spfRan\<cdot>f
in Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = I) \<leadsto>
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>((sb \<uplus> z)\<bar> I1)))\<cdot>(C^\<bottom>)))" 
  
definition spfFeedH:: "'m SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"

abbreviation iter_spfFeedH:: "'m SPF \<Rightarrow> nat \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_spfFeedH f i \<equiv> (\<lambda> x. iterate i\<cdot>(spfFeedH f x)\<cdot>((spfRan\<cdot>f)^\<bottom>))"

    
lemma spfFeedbackOperator2_iter_spfFeedH: 
shows "(spfFeedbackOperator f) = Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto>
                                              (\<Squnion>i. (iter_spfFeedH f i) sb))"
  apply(simp add: spfFeedbackOperator_def)
  apply(subst spfFeedH_def)
    by simp

(* ----------------------------------------------------------------------- *)
section \<open>spfFeedHelp\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>cont\<close>

lemma spfFeedH_cont[simp]: "cont (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
proof -
  have f1:"cont (\<lambda>z. (Rep_cfun (Rep_SPF f))\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f))"
   by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  thus ?thesis
    by(simp add: Rep_CSPF_def)
qed
  
lemma spfFeedH_cont2[simp]: "cont (\<lambda> x. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
proof -
  have f1: "cont (\<lambda>x. (x \<uplus> z))" (* really important line *)
    by simp
  hence f2:"cont (\<lambda>x. (Rep_cfun (Rep_SPF f))\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f))"
   by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  thus ?thesis
    by(simp add: Rep_CSPF_def)
qed
  
lemma spfFeedH_mono[simp]: "monofun (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
  using cont2mono spfFeedH_cont by blast

    
lemma spfFeedH_continX[simp]: "cont (\<lambda> x. spfFeedH f x)"
proof -
  have "cont (\<lambda>x. \<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"
    by(simp add: cont2cont_LAM)
  thus ?thesis
    by(simp add: spfFeedH_def)
qed
  
subsection \<open>dom\<close>
  
lemma spfFeedH_dom [simp]: assumes "sbDom\<cdot>x = spfDom\<cdot>f - spfRan\<cdot>f" 
                           and "sbDom\<cdot>sb = spfRan\<cdot>f"
shows "sbDom\<cdot>((spfFeedH f x)\<cdot>sb) = (spfRan\<cdot>f)"
  by (simp add: spfFeedH_def assms(1) assms(2))


(* ----------------------------------------------------------------------- *)
section \<open>iter_spfFeedH\<close>
(* ----------------------------------------------------------------------- *) 
    
lemma iter_spfFeedH_cont[simp]: "cont (\<lambda>x. iter_spfFeedH f i x)"
  by simp

lemma iter_spfFeedH_mono[simp]: "monofun (\<lambda>x. iter_spfFeedH f i x)"
  by (simp add: cont2mono)
    
lemma iter_spfFeedH_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_spfFeedH f i) x) \<sqsubseteq> ((iter_spfFeedH f i) y)"
  using assms monofun_def by fastforce
    
lemma iter_spfFeedH_chain[simp]: assumes "sbDom\<cdot>x =  spfDom\<cdot>f - spfRan\<cdot>f"
  shows "chain (\<lambda>i. iter_spfFeedH f i x)"
  apply(rule sbIterate_chain)
  by(simp add: assms)
    
    
(* ----------------------------------------------------------------------- *)
section \<open>lub_iter_spfFeedH\<close>
(* ----------------------------------------------------------------------- *) 
  
subsection \<open>mono\<close> 
  
  
lemma lub_iter_spfFeedH_mono_req:  assumes "x \<sqsubseteq> y" and  "sbDom\<cdot>x =  (spfDom\<cdot>f - spfRan\<cdot>f)"
  shows "(\<Squnion>i.(iter_spfFeedH f i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfFeedH f i) y)"
proof -
  have "\<forall>i. ((iter_spfFeedH f i) x) \<sqsubseteq> ((iter_spfFeedH f i) y)"
    by (simp add: iter_spfFeedH_mono2 assms)
  moreover
  have "sbDom\<cdot>x = sbDom\<cdot>y"
    using assms(1) sbdom_eq by auto
  ultimately
  show ?thesis
    by(simp add: lub_mono  iter_spfFeedH_mono2 assms)
qed
  
lemma if_lub_iter_spfFeedH_mono_req: assumes "x \<sqsubseteq> y"
  shows "((\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x)) x)
         \<sqsubseteq> ((\<lambda> x. (sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto> (\<Squnion>i.(iter_spfFeedH f i) x)) y)"
proof (cases "sbDom\<cdot>x = (spfDom\<cdot>f - spfRan\<cdot>f)")
  case True
  have "\<forall>i. ((iter_spfFeedH f i) x) \<sqsubseteq> ((iter_spfFeedH f i) y)"
    by (simp add: iter_spfFeedH_mono2 assms)
  moreover
  have f1: "sbDom\<cdot>x = sbDom\<cdot>y"
    using assms(1) sbdom_eq by auto
  ultimately
  have "(\<Squnion>i.(iter_spfFeedH f i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfFeedH f i) y)"
    using True assms lub_iter_spfFeedH_mono_req by blast
  thus ?thesis
    using f1 some_below by auto
next
  case False
  have "sbDom\<cdot>y = sbDom\<cdot>x"
    by (metis assms(1) sbdom_eq)
  thus ?thesis     
    by (simp add: False some_below)
qed

  
subsection \<open>cont\<close>  
  
lemma chain_lub_iter_spfFeedH: assumes "chain Y" and  "(sbDom\<cdot>(\<Squnion>i. Y i) =  (spfDom\<cdot>f - spfRan\<cdot>f))"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_spfFeedH f ia (Y i))"
proof -
  have f1: "\<forall>i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms po_class.chain_def by blast
  have f2: "\<forall>ia. sbDom\<cdot>(Y ia) = (spfDom\<cdot>f - spfRan\<cdot>f)"
    by (simp add: assms(1) assms(2) sbChain_dom_eq2)
  thus ?thesis
    apply(subst chainI, simp_all add: assms)
    by (simp add: f1 lub_iter_spfFeedH_mono_req)
qed
  
  
  
  
  
  
end