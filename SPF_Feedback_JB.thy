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
  
definition spfFeedHelp:: "'m SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfFeedHelp f1 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f1))))"

abbreviation iter_spfFeedHelp:: "'m SPF \<Rightarrow> nat \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_spfFeedHelp f1 i \<equiv> (\<lambda> x. iterate i\<cdot>(spfFeedHelp f1 x)\<cdot>((spfRan\<cdot>f1)^\<bottom>))"

    
(* ----------------------------------------------------------------------- *)
section \<open>spfFeedHelp\<close>
(* ----------------------------------------------------------------------- *)

  
end