(*  Title:  SPF_FeedComp.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: lemmas for feedback composition with the genranal composition operator
*)

theory SPF_FeedComp_JB
  (* check if StreamCase_Study is really necessary *)
  imports Streams SB SPF SPF_Composition_JB  ParComp_MW_JB SerComp_JB SPF_Templates SPF_MW "CaseStudies/StreamCase_Study"
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)

definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c1, c2, c3)" 
  
definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c3,c2)"

(* use new definition of composition and leave out hide as it is not production ready yet *)
definition s1SPF :: "nat SPF" where
"s1SPF \<equiv> spfcomp2 addC append0C"


subsection \<open>component properties\<close>
  (* spf_well and cont proofs left out *)
  
lemma addC_dom [simp]: "spfDom\<cdot>addC = {c1,c2}"
  by (simp add: addC_def)
    
lemma addC_ran [simp]: "spfRan\<cdot>addC = {c3}"
  by (simp add: addC_def)
    
lemma addC_rep_eq: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
  by (simp add: addC_def SPF2x1_rep_eq, auto)
    
lemma addC_apply: "addC \<rightleftharpoons> ([c1 \<mapsto> (s1:: nat stream), c2  \<mapsto> (s2:: nat stream)]\<Omega>) = ([c3 \<mapsto> (add\<cdot>s1\<cdot>s2)]\<Omega>)"
  by(simp add: addC_def SPF2x1_apply)
    
(* append0C *)
lemma append0C_dom [simp]: "spfDom\<cdot>append0C = {c3}"
  by (simp add: append0C_def)
    
lemma append0C_ran [simp]: "spfRan\<cdot>append0C = {c2}"
  by (simp add: append0C_def)
    
lemma append0C_rep_eq: "Rep_CSPF append0C = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>((appendElem2 0)\<cdot>(sb . c3))]\<Omega>))"
  by (simp add: append0C_def SPF1x1_rep_eq, auto)
    
lemma append0C_apply: "append0C \<rightleftharpoons> ([c3 \<mapsto> s]\<Omega>) = ([c2 \<mapsto> (appendElem2 0)\<cdot>(s:: nat stream)]\<Omega>)"
  by(simp add: append0C_def SPF1x1_apply)
  
end
  

