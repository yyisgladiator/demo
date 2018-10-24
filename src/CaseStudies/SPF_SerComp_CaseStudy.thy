(*  Title:  SPF_SerComp_CaseStudy.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: Show that the serial composition of two ID functions is again the ID function
*)

theory SPF_SerComp_CaseStudy
  
imports  "../SPF_Comp"
  
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>component instantiation\<close>
(* ----------------------------------------------------------------------- *)
  
definition ID1 :: "nat SPF" where
"ID1 = SPF1x1 sb_id (c1,c2)"

definition ID2 :: "nat SPF" where
"ID2 = SPF1x1 sb_id (c2,c3)"
    

subsection \<open>ID component properties\<close>
  
lemma [simp]: "spfDom\<cdot>ID1 = {c1}"
  by (simp add: ID1_def)

lemma [simp]: "spfRan\<cdot>ID1 = {c2}"
  by (simp add: ID1_def)

lemma [simp]: "spfDom\<cdot>ID2 = {c2}"
  by (simp add: ID2_def)


lemma [simp]: "spfRan\<cdot>ID2 = {c3}"
  by (simp add: ID2_def)


lemma id_apply1: "(ID1 \<rightleftharpoons> ([c1 \<mapsto> s]\<Omega>)) = ([c2 \<mapsto> (s:: nat stream)]\<Omega>)"
  by (simp add: ID1_def idSPF_apply spf1x1_sb_id_eq)

lemma id_apply2: "(ID2 \<rightleftharpoons> ([c2 \<mapsto> s]\<Omega>)) = ([c3 \<mapsto> (s:: nat stream)]\<Omega>)"
  by (simp add: ID2_def idSPF_apply spf1x1_sb_id_eq)

    
(* ----------------------------------------------------------------------- *)
section \<open>component prerequirements\<close>
(* ----------------------------------------------------------------------- *)
  
lemma [simp]: "spfComp_well ID1 ID2"
  by (simp add: spfComp_well_def)

lemma[simp]: "no_selfloops ID1 ID2"
  by(simp add: no_selfloops_def)

lemma [simp]: "C ID1 ID2 = {c1,c2,c3}"
  by (simp add: C_def, blast)

lemma [simp]: "L ID1 ID2 = {c2}"
  by (simp add: L_def)

lemma [simp]: "Oc ID1 ID2 = {c2,c3}"
  by (simp add: Oc_def, blast)

lemma [simp]: "I ID1 ID2 = {c1}"
  by (simp add: I_def)

lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream)]\<Omega>) = I ID1 ID2"
  by(simp add: sbdom_rep_eq)
    
lemma [simp]:"pL ID1 ID2 = {}"
  by(simp add: pL_def)
  

(* ----------------------------------------------------------------------- *)
section \<open>result\<close>
(* ----------------------------------------------------------------------- *)
    
lemma spfSerComp_spfID : "(((spfcomp ID1 ID2) \<rightleftharpoons> ([c1 \<mapsto> s]\<Omega>)) . c3)  =  s"
  apply (simp add: spfCompSeriellGetch)
  by (simp add: id_apply1 id_apply2)


  
end