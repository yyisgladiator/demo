(*  Title:  SPF_ParComp_CaseStudy.thy
    Author: Marc Wiartalla
    e-mail: Marc.Wiartalla@rwth-aachen.de

    Description: Show that the parallel composition of two ID functions is again the ID function on each output channel
*)

theory SPF_ParComp_CaseStudy
  
imports  "../SPF_Comp"
  
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>component instantiation\<close>
(* ----------------------------------------------------------------------- *)
  
definition ID1 :: "nat SPF" where
"ID1 = SPF1x1 sb_id (c1,c2)"

definition ID2 :: "nat SPF" where
"ID2 = SPF1x1 sb_id (c3,c4)"
    

subsection \<open>ID component properties\<close>
  
lemma [simp]: "spfDom\<cdot>ID1 = {c1}"
  by (simp add: ID1_def)

lemma [simp]: "spfRan\<cdot>ID1 = {c2}"
  by (simp add: ID1_def)

lemma [simp]: "spfDom\<cdot>ID2 = {c3}"
  by (simp add: ID2_def)

lemma [simp]: "spfRan\<cdot>ID2 = {c4}"
  by (simp add: ID2_def)


lemma id_apply1: "(ID1 \<rightleftharpoons> ([c1 \<mapsto> s]\<Omega>)) = ([c2 \<mapsto> (s:: nat stream)]\<Omega>)"
  by (simp add: ID1_def idSPF_apply spf1x1_sb_id_eq)

lemma id_apply2: "(ID2 \<rightleftharpoons> ([c3 \<mapsto> s]\<Omega>)) = ([c4 \<mapsto> (s:: nat stream)]\<Omega>)"
  by (simp add: ID2_def idSPF_apply spf1x1_sb_id_eq)

lemma sbUnion_eq: "([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>) = ([c1 \<mapsto> (s:: nat stream)]\<Omega>) \<uplus> ([c3 \<mapsto> (s2:: nat stream)]\<Omega>)"
proof - 
  have f1: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream)]\<Omega>) = {c1}"
    by(subst sbdom_rep_eq, simp_all)
  have f2: "sbDom\<cdot>([c3 \<mapsto> (s2:: nat stream)]\<Omega>) = {c3}"
    by(subst sbdom_rep_eq, simp_all)
  have f3: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>) = {c1,c3}"
    apply(subst sbdom_rep_eq, simp_all)
    by auto
  show ?thesis
    apply(subst sb_eq, simp_all)
     apply(auto simp add: f1 f2 f3)
     apply(subst sbgetch_rep_eq, simp_all)
      by(subst sbgetch_rep_eq, simp_all)
qed
    
lemma sb_restrict_eq1: "([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>)\<bar>{c1} = ([c1 \<mapsto> (s:: nat stream)]\<Omega>)" 
proof - 
  have f1: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream)]\<Omega>) = {c1}"
    by(subst sbdom_rep_eq, simp_all)
  have f2: "sbDom\<cdot>([c3 \<mapsto> (s2:: nat stream)]\<Omega>) = {c3}"
    by(subst sbdom_rep_eq, simp_all)
  have f3: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>) = {c1,c3}"
    apply(subst sbdom_rep_eq, simp_all)
    by auto
  show ?thesis
     apply(subst sb_eq, simp_all)
     apply(simp add: f1 f3)
     by (simp add: f1 f2 sbUnion_eq)  
qed   

lemma sb_restrict_eq2: "([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>)\<bar>{c3} = ([c3 \<mapsto> (s2:: nat stream)]\<Omega>)" 
proof - 
  have f1: "sbDom\<cdot>([c3 \<mapsto> (s2:: nat stream)]\<Omega>) = {c3}"
    by(subst sbdom_rep_eq, simp_all)
  have f2: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>) = {c1,c3}"
    apply(subst sbdom_rep_eq, simp_all)
    by auto
  show ?thesis
     apply(subst sb_eq, simp_all)
     apply(simp add: f1 f2)
     by (simp add: f1 sbUnion_eq)  
qed    
      
(* ----------------------------------------------------------------------- *)
section \<open>component prerequirements\<close>
(* ----------------------------------------------------------------------- *)
  
lemma [simp]: "spfComp_well ID1 ID2"
  by (simp add: spfComp_well_def)

lemma[simp]: "no_selfloops ID1 ID2"
  by(simp add: no_selfloops_def)

lemma [simp]: "C ID1 ID2 = {c1,c2,c3,c4}"
  by (simp add: C_def, blast)

lemma [simp]: "L ID1 ID2 = {}"
  by (simp add: L_def)

lemma [simp]: "Oc ID1 ID2 = {c2,c4}"
  by (simp add: Oc_def, blast)

lemma [simp]: "I ID1 ID2 = {c1,c3}"
  by auto

lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream), c3 \<mapsto> (s2:: nat stream)]\<Omega>) = I ID1 ID2"
  by(simp add: sbdom_rep_eq, auto)   
  

(* ----------------------------------------------------------------------- *)
section \<open>result\<close>
(* ----------------------------------------------------------------------- *)
  
lemma spfParComp_spfID : "(((spfcomp ID1 ID2) \<rightleftharpoons> ([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>)) . c2)  =  s"
  apply (simp add: spfCompParallelGetch1)
  by(simp add: sb_restrict_eq1 id_apply1)
    
lemma spfParComp_spfID2 : "(((spfcomp ID1 ID2) \<rightleftharpoons> ([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>)) . c4)  =  s2"
  apply (simp add: spfCompParallelGetch2)
   by(simp add: sb_restrict_eq2 id_apply2)


  
end