(*  Title:  SPF_FeedComp.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: This is a usage scenario for the SPF_FeedComp_Theory
                 to show the power of the combined Template, Comp and FeedComp theories
*)

theory SPF_FeedComp_JB
  (* check if StreamCase_Study is really necessary *)
  imports "../SPF_FeedComp" StreamCase_Study
begin
  

    
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)

definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c1, c2, c3)" 
  
definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c3,c2)"

(* use new definition of composition and leave out hide as it is not production ready yet *)
(* sum1EqCh can be used later when hide is introduced *)
definition s1SPF :: "nat SPF" where
"s1SPF \<equiv> spfcomp2 addC append0C"


    

  (* FINAL lemma *)
lemma sum4_sb_spf_eq: assumes "sb = ([c1 \<mapsto> s]\<Omega>)"
  shows "sum4\<cdot>s = (\<Squnion>i. (iter_spfCompH3 addC append0C i) sb) .c3"
proof -
  have f1: "sum4\<cdot>s = (gen_fix add (appendElem2 0))\<cdot>s"
    by (simp add: sum4_def appendElem2_def fix_def)
      
  thus ?thesis
    apply(subst f1) 
    apply (rule gen_fix_iter_spfComp_eq)
      by (simp_all add: assms addC_def append0C_def)
qed
    
end