(*  Title:        Medium.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Medium Component of the ABP on Timed Streams
*)

chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium_DS
imports "../../TStream" Medium

begin
default_sort countable

lemma sprojsnd_srcdups:
  "#(srcdups\<cdot>s) \<noteq> \<infinity> \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s)
     \<Longrightarrow> srcdups\<cdot>(sprojsnd\<cdot>s) = sprojsnd\<cdot>(srcdups\<cdot>s)"
(*
  apply (induction s rule: ind, simp_all)
  apply (rule adm_imp, rule admI)
  apply (simp add: contlub_cfun_arg)
  apply (rule admI, auto)
  apply (simp add: contlub_cfun_arg)
*)
  proof(induction s rule: ind)
    case 1
    then show ?case
    proof (rule admI, auto)
      fix Y :: "nat \<Rightarrow> ('a \<times> 'b) stream"
      assume chy: "chain Y" and
         as1: "\<forall>i. #(srcdups\<cdot>(Y i)) \<noteq> \<infinity> \<longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(Y i))) = #(srcdups\<cdot>(Y i)) \<longrightarrow> srcdups\<cdot>(sprojsnd\<cdot>(Y i)) = sprojsnd\<cdot>(srcdups\<cdot>(Y i))"
         and as2: "#(srcdups\<cdot>(\<Squnion>i::nat. Y i)) \<noteq> \<infinity>"
         and as3: "#(srcdups\<cdot>(sprojsnd\<cdot>(\<Squnion>i::nat. Y i))) = #(srcdups\<cdot>(\<Squnion>i::nat. Y i))"
         have h1: "\<And>i. #(srcdups\<cdot>(Y i)) \<noteq> \<infinity>"
           by (metis as2 chy inf_less_eq is_ub_thelub lnle_conv monofun_cfun_arg)
         have "\<And>i. #(srcdups\<cdot>(sprojsnd\<cdot>(Y i))) = #(srcdups\<cdot>(Y i))"  sorry
         thus "srcdups\<cdot>(sprojsnd\<cdot>(\<Squnion>i::nat. Y i)) = sprojsnd\<cdot>(srcdups\<cdot>(\<Squnion>i::nat. Y i))"
           by (smt as1 ch2ch_Rep_cfunR chy contlub_cfun_arg h1 lub_eq)
      qed
  next
    case 2
    then show ?case by simp
  next 
    case (3 a s)
    then show ?case
      apply (cases rule: scases [of s])
      apply (cases a,simp)
      apply (cases a,simp)
      apply (case_tac aa,simp) 
      apply (case_tac "b=ba")
      apply (case_tac "(aaa,b) = (ab,ba)")  
      apply simp_all
  by (metis antisym_conv2 inf_ub le2lnle order_refl slen_sprojsnd sprojsnd_scons sprojsnd_srcdups_slen)
  qed
 
end