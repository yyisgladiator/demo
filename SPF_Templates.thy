(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: commonly used SPF definitions and lemmas
*)

theory SPF_Templates
  imports SPF SBTheorie
    
begin

(* ----------------------------------------------------------------------- *)
section \<open>Identity\<close>
(* ----------------------------------------------------------------------- *)  
  
definition sb_id :: "nat stream \<rightarrow> nat stream" where
"sb_id \<equiv> \<Lambda> x . x"

definition idSPF :: "(channel \<times> channel) \<Rightarrow> nat SPF" where
"idSPF cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs) \<mapsto> sb_id\<cdot>(sb . (fst cs))]\<Omega>))"

lemma spf_sb_id_mono[simp] : "monofun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>))"
  apply (rule spf_mono2monofun)
  apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
  apply(simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  apply(meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  apply rule
  by(simp add: domIff2)

lemma sb_id_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> sb_id\<cdot>(Y i . ch1)]\<Omega>)"
  apply(rule chainI)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma sb_id_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> sb_id\<cdot>((Y i) . ch1)]\<Omega>)"
  by (simp  add: sbChain_dom_eq2)

lemma spf_sb_id_chain[simp]: "chain Y \<Longrightarrow> chain(\<lambda> i. (sbDom\<cdot>(Y i) = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>((Y i) . ch1)]\<Omega>))"
  apply(rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply(rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma spf_sb_id_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> (\<Squnion>i. sb_id\<cdot>(Y i . c1)) = sb_id\<cdot>((Lub Y) . c1)"
  by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma spf_sb_id_cont[simp] : "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_cont2cont)
 apply(rule spf_contlubI)
  apply(simp add: domIff2 sbChain_dom_eq2)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply(simp only: Cfun.contlub_cfun_arg sb_id_chain_lub)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
    apply(simp add: contlub_cfun_arg)
   apply (simp add: monofun2spf_mono)
  apply(simp add: domIff2)
  by rule+ 

lemma spf_sb_id_well[simp] : "spf_well (Abs_cfun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) 
                                                  \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>)))"  
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by(auto)    


lemma test2: "snd (ch1, ch2) = ch2"
  by simp
    
subsection \<open>idSPF lemmata\<close>

lemma idSPF_rep_eq_C: "Rep_CSPF (idSPF (ch1, ch2)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1,ch2))}) 
                                        \<leadsto> ([(snd (ch1,ch2)) \<mapsto> sb_id\<cdot>(sb . (fst (ch1,ch2)))]\<Omega>))"
  apply(simp add: idSPF_def)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  by simp
      
lemma idSPF_dom[simp]: "spfDom\<cdot>(idSPF (ch1, ch2)) = {ch1}"
  apply(simp add: idSPF_def, subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(simp add: spfdom_insert idSPF_rep_eq_C)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)
    
lemma idSPF_ran[simp]: "spfRan\<cdot>(idSPF (ch1, ch2)) = {ch2}"
  apply(simp add: spfran_least)
  apply(simp add: idSPF_def, subst Product_Type.snd_conv, subst Product_Type.fst_conv, simp)
  by(simp add: spfran_least sbdom_insert)
    
lemma idSPF_apply: "(idSPF (ch1, ch2)) \<rightleftharpoons> ([ch1 \<mapsto> s]\<Omega>) = ([ch2 \<mapsto> (s:: nat stream)]\<Omega>)"
  apply(simp add: idSPF_rep_eq_C  sb_id_def  sbgetch_insert)
  by(simp add: sbdom_rep_eq)


    
(* For further lemmas see SerComp or ParComp *) 
    
(* ----------------------------------------------------------------------- *)
section \<open>add_componentwise\<close>
(* ----------------------------------------------------------------------- *) 

(* add SPF *)

definition addSPF :: "(channel \<times> channel \<times> channel) \<Rightarrow> nat SPF" where
"addSPF cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"

lemma addSPF_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma add_chain: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {(fst cs), (fst (snd cs))} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma addSPF_chain_lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (fst (snd cs))} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>)"
  by (simp add: sbChain_dom_eq2 add_chain)

lemma addSPF_Lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (fst (snd cs))} \<Longrightarrow> 
  (\<Squnion>i. add\<cdot>(Y i . (fst cs))\<cdot>(Y i . (fst (snd cs)))) = add\<cdot>((Lub Y) . (fst cs))\<cdot>((Lub Y). (fst (snd cs)))"
  by (simp add: lub_distribs(1) lub_eval)

(*
lemma addSPF_chain: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
*)

lemma addSPF_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg addSPF_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub addSPF_chain_lub addSPF_Lub)
proof -
  have "monofun (\<lambda>s. (sbDom\<cdot>s = {fst cs, fst (snd cs)})\<leadsto>[snd (snd cs) \<mapsto> add\<cdot>(s . fst cs)\<cdot> (s . fst (snd cs))]\<Omega>)"
    using addSPF_mono by presburger
  then show "spf_mono (\<lambda>s. (sbDom\<cdot>s = {fst cs, fst (snd cs)})\<leadsto>[snd (snd cs) \<mapsto> add\<cdot>(s . fst cs)\<cdot> (s . fst (snd cs))]\<Omega>)"
    using monofun2spf_mono by blast
next
   show "\<forall>b. (b \<in> dom (\<lambda>sb. (sbDom\<cdot>sb = {fst cs, fst (snd cs)})\<leadsto>[snd (snd cs) \<mapsto> add\<cdot>(sb . fst cs)\<cdot>(sb . fst (snd cs))]\<Omega>)) 
                = (sbDom\<cdot>b = {fst cs, fst (snd cs)})" 
     by (simp add: domIff)
qed

lemma addSPF_well: "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> 
  ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  apply(simp add: spf_well_def addSPF_cont)
  apply(simp add: domIff2)
  by(auto simp add:  sbdom_rep_eq)

lemma addSPF_rep_eqC: "Rep_CSPF (addSPF cs) = 
  (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
apply(simp add: addSPF_def add2_def)
apply(subst rep_abs_cspf)
by(simp_all add: addSPF_cont addSPF_well)

    
(* ----------------------------------------------------------------------- *)
section \<open>mult_componentwise\<close>
(* ----------------------------------------------------------------------- *) 
(* multiplies 2 nat - streams component-wise *)
definition mult:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"mult \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) * (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"

definition multSPF :: "(channel \<times> channel \<times> channel) \<Rightarrow> nat SPF" where
"multSPF cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>mult\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"

(* multiplication component *)
lemma spfmult_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma mult_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1,ch2} 
                        \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>mult\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma mult_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} 
                                \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>mult\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma mult_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} \<Longrightarrow> 
  (\<Squnion>i. mult\<cdot>(Y i . ch1)\<cdot>(Y i . ch2)) = mult\<cdot>((Lub Y) . ch1)\<cdot>((Lub Y). ch2)"
proof -
  assume a1: "chain Y"
  have f2: "\<forall>f fa. (\<not> chain f \<or> \<not> chain fa) \<or> (\<Squnion>n. (f n\<cdot>(fa n::nat stream)::nat stream)) = Lub f\<cdot>(Lub fa)"
    using lub_APP by blast
  have f3: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat stream)::nat stream \<rightarrow> nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  have f4: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat SB)::channel \<rightarrow> nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  have "\<forall>f c. \<not> chain f \<or> (Lub f\<cdot>(c::channel)::nat stream) = (\<Squnion>n. f n\<cdot>c)"
    using contlub_cfun_fun by blast
  then have "(\<Squnion>n. mult\<cdot>(Y n . ch1)\<cdot>(Y n . ch2)) = mult\<cdot>(Lub Y . ch1)\<cdot>(Lub Y . ch2)"
    using f4 f3 f2 a1 by simp
  then show ?thesis
    by force
qed

lemma spfmult_cont[simp]: "cont 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg mult_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2spf_mono)
  by(simp add: domIff2, rule+)
    

lemma spfmult_well[simp] : "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply(simp add: spf_well_def)
  apply(simp add: domIff2)
  by(auto simp add: sbdom_rep_eq)
 
    
    
subsection \<open>multSPF lemmata\<close>
(* LEMMAS below work if spfmult_well is proven *)
  
  (*
lemma multSPF_rep_eq_C: "Rep_CSPF (multSPF (ch1, ch2, ch3)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1, ch2, ch3)), (fst (snd (ch1, ch2, ch3)))}) \<leadsto> ([(snd (snd (ch1, ch2, ch3)))\<mapsto>mult\<cdot>(sb . (fst (ch1, ch2, ch3)))\<cdot>(sb . (fst (snd (ch1, ch2, ch3))))]\<Omega>))"
  apply(simp add: multSPF_def)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv, subst Product_Type.snd_conv, subst Product_Type.fst_conv, subst Product_Type.snd_conv, subst Product_Type.snd_conv)
  by simp
      
lemma multSPF_dom[simp]: "spfDom\<cdot>(multSPF (ch1, ch2, ch3)) = {ch1, ch2}"
  apply(simp add: multSPF_def, subst Product_Type.snd_conv, subst Product_Type.fst_conv, subst Product_Type.snd_conv, subst Product_Type.fst_conv, subst Product_Type.snd_conv)
  apply(simp add: spfdom_insert idSPF_rep_eq_C)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)
    
lemma multSPF_ran[simp]: "spfRan\<cdot>(multSPF (ch1, ch2, ch3)) = {ch3}"
  apply(simp add: spfran_least)
  apply(simp add: multSPF_def, subst Product_Type.snd_conv, subst Product_Type.fst_conv, subst Product_Type.snd_conv, subst Product_Type.fst_conv, subst Product_Type.snd_conv, simp)
  by(simp add: spfran_least sbdom_insert)
    
lemma multSPF_apply: "(multSPF (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) = ([ch3 \<mapsto> (mult\<cdot>s1\<cdot>s2)]\<Omega>)"
  apply(simp add: multSPF_rep_eq_C sb_id_def sbgetch_insert)
  apply(simp add: sbdom_rep_eq)
  oops
    *)

end