(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: aggregates commonly used SPF patterns with constructors
    To instantiate a SPF use the SPF1x1, SPF2x1 definition with an appropriate function which 
    automatically proves cont, spf_well, dom, range for your definition
*)

theory SPF_Templates
  imports SPF SB
    
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>Definitions\<close>
(* ----------------------------------------------------------------------- *)

(* Identity funciton for nat streams *)  
definition sb_id :: "nat stream \<rightarrow> nat stream" where
"sb_id \<equiv> \<Lambda> x . x"

definition appendElem:: "nat \<Rightarrow> nat stream \<Rightarrow> nat stream" where
"appendElem a s = \<up>a \<bullet> s"

definition appendElem2:: "'a \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"appendElem2 a \<equiv> \<Lambda> s. \<up>a \<bullet> s" 

(* multiplies 2 nat - streams component-wise *)
definition mult:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"mult \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) * (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"


subsubsection \<open>1x1 SPF definitions\<close>
(* general 1x1 SPF constructor with one input and one output channel *)
definition SPF1x1 :: "(nat stream \<rightarrow> nat stream) \<Rightarrow> (channel \<times> channel) \<Rightarrow> nat SPF" where
"SPF1x1 f cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs)}) 
                             \<leadsto> ([(snd cs) \<mapsto> f\<cdot>(sb . (fst cs))]\<Omega>))"

(* Special case 1x1 SPF *)
definition idSPF :: "(channel \<times> channel) \<Rightarrow> nat SPF" where
"idSPF cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs)}) 
                             \<leadsto> ([(snd cs) \<mapsto> sb_id\<cdot>(sb . (fst cs))]\<Omega>))"

definition appendSPF :: "(channel \<times> channel) \<Rightarrow> nat \<Rightarrow> nat SPF" where
"appendSPF cs a \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) 
                             \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"

subsubsection \<open>2x1 SPF definitions\<close>
  
(* general 2x1 SPF constructor with one input and one output channel *)
definition SPF2x1 :: "(nat stream \<rightarrow> nat stream \<rightarrow> nat stream) \<Rightarrow>  (channel \<times> channel \<times> channel) 
                      \<Rightarrow> nat SPF" where
"SPF2x1 f cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) 
                          \<leadsto> ([(snd (snd cs))\<mapsto>f\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"

definition addSPF :: "(channel \<times> channel \<times> channel) \<Rightarrow> nat SPF" where
"addSPF cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) 
                          \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"

definition multSPF :: "(channel \<times> channel \<times> channel) \<Rightarrow> nat SPF" where
"multSPF cs \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) 
                          \<leadsto> ([(snd (snd cs))\<mapsto>mult\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"



(* ----------------------------------------------------------------------- *)
section \<open>1x1 SPF\<close>
(* ----------------------------------------------------------------------- *)  
  
(* In this section it is shown that general SPFs with one input and one output( = f(input)) are
    in fact SPFs *)
  

subsection \<open>SPF1x1 prerequirements\<close>
(* The following lemma are all prerequirements for 1x1SPF *)
  
lemma spf_1x1_general_spfmono[simp]: 
  shows "monofun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)\<cdot>(sb . ch1)]\<Omega>))"
  apply (rule spf_mono2monofun)
  apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
  apply(simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  apply(meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  apply rule
  by(simp add: domIff2)
    
lemma spf_1x1_general_chain1[simp]:
  shows "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)
    \<cdot>(Y i . ch1)]\<Omega>)"
     apply(rule chainI)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    
lemma spf_1x1_general_chain_lub[simp]: 
  shows "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)
          \<cdot>((Y i) . ch1)]\<Omega>)"
  by (simp  add: sbChain_dom_eq2)
    
lemma spf_1x1_general_chain2: "chain Y \<Longrightarrow> chain(\<lambda> i. (sbDom\<cdot>(Y i) = {ch1}) 
  \<leadsto> ([ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)\<cdot>((Y i) . ch1)]\<Omega>))"
  apply(rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply(rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)
    
lemma spf_1x1_general_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> 
  (\<Squnion>i. (f::nat stream \<rightarrow> nat stream)\<cdot>(Y i . c1)) = (f::nat stream \<rightarrow> nat stream)\<cdot>((Lub Y) . c1)"
  by (simp add: contlub_cfun_arg contlub_cfun_fun)

(* As the general 1x1 SPF is monotone and has the appropriate lub properties we can show that it is
  in fact a continous function *)
lemma spf_1x1_general_cont[simp] : "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) 
  \<leadsto> ([ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_cont2cont)
 apply(rule spf_contlubI)
  apply(simp add: domIff2 sbChain_dom_eq2)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply(simp only: Cfun.contlub_cfun_arg spf_1x1_general_chain_lub)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
    apply(simp add: contlub_cfun_arg)
   apply (simp add: monofun2spf_mono)
  apply(simp add: domIff2)
  by rule+ 

(* As the general 1x1 SPF is continous and has fixed input and output channels it is an spf *)
lemma spf_1x1_general_well[simp] : "spf_well (Abs_cfun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) 
                                          \<leadsto> ([ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)\<cdot>(sb . ch1)]\<Omega>)))"  
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by(auto)  

(* Now explicitly show the domain properties of the general 1x1 SPF *)
lemma spf_1x1_general_dom[simp]: "spfDom\<cdot>(Abs_CSPF(\<lambda> sb. (sbDom\<cdot>sb = {ch1}) 
                                  \<leadsto> ([ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)\<cdot>(sb . ch1)]\<Omega>))) = {ch1}"
  apply(simp add: spfdom_insert)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)
    
lemma spf_1x1_general_ran[simp]: "spfRan\<cdot>(Abs_CSPF(\<lambda> sb. (sbDom\<cdot>sb = {ch1}) 
                                  \<leadsto> ([ch2 \<mapsto> (f::nat stream \<rightarrow> nat stream)\<cdot>(sb . ch1)]\<Omega>))) = {ch2}"
  apply(simp add: spfran_least)
  by(simp add: spfran_least sbdom_insert)

      
 
subsection \<open>SPF1x1 constructor lemmata\<close>
(* As we now know that the general SPF1x1 is in fact an SPF we can proof properties for the general
   SPF1x1 constructor *)
  
lemma second_channel: "snd (a, b) = b"
  by simp
  
lemma SPF1x1_dom[simp]: "spfDom\<cdot>(SPF1x1 f (ch1, ch2)) = {ch1}"
proof -
  have "spfDom\<cdot> (Abs_CSPF (\<lambda>s. (sbDom\<cdot>s = {fst (ch1, ch2)})
                                            \<leadsto>[snd (ch1, ch2) \<mapsto> f\<cdot>(s . fst (ch1, ch2))]\<Omega>)) = {ch1}"
    by (metis (no_types) prod.sel(1) spf_1x1_general_dom)
  then show ?thesis
    using SPF1x1_def by presburger
qed
  
lemma SPF1x1_ran[simp]: "spfRan\<cdot>(SPF1x1 f (ch1, ch2)) = {ch2}"
  apply(simp add: SPF1x1_def)
  by (metis fst_conv spf_1x1_general_ran second_channel)
    
lemma SPF1x1_rep_eq: "Rep_CSPF (SPF1x1 f (ch1, ch2)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1,ch2))}) 
                                        \<leadsto> ([(snd (ch1,ch2)) \<mapsto> f\<cdot>(sb . (fst (ch1,ch2)))]\<Omega>))"
  apply(simp add: SPF1x1_def)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  by simp
    
lemma SPF1x1_apply: "(SPF1x1 f (ch1, ch2)) \<rightleftharpoons> ([ch1 \<mapsto> s]\<Omega>) = ([ch2 \<mapsto> f\<cdot>(s:: nat stream)]\<Omega>)"
  apply(simp add:  SPF1x1_rep_eq  sb_id_def  sbgetch_insert)
  by(simp add: sbdom_rep_eq)
    


(* ----------------------------------------------------------------------- *)
section \<open>2x1 SPF\<close>
(* ----------------------------------------------------------------------- *)

  subsection \<open>SPF2x1 prerequirements\<close>
(* anlogue to before we first show some prerequirements *)
  
lemma spf_2x1_general_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
 ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  by (rule, simp add: domIff2)
    
lemma spf_2x1_general_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1,ch2} 
                        \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)
                                    \<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma spf_2x1_general_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} 
                                \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)
  \<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma spf_2x1_general_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} \<Longrightarrow> 
  (\<Squnion>i. (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(Y i . ch1)\<cdot>(Y i . ch2)) 
  = f\<cdot>((Lub Y) . ch1)\<cdot>((Lub Y). ch2)"
proof -
  assume a1: "chain Y"
  have f2: "\<forall>f fa. (\<not> chain f \<or> \<not> chain fa) \<or> (\<Squnion>n. (f n\<cdot>(fa n::nat stream)::nat stream)) 
            = Lub f\<cdot>(Lub fa)"
    using lub_APP by blast
  have f3: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat stream)::nat stream \<rightarrow> nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  have f4: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat SB)::channel \<rightarrow> nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  have "\<forall>f c. \<not> chain f \<or> (Lub f\<cdot>(c::channel)::nat stream) = (\<Squnion>n. f n\<cdot>c)"
    using contlub_cfun_fun by blast
  then have "(\<Squnion>n. f\<cdot>(Y n . ch1)\<cdot>(Y n . ch2)) = f\<cdot>(Lub Y . ch1)\<cdot>(Lub Y . ch2)"
    using f4 f3 f2 a1 by simp
  then show ?thesis
    by force
qed

lemma spf_2x1_general_cont[simp]: "cont 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
  ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg  spf_2x1_general_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2spf_mono)
  by(simp add: domIff2, rule+)
    
lemma  spf_2x1_general_well[simp] : "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
  ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply(simp add: spf_well_def)
  apply(simp add: domIff2)
  by(auto simp add: sbdom_rep_eq)

(* Now explicitly show the domain properties of the general 2x1 SPF *)
lemma spf_2x1_general_dom[simp]: "spfDom\<cdot>(Abs_CSPF(\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
    \<leadsto> ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))) = {ch1, ch2}"
  apply(simp add: spfdom_insert)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)
    
lemma spf_2x1_general_ran[simp]: "spfRan\<cdot>(Abs_CSPF(\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
    \<leadsto> ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))) = {ch3}"
  apply(simp add: spfran_least)
  by(simp add: spfran_least sbdom_insert)
    
    
subsection \<open>SPF2x1 constructor lemmata\<close>
(* As we now know that the general SPF2x1 is in fact an SPF we can proof properties for the general
   SPF2x1 constructor *)
    
lemma SPF2x1_dom[simp]: "spfDom\<cdot>(SPF2x1 f (ch1, ch2, ch3)) = {ch1, ch2}"
  apply(simp add: SPF2x1_def)
  apply(subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv, subst snd_conv)
  by simp  
    
lemma SPF2x1_ran[simp]: "spfRan\<cdot>(SPF2x1 f (ch1, ch2, ch3)) = {ch3}"
  apply(simp add: spfran_least)
    (* the next step is very ugly, but effectively removes fst, snds *)
  apply(simp add: SPF2x1_def, subst snd_conv, subst fst_conv, 
      subst snd_conv, subst fst_conv, subst snd_conv)
  by(simp, simp add: spfran_least sbdom_insert)
    
lemma  SPF2x1_rep_eq: "Rep_CSPF (SPF2x1 f (ch1, ch2, ch3)) 
    =  (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1, ch2, ch3)), (fst (snd (ch1, ch2, ch3)))}) 
          \<leadsto> ([(snd (snd (ch1, ch2, ch3)))\<mapsto>f\<cdot>(sb . (fst (ch1, ch2, ch3)))
                \<cdot>(sb . (fst (snd (ch1, ch2, ch3))))]\<Omega>))"
  apply(simp add: SPF2x1_def)
  apply(subst snd_conv, subst fst_conv)
  apply(subst snd_conv, subst fst_conv)
  apply(subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv, subst snd_conv, 
        subst snd_conv)
  by simp
      
lemma SPF2x1_apply: assumes "ch1 \<noteq> ch2"
  shows "(SPF2x1 f (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) 
    = ([ch3 \<mapsto> (f\<cdot>s1\<cdot>s2)]\<Omega>)"
  apply(simp add: SPF2x1_rep_eq sb_id_def sbgetch_insert)
  by(auto simp add: sbdom_rep_eq assms)
    
(* For further lemmas see SerComp or ParComp *) 
    
(* ----------------------------------------------------------------------- *)
section \<open>append_componentwise\<close>
(* ----------------------------------------------------------------------- *)     
    

lemma [simp]: "cont (appendElem a)"
  apply(simp add: cont_def)
proof -
  have f1: "\<forall>f c. \<not> chain f \<or> chain (\<lambda>n. c\<cdot>(f n::nat stream)::nat stream)"
    by (metis ch2ch_Rep_cfunR)
  have f2: "\<forall>f s. (\<not> chain f \<or> Lub f \<noteq> (s::nat stream)) \<or> range f <<| s"
    by (metis thelubE)
  have "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat stream)::nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  then show "\<forall>f. chain f \<longrightarrow> range (\<lambda>n. appendElem a (f n)) <<| appendElem a (\<Squnion>n. f n)"
    using f2 f1 appendElem_def by presburger
qed

lemma appendSPF_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"
  apply(simp only: appendElem_def)
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma append_chain: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {(fst cs)} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd cs)\<mapsto>(appendElem a ((Y i).(fst cs)))]\<Omega>)"
  apply(simp only: appendElem_def)
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma appendSPF_chain_lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs)} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd cs)\<mapsto>(appendElem a ((Y i).(fst cs)))]\<Omega>)"
  by (simp add: append_chain sbChain_dom_eq2)  

lemma appendSPF_Lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs)} 
                        \<Longrightarrow> (\<Squnion>i.(appendElem a ((Y i).(fst cs)))) = appendElem a ((Lub Y).(fst cs))"
  apply(simp only: appendElem_def)    
  by (simp add: lub_distribs(1) lub_eval)

lemma appendSPF_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"
    apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg appendSPF_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub appendSPF_chain_lub appendSPF_Lub)
   apply (simp add: appendSPF_mono monofun2spf_mono)
proof -
   show "\<forall>b. (b \<in> dom (\<lambda>sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))) 
                = (sbDom\<cdot>b = {fst cs})" 
     by (simp add: domIff)
qed

(* ----------------------------------------------------------------------- *)
section \<open>legacy\<close>
(* ----------------------------------------------------------------------- *)
  (* In the following you find obsolete lemmas, kept only for compatibility purposes *)
  
subsubsection \<open>idSPF lemmata\<close>
  (* the following lemmata are only there for legacy/didactic purposes *)
  (* the functionality is now moved to the general SPF1x1 lemmata *)
  
lemma spf_sb_id_cont[simp] : "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>))"
  by simp

lemma spf_sb_id_well[simp] : "spf_well (Abs_cfun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) 
                                                  \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>)))"  
  by simp  
  
lemma spf1x1_sb_id_eq: "SPF1x1 sb_id cs = idSPF cs"
  by(simp add: SPF1x1_def idSPF_def)

lemma idSPF_rep_eq_C: "Rep_CSPF (idSPF (ch1, ch2)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1,ch2))}) 
                                        \<leadsto> ([(snd (ch1,ch2)) \<mapsto> sb_id\<cdot>(sb . (fst (ch1,ch2)))]\<Omega>))"
proof -
  have f1: "\<forall>cs. idSPF cs = SPF1x1 sb_id cs"
    by(simp add:  spf1x1_sb_id_eq)
  thus ?thesis
    by(subst f1, simp add:  SPF1x1_rep_eq)
qed
      
lemma idSPF_dom[simp]: "spfDom\<cdot>(idSPF (ch1, ch2)) = {ch1}"
  by (metis SPF1x1_dom spf1x1_sb_id_eq)
    
lemma idSPF_ran[simp]: "spfRan\<cdot>(idSPF (ch1, ch2)) = {ch2}"
  by (metis SPF1x1_ran spf1x1_sb_id_eq)
    
lemma idSPF_apply: "(idSPF (ch1, ch2)) \<rightleftharpoons> ([ch1 \<mapsto> s]\<Omega>) = ([ch2 \<mapsto> (s:: nat stream)]\<Omega>)"
proof -
  have f1: "\<forall>cs. idSPF cs = SPF1x1 sb_id cs"
    by(simp add:  spf1x1_sb_id_eq)
  thus ?thesis
    by(subst f1, simp add:  SPF1x1_apply sb_id_def)
qed
  
(* testing general lemmas 
lemma monotest: assumes "\<And>b1 b2. sbDom\<cdot>b1 = cs \<Longrightarrow> sbDom\<cdot>b2 = cs \<Longrightarrow> b1 \<sqsubseteq> b2 \<Longrightarrow> sbDom\<cdot>(f(b1)) = sbDom\<cdot>(f(b2))"
                    and "\<And>b1 b2 c. sbDom\<cdot>b1 = cs \<Longrightarrow> sbDom\<cdot>b2 = cs \<Longrightarrow> b1 \<sqsubseteq> b2 \<Longrightarrow> c \<in> sbDom\<cdot>(f(b1)) \<Longrightarrow> f(b1) . c \<sqsubseteq> f(b2) . c"
                    and " \<forall>b. (b \<in> dom (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))) = (sbDom\<cdot>b = In)"
                  shows "monofun (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))"
  sorry
    
   apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below) 
    
lemma conttest: assumes "monofun (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))"
                    and "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = cs 
                        \<Longrightarrow> chain (\<lambda> i. f(Y i))"
                    and "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = cs 
                        \<Longrightarrow> chain (\<lambda> i. f(Y i))"
                  shows "cont (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))"
  sorry siehe SPF_CaseStudy contSPF *)
    
    


(*lift_definition addSPF2 :: "nat SPF" is
"(\<lambda> cs. (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))) (ch1,ch2,ch3)"
sorry*)
  
lemma appendSPF_SPF1x1_eq: "SPF1x1 (appendElem2 a) (ch1,ch2) = appendSPF (ch1,ch2) a"
  oops (* @Marc: can you resolve this *)
    
lemma addSPF_SPF2x1_eq: "addSPF (ch1,ch2,ch3) = SPF2x1 add (ch1,ch2,ch3)"
  by(simp add: SPF2x1_def addSPF_def)
    
lemma multSPF_SPF2x1_eq: "multSPF (ch1,ch2,ch3) = SPF2x1 mult (ch1,ch2,ch3)"
  by(simp add: SPF2x1_def multSPF_def)
    
(* ----------------------------------------------------------------------- *)
subsection \<open>add_componentwise\<close>
(* ----------------------------------------------------------------------- *) 
  

lemma addSPF_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  by simp

     
lemma add_chain: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {(fst cs), (fst (snd cs))} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>)"
  by simp


lemma addSPF_chain_lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (fst (snd cs))} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>)"
  by simp

lemma addSPF_Lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (fst (snd cs))} \<Longrightarrow> 
  (\<Squnion>i. add\<cdot>(Y i . (fst cs))\<cdot>(Y i . (fst (snd cs)))) = add\<cdot>((Lub Y) . (fst cs))\<cdot>((Lub Y). (fst (snd cs)))"
   by simp


lemma addSPF_chain: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)


lemma addSPF_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  by simp

lemma addSPF_well: "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> 
  ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  by simp

lemma addSPF_rep_eqC: "Rep_CSPF (addSPF cs) = 
  (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
by(simp add: addSPF_def add2_def)


    
(* ----------------------------------------------------------------------- *)
subsection \<open>mult_componentwise\<close>
(* ----------------------------------------------------------------------- *) 
  

(* TODO: remove [simp] *)

lemma spfmult_cont[simp]: "cont 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  by simp

    

lemma spfmult_well[simp] : "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  by simp

     
    
subsection \<open>multSPF lemmata\<close>
(* LEMMAS below work if spfmult_well is proven *)
  
  
lemma multSPF_rep_eq_C: "Rep_CSPF (multSPF (ch1, ch2, ch3)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1, ch2, ch3)), (fst (snd (ch1, ch2, ch3)))}) \<leadsto> ([(snd (snd (ch1, ch2, ch3)))\<mapsto>mult\<cdot>(sb . (fst (ch1, ch2, ch3)))\<cdot>(sb . (fst (snd (ch1, ch2, ch3))))]\<Omega>))"
  by (simp add: SPF2x1_rep_eq multSPF_SPF2x1_eq)
      
lemma multSPF_dom[simp]: "spfDom\<cdot>(multSPF (ch1, ch2, ch3)) = {ch1, ch2}"
    by (simp add: multSPF_SPF2x1_eq)
    
lemma multSPF_ran[simp]: "spfRan\<cdot>(multSPF (ch1, ch2, ch3)) = {ch3}"
  by (simp add: multSPF_SPF2x1_eq)
 
lemma multSPF_apply: assumes "ch1 \<noteq> ch2"
shows "(multSPF (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) = ([ch3 \<mapsto> (mult\<cdot>s1\<cdot>s2)]\<Omega>)"
  by (simp add: multSPF_SPF2x1_eq  SPF2x1_apply assms)

    
(* lift_definition *)

lift_definition appendElem3:: "nat stream \<rightarrow> nat stream" is
"\<Lambda> s. \<up>0 \<bullet> s"
sorry

lemma append_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> (appendElem 0 (sb . c1))]\<Omega>))"
proof -
  have "\<And>c ca. (\<lambda>n s. (sbDom\<cdot>s = {c})\<leadsto>[ca \<mapsto> appendElem n (s . c)]\<Omega>) = (\<lambda>n s. (sbDom\<cdot>s = {fst (c, ca)})\<leadsto>[snd (c, ca) \<mapsto> appendElem n (s . fst (c, ca))]\<Omega>)"
    by force
  then show ?thesis
    by (metis appendSPF_cont) (* > 1.0 s, timed out *)
qed

lift_definition appendSPF2 :: "nat SPF" is
"(\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> (appendElem 0 (sb . c1))]\<Omega>))"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq append_cont)

lift_definition appendSPF3 :: "nat SPF" is
"SPF1x1 appendElem3 (c1, c2)"
sorry
    
definition SPF1x1_2 :: "(nat stream \<rightarrow> nat stream) \<Rightarrow> (channel \<times> channel) \<Rightarrow> nat SB \<rightarrow> nat SB option" where
"SPF1x1_2 f cs \<equiv> (\<Lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs)}) 
                             \<leadsto> ([(snd cs) \<mapsto> f\<cdot>(sb . (fst cs))]\<Omega>))"       

lift_definition appendSPF4 :: "nat SPF" is
"SPF1x1_2 appendElem3 (c1, c2)"
  using SPF1x1_2_def spf_1x1_general_well by presburger
    
end
 
(*
BACKUP Section

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


MULTIPLICATION

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

*)