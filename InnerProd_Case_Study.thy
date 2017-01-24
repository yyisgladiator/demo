(*  Title: InnerCase_Study
    Author: Marc Wiartalla, Jens Christoph Bürger
    e-mail: marc.wiartalla@rwth-aachen.de, jens.buerger@rwth-aachen.de

    Description: Fingerübung inner product
*)

theory InnerProd_Case_Study
imports SPF Streams SerComp_JB StreamCase_Study SPF_MW

begin

(* message instantiation already done in SerComp *)

(* DEFINITION ADD/MULT *)
(* Before we can build up the inner component we have to define the add and mult component first *)
(* multiplies 2 nat - streams component-wise *)
definition mult:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"mult \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) * (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"

(* Add component (use definition form StreamCase_Study) *)

(* SHOW THAT MULT/ADD COMPONENT IS CONTINUOUS *)
lemma spfadd_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> add\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma add_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1,ch2} 
                        \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>add\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma add_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} 
                                \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>add\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma sAdd_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} \<Longrightarrow> 
  (\<Squnion>i. add\<cdot>(Y i . ch1)\<cdot>(Y i . ch2)) = add\<cdot>((Lub Y) . ch1)\<cdot>((Lub Y). ch2)"
  by (simp add: lub_distribs(1) lub_eval)

lemma spfadd_chain [simp]: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {ch1, ch2}) \<leadsto> ([ch3\<mapsto>add\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma spfadd_cont[simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
                                \<leadsto> ([ch3\<mapsto>add\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))" (is "cont ?F")
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg add_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2spf_mono)
  by(simp add: domIff2, rule+)


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


(* As we now proved that the add and mult component is continuous we can define some components *)
lift_definition mult1 :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c5\<mapsto>mult\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition mult2 :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c3, c4}) \<leadsto> ([c6\<mapsto>mult\<cdot>(sb . c3)\<cdot>(sb . c4)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition addC :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c5, c6}) \<leadsto> ([c7\<mapsto>add\<cdot>(sb . c5)\<cdot>(sb . c6)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

(* rep equalities, useful for simp *)
lemma mult1_rep_eqC: "Rep_CSPF mult1 = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c5 \<mapsto> mult\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
  by (simp add: mult1.rep_eq Rep_CSPF_def)

lemma mult2_rep_eqC: "Rep_CSPF mult2 = (\<lambda> sb. (sbDom\<cdot>sb = {c3, c4}) \<leadsto> ([c6 \<mapsto> mult\<cdot>(sb . c3)\<cdot>(sb . c4)]\<Omega>))"
  by (simp add: mult2.rep_eq Rep_CSPF_def)

lemma addC_rep_eqC: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c5, c6}) \<leadsto> ([c7 \<mapsto> add\<cdot>(sb . c5)\<cdot>(sb . c6)]\<Omega>))"
  by (simp add: addC.rep_eq Rep_CSPF_def)


(* COMPONENT PROPERTIES *)
(* mult1 *)
lemma [simp]: "spfDom\<cdot>mult1 = {c1,c2}"
  apply(simp add: spfdom_insert mult1.rep_eq Rep_CSPF_def domIff2)
  by (meson sbleast_sbdom someI_ex)

lemma [simp]: "spfRan\<cdot>mult1 = {c5}"
  apply (simp add: spfran_least mult1_rep_eqC)
  by (simp add: sbdom_insert)

(* mult2 *)
lemma [simp]: "spfDom\<cdot>mult2 = {c3,c4}"
  apply(simp add: spfdom_insert mult2.rep_eq Rep_CSPF_def domIff2)
  by (meson sbleast_sbdom someI_ex)

lemma [simp]: "spfRan\<cdot>mult2 = {c6}"
  apply (simp add: spfran_least mult2_rep_eqC)
  by (simp add: sbdom_insert)

(* addC *)
lemma [simp]: "spfDom\<cdot>addC = {c5,c6}"
  apply(simp add: spfdom_insert addC.rep_eq Rep_CSPF_def domIff2)
  by (meson sbleast_sbdom someI_ex)

lemma [simp]: "spfRan\<cdot>addC = {c7}"
  apply (simp add: spfran_least addC_rep_eqC)
  by (simp add: sbdom_insert)


(* PARALLEL COMPOSITION OF MULTS PREREQUIREMENTS *)
lemma [simp]: "spfComp_well mult1 mult2"
  by (simp add: spfComp_well_def)

lemma [simp]: "C mult1 mult2 = {c1,c2,c3,c4,c5,c6}"
  by (auto simp add: C_def)

lemma [simp]: "L mult1 mult2 = {}"
  by (auto simp add: L_def)

lemma [simp]: "Oc mult1 mult2 = {c5,c6}"
  by (auto simp add: Oc_def)

lemma [simp]: "I mult1 mult2 = {c1,c2,c3,c4}"
by auto

(* Remove this ASAP *)
lemma spfCompParallelGetch1: assumes "L f1 f2 = {}"
                                and "sbDom\<cdot>sb = I f1 f2"
                                and "spfComp_well f1 f2"
                                and "c \<in> spfRan\<cdot>f1" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1)) . c"
sorry

lemma spfCompParallelGetch2: assumes "L f1 f2 = {}"
                                and "sbDom\<cdot>sb = I f1 f2"
                                and "spfComp_well f1 f2"
                                and "c \<in> spfRan\<cdot>f2" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f2) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f2)) . c"
sorry

(* added because of message instantiation clash *)

lemma mult_comp1: assumes "sbDom\<cdot>sb = I mult1 mult2"
  shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb) . c5 = ((Rep_CSPF(mult1)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult1)) . c5"
  by (subst spfCompParallelGetch1, simp_all add: assms)

lemma mult_comp2: assumes "sbDom\<cdot>sb = I mult1 mult2"
  shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb) . c6 = ((Rep_CSPF(mult2)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult2)) . c6"
  by (subst spfCompParallelGetch2, simp_all add: assms)


lemma mults_comp: assumes "sbDom\<cdot>sb = I mult1 mult2"
  shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb)  = ((Rep_CSPF(mult1)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult1)) \<uplus> ((Rep_CSPF(mult2)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult2))"
  apply(subst parallelOperatorEq)
  apply(simp_all add: parcomp_def)
 sorry  (* In order to proof this ticket:8 has to be resolved first *) 


(* SERIAL COMPOSITION OF MULTS and addC PREREQUIREMENTS *)

lemma [simp]: "spfDom\<cdot>(spfcomp mult1 mult2) = {c1, c2, c3, c4}"
by(simp add: spfComp_dom_I)

lemma [simp]: "spfRan\<cdot>(spfcomp mult1 mult2) = {c5, c6}"
by(simp add: spfComp_ran_Oc)

lemma [simp]: "spfComp_well (spfcomp mult1 mult2) addC"
by(simp add: spfComp_well_def)

lemma [simp]: "C (spfcomp mult1 mult2) addC = {c1,c2,c3,c4,c5,c6,c7}"
by(auto simp add: C_def)

lemma [simp]: "L (spfcomp mult1 mult2) addC = {c5,c6}"
by(auto simp add: L_def)

lemma [simp]: "pL (spfcomp mult1 mult2) addC = {}"
by(auto simp add: pL_def)

lemma [simp]: "Oc (spfcomp mult1 mult2) addC = {c5, c6, c7}"
by(auto simp add: Oc_def)

lemma [simp]: "I (spfcomp mult1 mult2) addC  = {c1,c2,c3,c4}"
by(auto simp add: I_def)

lemma innerprod_serComp: assumes "sbDom\<cdot>sb = I (spfcomp mult1 mult2) addC"
  shows "((spfcomp (spfcomp mult1 mult2) addC)  \<rightleftharpoons> sb) . c7 = 
         (addC \<rightleftharpoons> ((spfcomp mult1 mult2) \<rightleftharpoons> (sb\<bar>(spfDom\<cdot>(spfcomp mult1 mult2))))) . c7"
  by (subst spfCompSeriellGetch, simp_all add: assms spfComp_ran_Oc)

(* insert result lemma here *)

definition innerProd :: "nat SPF" where
"innerProd \<equiv> hide ((mult1 \<parallel> mult2) \<otimes> addC) {c5, c6}"

lemma [simp]: "spfDom\<cdot>( spfcomp (parcomp mult1 mult2) addC) = {c1, c2, c3, c4}"
apply(simp add: spfComp_dom_I I_def parCompDom parCompRan)
by auto

lemma innerProdEqCh: assumes "sbDom\<cdot>sb = I (spfcomp mult1 mult2) addC" 
    shows "(innerProd  \<rightleftharpoons> sb) . c7 = (spfcomp (spfcomp mult1 mult2) addC) \<rightleftharpoons> sb . c7"
apply(simp add: innerProd_def parallelOperatorEq)
apply(subst hideSbRestrictCh)
by(simp_all add: assms)

lemma innerprod: assumes "sbDom\<cdot>sb = I (spfcomp mult1 mult2) addC"
  shows "(innerProd  \<rightleftharpoons> sb) . c7 = add\<cdot>(mult\<cdot>(sb . c1)\<cdot>(sb . c2))\<cdot>(mult\<cdot>(sb . c3)\<cdot>(sb . c4))"
  apply(subst innerProdEqCh)
  apply(simp add: assms)
  apply(subst innerprod_serComp, simp_all add: assms)
  apply(subst mults_comp, simp_all add: assms)
  sorry

end