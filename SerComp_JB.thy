(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: serial composition of two identity single input/output channel functions
*)

theory SerComp_JB
imports SPF SBTheorie
begin

(* instatiate our message space*)
instantiation nat :: message
begin
  definition ctype_nat :: "channel \<Rightarrow> nat set" where
  "ctype c = range nat"

instance ..
end

lemma [simp]: "cs \<subseteq> ((ctype c) :: nat set)"
  apply(simp add: ctype_nat_def)
  by(metis subset_UNIV subset_image_iff transfer_int_nat_set_return_embed)


(* id function defintion, change name ASAP but for now ensures readability *)
definition bla :: "nat stream \<rightarrow> nat stream" where
"bla \<equiv> \<Lambda> x . x"

(* Show ID is monotone *)
lemma spfID_mono[simp] : "monofun (\<lambda> sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> bla\<cdot>(sb . ch1)]\<Omega>))"
  apply (rule spf_mono2monofun)
  apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
  apply(simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  apply(meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  apply rule
  by(simp add: domIff2)

(* Show ID is continuous *)
lemma ID_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> bla\<cdot>(Y i . ch1)]\<Omega>)"
  apply(rule chainI)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma ID_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> bla\<cdot>((Y i) . ch1)]\<Omega>)"
  by (simp  add: sbChain_dom_eq2)

lemma spfID_chain[simp]: "chain Y \<Longrightarrow> chain(\<lambda> i. (sbDom\<cdot>(Y i) = {ch1}) \<leadsto> ([ch2\<mapsto>bla\<cdot>((Y i) . ch1)]\<Omega>))"
  apply(rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply(rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma sID_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> (\<Squnion>i. bla\<cdot>(Y i . c1)) = bla\<cdot>((Lub Y) . c1)"
  by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma spfID_cont[simp] : "cont (\<lambda> sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> bla\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_cont2cont)
 apply(rule spf_contlubI)
  apply(simp add: domIff2 sbChain_dom_eq2)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply(simp only: Cfun.contlub_cfun_arg ID_chain_lub)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply(simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
    apply(simp add: contlub_cfun_arg)
   apply (simp add: monofun2spf_mono)
  apply(simp add: domIff2)
  by rule+ 
  

(* ID function definitions *)
lift_definition ID1 :: "nat SPF" is "(\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> bla\<cdot>(sb . c1)]\<Omega>))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition ID2 :: "nat SPF" is "(\<Lambda> sb. (sbDom\<cdot>sb = {c2}) \<leadsto> ([c3 \<mapsto> bla\<cdot>(sb . c2)]\<Omega>))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)


(* ID rep equalities *)
lemma ID1_rep_eqC: "Rep_CSPF ID1 = (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> bla\<cdot>(sb . c1)]\<Omega>))"
  by(simp add: ID1.rep_eq Rep_CSPF_def)

lemma ID2_rep_eqC: "Rep_CSPF ID2 = (\<lambda> sb. (sbDom\<cdot>sb = {c2}) \<leadsto> ([c3 \<mapsto> bla\<cdot>(sb . c2)]\<Omega>))"
  by(simp add: ID2.rep_eq Rep_CSPF_def)


(* composition prerequirements *)
lemma [simp]: "spfDom\<cdot>ID1 = {c1}"
  apply(simp add: spfdom_insert ID1.rep_eq Rep_CSPF_def)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)

lemma [simp]: "spfRan\<cdot>ID1 = {c2}"
  apply(simp add: spfran_least)
  apply(simp add: ID1_rep_eqC)
  by(simp add: sbdom_insert)

lemma [simp]: "spfDom\<cdot>ID2 = {c2}"
  apply(simp add: spfdom_insert ID2.rep_eq Rep_CSPF_def)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)

lemma [simp]: "spfRan\<cdot>ID2 = {c3}"
  apply(simp add: spfran_least)
  apply(simp add: ID2_rep_eqC)
  by(simp add: sbdom_insert)

lemma id_apply1: "((Rep_CSPF ID1) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>)) = ([c2 \<mapsto> (s:: nat stream)]\<Omega>)"
  apply(simp add: bla_def Rep_CSPF_def ID1.rep_eq sbdom_rep_eq)
  by(simp add: sbgetch_insert)

lemma id_apply2: "((Rep_CSPF ID2) \<rightharpoonup> ([c2 \<mapsto> s]\<Omega>)) = ([c3 \<mapsto> (s:: nat stream)]\<Omega>)"
  apply(simp add: bla_def Rep_CSPF_def ID2.rep_eq sbdom_rep_eq)
  by(simp add: sbgetch_insert)

lemma [simp]: "spfComp_well ID1 ID2"
  by (simp add: spfComp_well_def)


lemma [simp]: "C ID1 ID2 = {c1,c2,c3}"
  by (auto simp add: C_def)

lemma [simp]: "L ID1 ID2 = {c2}"
  by (auto simp add: L_def)

lemma [simp]: "Oc ID1 ID2 = {c3}"
  by (auto simp add: Oc_def)

lemma [simp]: "I ID1 ID2 = {c1}"
  by (auto simp add: I_def)



(* bundle prerequirements *)
lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream)]\<Omega>) = I ID1 ID2"
  by(simp add: sbdom_rep_eq)

lemma sb_rest: "([c1 \<mapsto> s]\<Omega>)\<bar>{c1} = [c1 \<mapsto> (s:: nat stream)]\<Omega>"
  by(simp add: sbrestrict_insert)

lemma [simp]:"([ch1 \<mapsto> s]\<Omega>) . ch1 = (s:: nat stream)"
  by(simp add: sbgetch_rep_eq)
(*
lemma work4: "\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(z\<bar>{c1})) \<uplus> (Rep_CSPF ID2)\<rightharpoonup>(z\<bar>{c2})) = 
 (\<Lambda> z. x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(z\<bar>{c1})) \<uplus> (Rep_CSPF ID2)\<rightharpoonup>(z\<bar>{c2}))"
oops (* this is nonsense *)


lemma work6: "\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(z\<bar>{c1})) \<uplus> (Rep_CSPF ID2)\<rightharpoonup>(z\<bar>{c2})) = "
oops (* this is nonsense *)

lemma work5: "((Rep_CSPF ID1)\<rightharpoonup>(z\<bar>{c1})) = (z\<bar>{c1})"
sorry

lemma work1: "(Rep_CSPF(spfcomp ID1 ID2) \<rightharpoonup> sb)  = ((Rep_CSPF ID2)\<rightharpoonup>((Rep_CSPF ID1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>ID1)))"
apply(simp add: spfcomp_def)
oops
*)

(* TODO: this should be ported to SPF.thy in order to make spfcomp proofs more readable *)
definition spfCompHelp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompHelp2 f1 f2 x \<equiv> (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"

(* general lemmas *)
lemma spfComp_getch_outofrange: assumes "c \<notin> spfRan\<cdot>f1" and "c \<notin> spfRan\<cdot>f2" and "sbDom\<cdot>sb = C f1 f2"
      shows "((spfCompHelp2 f1 f2 x)\<cdot>sb) . c = x . c"
  apply (simp add: spfCompHelp2_def)
  apply (subst sbunion_getchL)
  apply (simp add: C_def assms(2) assms(3) subsetI)
  by (simp add: C_def Un_assoc assms(1) assms(3))


lemma spfCompH2_dom [simp]: assumes "sbDom\<cdot>sb = C f1 f2"
      shows "sbDom\<cdot>((spfCompHelp2 f1 f2 x)\<cdot>sb) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (simp add: spfCompHelp2_def)
  proof -
    have f1: "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb"
      by (simp add: C_def Un_commute Un_left_commute assms)
    have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb"
      using C_def assms by auto
    then show "sbDom\<cdot>x \<union> (sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) \<union> (sbDom\<cdot>Rep_CSPF f2\<rightharpoonup>(sb\<bar>spfDom\<cdot>f2)) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
  qed


lemma spfComp_itCompH2_dom[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "sbDom\<cdot>(iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) = C f1 f2"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: C_def I_def assms inf_sup_aci(6))


lemma spfComp_getChI: assumes "sbDom\<cdot>x = I f1 f2" and "spfComp_well f1 f2"
                      and "c \<in> I f1 f2"
                      shows "(iterate (Suc i)\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c = x .c"
  apply (unfold iterate_Suc, subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchL)
  apply (metis C_def DiffD2 I_def UnI2 assms(1) assms(3) inf_sup_ord(4) le_supI1 spfComp_itCompH2_dom spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis C_def DiffD2 I_def UnI1 Un_upper1 assms(1) assms(3) le_supI1 spfComp_itCompH2_dom spfRanRestrict)
   by (simp)


lemma spfComp_resI: assumes "sbDom\<cdot>x = I f1 f2" and "spfComp_well f1 f2"
                    shows "(iterate (Suc i)\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> (I f1 f2) = x"
  apply (rule sb_eq)
   apply (simp add: assms(1) inf_sup_aci(1) inf_sup_aci(6))
   using assms(1) assms(2) spfComp_getChI by fastforce

(* feedback channels after composition*)
definition pL :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"pL f1 f2 \<equiv> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1) \<union> (spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2) \<union> (spfDom\<cdot>f2 \<inter> spfRan\<cdot>f2)"

lemma spfComp_serial1: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" and "sbDom\<cdot>x = I f1 f2" and "spfComp_well f1 f2"
                       and "c \<in> spfRan\<cdot>f2" and "pL f1 f2 = {}"
                       shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                              = ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1))) . c"
  


(* special case lemmas *)

















(* Generalize this, but first prove special case with f1=ID1 and f2=ID2 *)
lemma spfCompSeriellGetch: assumes "spfCompInternal f1 f2 = {ch2}"
        and "sbDom\<cdot>sb = spfCompIn f1 f2"
        and "spfComp_well f1 f2"
        and "spfRan\<cdot>f1 = {ch2}"
        and "spfRan\<cdot>f2 = {ch3}"
        and "c \<in> spfRan\<cdot>f2"
        shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1))) .c "
sorry


lemma spfSerComp_spfID : "(((Rep_CSPF (spfcomp ID1 ID2)) \<rightharpoonup> ([c1 \<mapsto> a]\<Omega>)) . c3)  =  a"
  apply (simp add: spfCompSeriellGetch)
  by (simp add: id_apply1 id_apply2)

end