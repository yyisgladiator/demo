(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: serial composition of two identity single input/output channel functions
*)

theory SerComp_JB
imports SPF SBTheorie SPF_Templates
begin

(* special operator for serial composition, domain of f2 must be range of f1  *)
definition sercomp :: "'m SPF => 'm SPF => 'm SPF"  where
"sercomp f1 f2 \<equiv>
let I = spfDom\<cdot>f1
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I ) \<leadsto> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> x)))"


(* NEW CONT PROOFS *)
(* (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2 *)

lemma helper_cont[simp] : "cont (Rep_cfun (spfCompHelp2 f1 f2 x))"
by simp 


lemma iterate_cont: shows "cont (Rep_cfun (\<Squnion>i.(iterate i\<cdot>(spfCompHelp2 f1 f2 x))))"
by simp







(* Proof comphelper properties by referring to original comphelper *)
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

lemma spfCompH2_cont[simp]: "cont (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                          \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
  using spfCompHelp_cont by blast

lemma helpermonoinX: shows "monofun (\<lambda> x. spfCompHelp2 f1 f2 x)"
by(simp add: spfCompHelp2_def)

lemma helpercontinX: shows "cont (\<lambda> x. spfCompHelp2 f1 f2 x)"
apply(simp add: spfCompHelp2_def)
proof -
   have "\<forall>x. cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons>(z \<bar> spfDom\<cdot>f2)))"
   by simp
   thus "cont (\<lambda>x. \<Lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
   by (simp add: cont2cont_LAM)
qed
(*
lemma spfCompHelp_cont2 [simp]: "cont (\<lambda> last. (b \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(last \<bar> spfDom\<cdot>f1))
                                   \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(last \<bar> spfDom\<cdot>f2))))"
proof -
  have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  then have "cont (\<lambda>s. sbUnion\<cdot> (b \<uplus> Rep_cfun (Rep_SPF f1)\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))) \<and> cont (\<lambda>s. Rep_SPF f2\<cdot>(s\<bar>spfDom\<cdot>f2))"
    by simp
  then have "cont (\<lambda>s. b \<uplus> (Rep_cfun (Rep_SPF f1)\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) \<uplus> (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s\<bar>spfDom\<cdot>f2))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis by(simp add: Rep_CSPF_def)
qed
*)

(* MOVE ME
lemma test15: assumes "spfComp_well f1 f2"
shows "\<exists>i. ((\<lambda> x. (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))) = (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))))"
sorry (* Beweis Idee: verwende fall unterscheidung für die Kanäle von x, entweder fließen diese nur durch eine Komponente \<Rightarrow> parComp verwenden, 
oder durch beide lemmas von serComp verwenden jeweils die iterate to constant *)


lemma test14: assumes "spfComp_well f1 f2"
shows "cont (\<lambda> x. (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
proof -
  have "cont (\<lambda> x. (spfCompHelp2 f1 f2 x))"
    by (simp add: helpercontinX)
  then have "\<forall> i. cont (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x))"
    using cont_Rep_cfun2 cont_compose by blast
  then have "\<forall> i. cont (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))" 
     by (simp)  (* why didn't sledgi find this, needs further investigation *)
  
(* Beweis Idee für lub, 1. zeige das sofern feedback frei ein j existiert sodass lub i f(x,i) = f(j,i), dafür wird feedback freiheit benötigt ansonsten existiert lub nicht*)
(* 2. sage das dadurch das ein solches j existiert mit II unmittelbar folgt das auch lub stetig ist *)
  then have "cont (\<lambda> x. (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))))"
     using test15 assms \<open>\<forall>i. cont (\<lambda>x. iterate i\<cdot>(SerComp_JB.spfCompHelp2 f1 f2 x)\<cdot> (sbLeast (C f1 f2)))\<close> by fastforce
(* PROBLEM DES BEWEISES: feedback schleifen, vll lösbar mit direktem beweis über stetigkeit von lub, range etc. lösen *)


  thus ?thesis using cont_Rep_cfun2 cont_compose by blast
qed

lemma mySPFCOMPISCONT: assumes "spfComp_well f1 f2"
shows "cont (\<lambda> sb. (sbDom\<cdot>sb = I f1 f2) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 sb)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2))"
using assms if_then_cont test14 by blast

*)

lemma spfcomp_tospfH2: "(spfcomp f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
  apply (subst spfcomp_def, subst spfCompHelp2_def, subst C_def, subst I_def, subst Oc_def)
  by (metis (no_types) C_def I_def Oc_def)

    


(* only needed to derive the above 

definition myHelper :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"myHelper f1 f2  \<equiv>   (\<Lambda> x. (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"

lemma spfCompmono[simp] : assumes "spfComp_well f1 f2"
shows "monofun (\<lambda> sb. (sbDom\<cdot>sb = I f1 f2) \<leadsto> (myHelper f1 f2)\<cdot>sb)"
apply (rule spf_mono2monofun)
 apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
  using monofun_cfun_arg sbdom_eq apply blast
  apply(simp add: sbdom_insert)
  apply (simp add: monofun_cfun_arg monofun_cfun_fun)
 apply (simp add: domIff2)
by (rule, rule) (* the second rule almost costed all my nerves *)

lemma spfComp_chain1[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = I f1 f2 \<Longrightarrow> chain (\<lambda> i. (myHelper f1 f2)\<cdot>(Y i))"
by (simp add: monofun_cfun_arg)

lemma spfComp_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = I f1 f2 
                                      \<Longrightarrow> chain (\<lambda> i. (myHelper f1 f2)\<cdot>(Y i))"
by (simp  add: sbChain_dom_eq2)

lemma spfComp_chain2[simp]: "chain Y \<Longrightarrow> 
                                  chain(\<lambda> i. (sbDom\<cdot>(Y i) = I f1 f2) \<leadsto> ((myHelper f1 f2)\<cdot>(Y i)))"
by (simp add: monofun_Rep_cfun2)

lemma spfComp_cont[simp] : "cont (\<lambda> sb. (sbDom\<cdot>sb = I f1 f2) \<leadsto> ((myHelper f1 f2)\<cdot>sb))"
apply(rule spf_cont2cont)
 apply(rule spf_contlubI)
  apply (smt cont2contlubE cont_Rep_cfun2 domIff lub_eq option.sel po_eq_conv sbChain_dom_eq2)
  using if_then_mono monofun2spf_mono monofun_Rep_cfun2 apply blast
  apply (simp add: domIff2)
  by (rule, rule)

lemma test13 :  assumes "spfComp_well f1 f2"
shows "(myHelper f1 f2)\<cdot>sb = 
                (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 sb)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2 "
apply(subst myHelper_def)
using beta_cfun test14 assms by blast

*)









(* END OF NEW THINGS *)


(* ID function definitions *)
lift_definition ID1 :: "nat SPF" is "(\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition ID2 :: "nat SPF" is "(\<Lambda> sb. (sbDom\<cdot>sb = {c2}) \<leadsto> ([c3 \<mapsto> sb_id\<cdot>(sb . c2)]\<Omega>))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)


(* ID rep equalities, useful for simp *)
lemma ID1_rep_eqC: "Rep_CSPF ID1 = (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>))"
  by(simp add: ID1.rep_eq Rep_CSPF_def)

lemma ID2_rep_eqC: "Rep_CSPF ID2 = (\<lambda> sb. (sbDom\<cdot>sb = {c2}) \<leadsto> ([c3 \<mapsto> sb_id\<cdot>(sb . c2)]\<Omega>))"
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
  apply(simp add: sb_id_def Rep_CSPF_def ID1.rep_eq sbdom_rep_eq)
  by(simp add: sbgetch_insert)

lemma id_apply2: "((Rep_CSPF ID2) \<rightharpoonup> ([c2 \<mapsto> s]\<Omega>)) = ([c3 \<mapsto> (s:: nat stream)]\<Omega>)"
  apply(simp add: sb_id_def Rep_CSPF_def ID2.rep_eq sbdom_rep_eq)
  by(simp add: sbgetch_insert)

lemma [simp]: "spfComp_well ID1 ID2"
  by (simp add: spfComp_well_def)

lemma[simp]: "no_selfloops ID1 ID2"
  by(simp add: no_selfloops_def)

lemma [simp]: "C ID1 ID2 = {c1,c2,c3}"
  by (auto simp add: C_def)

lemma [simp]: "L ID1 ID2 = {c2}"
  by (auto simp add: L_def)

lemma [simp]: "Oc ID1 ID2 = {c2,c3}"
  by (auto simp add: Oc_def)

lemma [simp]: "I ID1 ID2 = {c1}"
  by (auto simp add: I_def)
(* END OF ID DEFINITION/PROPERTIES*)





(* GENERAL LEMMAS *)

(* bundle prerequirements *)
lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream)]\<Omega>) = I ID1 ID2"
  by(simp add: sbdom_rep_eq)

lemma sb_rest: "([ch1 \<mapsto> s]\<Omega>)\<bar>{ch1} = [ch1 \<mapsto> (s:: nat stream)]\<Omega>"
  by(simp add: sbrestrict_insert)

lemma [simp]:"([ch1 \<mapsto> s]\<Omega>) . ch1 = (s:: nat stream)"
  by(simp add: sbgetch_rep_eq)










(* PROOF OF ITERATE EQUALITIES *)

(* Helper lemmas for iterate equality *)
(* TODO Port this to SPF *)
lemma spfI_sub_C[simp]: "I f1 f2 \<subseteq> C f1 f2"
using I_def C_def by fastforce

(* TODO: improve this, needed since sledgi does not work effective without this *)
lemma num3_eq[simp] : " 3 = (Suc(Suc(Suc 0)))"
  using numeral_3_eq_3 by blast

lemma spfCompH2_getch_outofrange: assumes "c \<notin> spfRan\<cdot>f1" 
                                and "c \<notin> spfRan\<cdot>f2" 
                                and "sbDom\<cdot>sb = C f1 f2"
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
    then show "sbDom\<cdot>x \<union> (sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) \<union> (sbDom\<cdot>Rep_CSPF f2\<rightharpoonup>(sb\<bar>spfDom\<cdot>f2)) 
                = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
  qed


(* cover some basic cases *)
(* TODO: port them to SPF.thy *)
lemma spfCompH2_itDom[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "sbDom\<cdot>(iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) = C f1 f2"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: C_def I_def assms inf_sup_aci(6))


lemma spfCompH2_itgetChI: assumes "sbDom\<cdot>x = I f1 f2" 
                      and "spfComp_well f1 f2"
                      and "c \<in> I f1 f2"
  shows "(iterate (Suc i)\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c = x .c"
  apply (unfold iterate_Suc, subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchL)
  apply (metis C_def DiffD2 I_def UnI2 assms(1) assms(3) inf_sup_ord(4) 
               le_supI1 spfCompH2_itDom spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis C_def DiffD2 I_def UnI1 Un_upper1 assms(1) assms(3) 
                le_supI1 spfCompH2_itDom spfRanRestrict)
   by (simp)


lemma spfCompH2_itResI: assumes "sbDom\<cdot>x = I f1 f2" 
                    and "spfComp_well f1 f2"
  shows "(iterate (Suc i)\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> (I f1 f2) = x"
  apply (rule sb_eq)
   apply (simp add: assms(1) inf_sup_aci(1) inf_sup_aci(6))
   using assms(1) assms(2) spfCompH2_itgetChI by fastforce


lemma spfComp_I_domf1_eq: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                          and "sbDom\<cdot>sb = I f1 f2" 
                          and "spfComp_well f1 f2"
                          and "no_selfloops f1 f2"
                          and "pL f1 f2 = {}"
  shows "I f1 f2 = spfDom\<cdot>f1"
  apply(simp add: I_def, subst assms(1))
by (metis I_def pL_def assms(1) assms(2) assms(3) assms(4) assms(5) spfComp_I_domf1_eq)

(* for simp usage when the resut is input for f2 *)
lemma spfComp_domranf1: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                        and "sbDom\<cdot>sb = I f1 f2" 
                        and "spfComp_well f1 f2"
                        and "no_selfloops f1 f2"
                        and "pL f1 f2 = {}"
  shows "(sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) = spfRan\<cdot>f1"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) spfRanRestrict subset_refl spfComp_I_domf1_eq)

(* TODO: rewrite this *)
lemma spfComp_test8: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f1" 
                       and "pL f1 f2 = {}"
  shows "(iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>spfDom\<cdot>f1 
                    = ((iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>(I f1 f2))"
  using assms(1) assms(2) assms(3) assms(4) assms(6) spfComp_I_domf1_eq by fastforce


(* proof equality of iterate expressions for f1 and f2 *)
lemma spfComp_serialf1: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f1" 
                       and "pL f1 f2 = {}"                   
shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                   = (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)) . c"
  apply (subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
  apply (subst sbunion_getchL)
   apply (smt assms(1) assms(2) assms(3) assms(4) assms(5) disjoint_iff_not_equal inf_sup_ord(4) 
              le_supI1 spfCompH2_dom spfCompH2_itDom spfComp_well_def spfRanRestrict)
   apply (subst sbunion_getchR)
    apply (metis C_def Un_upper1 assms(2) assms(5) iterate_Suc le_supI1 spfCompH2_itDom 
                 spfRanRestrict)
    by (metis assms(1) assms(2) assms(3) assms(4) assms(6) iterate_Suc sbrestrict_id spfComp_I_domf1_eq 
                 spfCompH2_itResI subsetI)
  
lemma spfComp_serialf2: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f2" 
                       and "pL f1 f2 = {}"
  shows "(iterate (Suc (Suc (Suc i)))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                   = ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1))) . c"
  apply (subst iterate_Suc)
  apply (subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchR)
   apply (metis assms(1) assms(2) assms(5) inf_sup_ord(4) iterate_Suc le_supI1 spfCompH2_dom 
                spfCompH2_itDom spfRanRestrict)
    by (smt Int_absorb1 assms(1) assms(2) assms(3) assms(4) assms(6) inf_sup_ord(4) iterate_Suc 
            le_supI1 sb_eq sbrestrict2sbgetch sbrestrict_sbdom spfCompH2_dom spfComp_domranf1 
            spfCompH2_itDom spfComp_serialf1)


(* this is the core lemma for the equality proofs *)
lemma spfComp_serial : assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "pL f1 f2 = {}"
  shows "(iterate (Suc (Suc (Suc i)))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) 
                      \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1)))" (is "?L = ?R")
  apply(rule sb_eq)
  apply (smt C_def assms(1) assms(2) assms(3) assms(4) assms(5) inf_sup_ord(4) sbunionDom sbunion_restrict 
             spfComp_I_domf1_eq spfComp_domranf1 spfCompH2_itDom spfRanRestrict sup.right_idem)
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) inf_sup_ord(4) iterate_Suc sbunionDom 
          sbunion_getchL sbunion_getchR sbunion_restrict spfComp_domranf1 spfCompH2_getch_outofrange 
          spfCompH2_itDom spfComp_serialf1 spfComp_serialf2 spfRanRestrict)



(* LUB EQUALITY *)

(* As we proved that the iteration expressions can be simplified to static ones under certain 
   circumstance, we now use the lemmas from before to show that the lub can be simplified to a 
   static expression *)
(* show that lub can be described by constant if no feedback channels exist *)
lemma spfComp_serialnf_chain: assumes "sbDom\<cdot>x = I f1 f2"
                              and "spfComp_well f1 f2"
  shows "chain (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  apply(rule sbIterate_chain)
  apply (simp add: assms C_def I_def)
  by blast

lemma spfComp_serial_max: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                          and "sbDom\<cdot>x = I f1 f2" 
                          and "spfComp_well f1 f2"
                          and "no_selfloops f1 f2"
                          and "pL f1 f2 = {}"
  shows "max_in_chain 3 (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  apply(rule max_in_chainI, subst num3_eq)
  apply(subst spfComp_serial, simp_all add: assms)
  by (metis Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) assms(4) assms(5) less_Suc_eq_le spfComp_serial)

lemma spfComp_serial_itconst1 [simp]: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
                                      and "no_selfloops f1 f2"
                                      and "pL f1 f2 = {}"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
               = iterate 3\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))"
  using assms(1) assms(2) assms(3) assms(4) assms(5)
        maxinch_is_thelub spfComp_serial_max spfComp_serialnf_chain by blast

lemma spfComp_serial_itconst2 [simp]: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
                                      and "no_selfloops f1 f2"
                                      and "pL f1 f2 = {}"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) 
                \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1)))"
  by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) assms(4) assms(5)
            spfComp_serial spfComp_serial_itconst1 num3_eq)




(* NOW BRING IT ALL TOGETHER *)

(* Use the lub equality to simplify the inner expression and show that the composition is a 
   well defined spf *)



(* TODO: SHOW COMPPOSITION IS SPF AND CONTINUOUS *)

(* end of TODO *)
(* MOVE ME
lemma spfComp_mono[simp]: assumes "spfComp_well f1 f2"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
sorry
*)

lemma spfComp_Oc_sub_C: assumes "c \<in> Oc f1 f2" shows "c \<in> C f1 f2"
  by (meson assms set_mp spfOc_sub_C)

lemma spfComp_getC_Oc[simp]:  assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                              and "spfComp_well f1 f2"
                              and "c \<in> spfRan\<cdot>f2" 
                              and "pL f1 f2 = {}"
  shows "c \<in> Oc f1 f2"
  using Oc_def assms(3) assms(4) pL_def by fastforce


(* show that spfcomp can be simplified to SPF without iterate if the assumtion hold *)
lemma spfComp_iterconst_eq[simp]: assumes "spfComp_well f1 f2"
                                  and "no_selfloops f1 f2" 
                                  and "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                  and "pL f1 f2 = {}"  shows
 "(\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
            = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
proof -
  have "\<forall>s. (sbDom\<cdot>s \<noteq> I f1 f2  \<or> (Some ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2) = Some (s \<uplus> (Rep_CSPF f1\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) \<uplus> (Rep_CSPF f2\<rightharpoonup>(Rep_CSPF f1\<rightharpoonup>(s\<bar>spfDom\<cdot> f1)))\<bar>Oc f1 f2)))"
    by (metis assms(1) assms(2) assms(3) assms(4) spfComp_serial_itconst2)
  then show ?thesis
    by meson
qed



abbreviation iconst :: "'a SB \<rightarrow> 'a SPF \<rightarrow> 'a SPF \<rightarrow> 'a SB" where
"iconst \<equiv> \<Lambda> x f1 f2 . (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2"

lemma foo3[simp]: assumes "sbDom\<cdot>x = I f1 f2"
shows "sbDom\<cdot>((x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)
        = Oc f1 f2"
oops

  (*
lemma iterconst_mono1[simp]: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "pL f1 f2 = {}"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
(*apply (rule spf_mono2monofun)
  apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
   apply (metis (no_types, lifting) assms(1) assms(2) assms(3) sbdom_insert spfComp_serial_itconst2 test9)
  defer
  apply (rule, simp add: domIff2)
  apply(simp add: assms)
sorry*)
sorry
*)


lemma serial_iterconst_cont[simp]:       assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "pL f1 f2 = {}"
shows "cont (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
proof -
  
   (* show f2 (f1 (x)) is cont *) 
   have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   moreover
     have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s))"
       by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   ultimately
     have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))"
       using cont2cont_APP cont_compose op_the_cont by blast
         
   (* show that sbUnion is cont *)      
   have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   hence "cont (\<lambda>s. sbUnion\<cdot> (s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))"
     by simp
   hence "cont (\<lambda>s. s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)))))"
     using \<open>cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))\<close> cont2cont_APP cont_compose op_the_cont by blast
       
   (* show thesis *)    
   thus ?thesis
      by(simp add: Rep_CSPF_def)
  qed
    
lemma serial_iterconst_monofun[simp]:    assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "pL f1 f2 = {}"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
 using cont2mono serial_iterconst_cont assms by blast
   

lemma serial_iterconst_well[simp]:       assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "no_selfloops f1 f2"
                                  and "pL f1 f2 = {}"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) 
                            \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2))"
 apply (simp add: spf_well_def domIff2 sbdom_rep_eq assms)
 by (smt assms(1) assms(2) assms(3) assms(4) sbunionDom spfCompH2_itDom spfComp_serial_itconst1 
         spfComp_serial_itconst2)




(* FINAL LEMMA *)
lemma spfCompSeriellGetch: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                           and "sbDom\<cdot>sb = I f1 f2" 
                           and "spfComp_well f1 f2"
                           and "no_selfloops f1 f2"
                           and "c \<in> spfRan\<cdot>f2" 
                           and "pL f1 f2 = {}"
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1))) .c"
  apply (simp add: spfcomp_tospfH2)
  apply (subst spfComp_iterconst_eq, simp_all add: assms)
  apply (subst sbunion_getchR, simp_all add: assms)
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) domIff option.exhaust_sel sbleast_sbdom 
          spfLeastIDom spf_sbdom2dom spfran2sbdom spfComp_domranf1)


(* RESULT *)
(* apply the lemma to two ID functions *)
lemma [simp]:"pL ID1 ID2 = {}"
  by(simp add: pL_def)

lemma spfSerComp_spfID : "(((Rep_CSPF (spfcomp ID1 ID2)) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>)) . c3)  =  s"
  apply (simp add: spfCompSeriellGetch)
  by (simp add: id_apply1 id_apply2)

end

  
  
  
  
(* fragments for spfcomp is cont *)
(* 

lemma test10: "sbDom\<cdot>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) = C f1 f2"
sorry
lemma spfComp_cont [simp]: assumes "spfComp_well f1 f2"
shows "cont (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
apply(rule spf_cont2cont)
 apply(rule spf_contlubI)
 defer
  using assms monofun2spf_mono spfComp_mono apply blast
  apply(simp add: domIff2, rule+)
  oops

lemma spfComp_well2 [simp]: assumes "spfComp_well f1 f2"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>
                               (spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq test10 assms)

lemma spfComp_mono[simp]: assumes "spfComp_well f1 f2"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
  apply (rule spf_mono2monofun)
  apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
  apply(simp add: sbdom_insert)
  apply(rule test9, simp_all)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq spfCompHelp2_def)
  defer
  apply rule
  apply(simp add: domIff2)
  sorry

lemma test9 : "dom (Rep_SB b1) = I f1 f2 \<Longrightarrow>
             dom (Rep_SB b2) = I f1 f2 \<Longrightarrow>
             b1 \<sqsubseteq> b2 \<Longrightarrow>
             dom (Rep_SB ((\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)) =
             dom (Rep_SB ((\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))"
proof -
  fix b1 :: "'a SB" and b2 :: "'a SB"
  assume a1: "dom (Rep_SB b1) = I f1 f2"
  assume a2: "dom (Rep_SB b2) = I f1 f2"
  { fix nn :: nat
    have ff1: "sbDom\<cdot>b1 = sbDom\<cdot>b2"
      using a2 a1 by (simp add: sbdom_insert)
    have ff2: "\<And>c s. c\<cdot>(s::'a SB) = iterate (Suc 0)\<cdot>c\<cdot>s"
      by simp
    have ff3: "\<And>n s. sbDom\<cdot> (iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot>(sbLeast (C f1 f2))) = C f1 f2 \<or> sbDom\<cdot>s \<noteq> sbDom\<cdot>b2"
      using ff1 a1 by (smt SPF.spfCompHelp2_def SerComp_JB.spfCompHelp2_def sbdom_insert spfCompH2_itDom)
    then have "chain (\<lambda>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot>(sbLeast (C f1 f2)))"
      using ff2 by (metis sbIterate_chain)
    then have ff4: "\<And>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot> (sbLeast (C f1 f2)) \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot>(sbLeast (C f1 f2)))"
      by (meson is_ub_thelub)
    have "chain (\<lambda>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot>(sbLeast (C f1 f2)))"
      using ff3 ff2 ff1 by (metis sbIterate_chain)
    then have ff5: "\<And>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot> (sbLeast (C f1 f2)) \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot>(sbLeast (C f1 f2)))"
      using is_ub_thelub by blast
    have ff6: "sbLeast (C f1 f2) \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot>(sbLeast (C f1 f2)))"
      using ff4 by (metis iterate_0)
    have "sbDom\<cdot> (\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot> (sbLeast (C f1 f2))) \<inter> Oc f1 f2 = C f1 f2 \<inter> Oc f1 f2"
      using ff5 ff3 by (metis (no_types) below_SB_def iterate_0 part_dom_eq sbdom_insert)
    then have "dom (Rep_SB ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2)) = dom (Rep_SB ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2)) \<or> iterate nn\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot>(sbLeast (C f1 f2)) = iterate nn\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot>(sbLeast (C f1 f2))"
      using ff6 ff3 by (metis (no_types) below_SB_def iterate_0 part_dom_eq sbdom_insert sbrestrict_sbdom) }
  then show "dom (Rep_SB ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b1)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2)) = dom (Rep_SB ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 b2)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2))"
    by presburger
qed

lemma spfComp_mono[simp]: assumes "spfComp_well f1 f2"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
  apply (rule spf_mono2monofun)
  apply(rule spf_monoI)
  apply(simp add: domIff2)
  apply(rule sb_below)
  apply(simp add: sbdom_insert)
  apply(rule test9, simp_all)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq spfCompHelp2_def)
  defer
  apply rule
  apply(simp add: domIff2)

oops
*)