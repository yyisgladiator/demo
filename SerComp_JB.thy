(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: serial composition of two identity single input/output channel functions
*)

theory SerComp_JB
imports SPF SB SPF_Templates
begin

(* ----------------------------------------------------------------------- *)
section \<open>Definitions\<close>
(* ----------------------------------------------------------------------- *)  
  
(* special operator for serial composition, domain of f2 must be range of f1  *)
  (* THIS IS OBSOLETE *)
definition sercomp :: "'m SPF => 'm SPF => 'm SPF"  where
"sercomp f1 f2 \<equiv>
let I = spfDom\<cdot>f1
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I ) \<leadsto> ((f2 \<rightleftharpoons> ( f1 \<rightleftharpoons> x))))"

abbreviation iconst :: "'a SB \<rightarrow> 'a SPF \<rightarrow> 'a SPF \<rightarrow> 'a SB" where
"iconst \<equiv> \<Lambda> x f1 f2 . (x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2"

(* ----------------------------------------------------------------------- *)
section \<open>General lemmata\<close>
(* ----------------------------------------------------------------------- *)

lemma sb_rest: "([ch1 \<mapsto> s]\<Omega>)\<bar>{ch1} = [ch1 \<mapsto> (s:: nat stream)]\<Omega>"
  by(simp add: sbrestrict_insert)

lemma [simp]:"([ch1 \<mapsto> s]\<Omega>) . ch1 = (s:: nat stream)"
  by(simp add: sbgetch_rep_eq)
  
lemma spfI_sub_C[simp]: "I f1 f2 \<subseteq> C f1 f2"
using I_def C_def by fastforce
  
  (* necessary for sledgehammer *)
lemma num3_eq[simp] : " 3 = (Suc(Suc(Suc 0)))"
  using numeral_3_eq_3 by blast  
  


(* ----------------------------------------------------------------------- *)
section \<open>sercomp channel domain lemmata\<close>
(* ----------------------------------------------------------------------- *)
    
lemma spfComp_test8: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f1" 
                       and "pL f1 f2 = {}"
  shows "spfDom\<cdot>f1  = (I f1 f2)"
  using assms(1) assms(2) assms(3) assms(4) assms(6) spfComp_I_domf1_eq by fastforce
    
(* for simp usage when the resut is input for f2 *)
lemma spfComp_domranf1: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                        and "sbDom\<cdot>sb = I f1 f2" 
                        and "spfComp_well f1 f2"
                        and "no_selfloops f1 f2"
                        and "pL f1 f2 = {}"
  shows "(sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) = spfRan\<cdot>f1"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) spfRanRestrict subset_refl 
      spfComp_I_domf1_eq)
    

lemma spfComp_I_domf1_eq: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                          and "sbDom\<cdot>sb = I f1 f2" 
                          and "spfComp_well f1 f2"
                          and "no_selfloops f1 f2"
                          and "pL f1 f2 = {}"
  shows "I f1 f2 = spfDom\<cdot>f1"
  apply(simp add: I_def, subst assms(1))
  by (metis I_def  assms(1) assms(2) assms(3) assms(4) assms(5) spfComp_I_domf1_eq)
    

lemma spfComp_Oc_sub_C: assumes "c \<in> Oc f1 f2" shows "c \<in> C f1 f2"
  by (meson assms set_mp spfOc_sub_C)

lemma spfComp_getC_Oc[simp]:  assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                              and "spfComp_well f1 f2"
                              and "c \<in> spfRan\<cdot>f2" 
                              and "pL f1 f2 = {}"
  shows "c \<in> Oc f1 f2"
  using Oc_def assms(3) assms(4) pL_def by fastforce
    
(* ----------------------------------------------------------------------- *)
section \<open>Comp Helper2 Lemmata\<close>
(* ----------------------------------------------------------------------- *)
  

subsection \<open>basic properties\<close>
(* ----------------------------------------------------------------------- *)

lemma helper_cont[simp] : "cont (Rep_cfun (spfCompHelp2 f1 f2 x))"
by simp 


lemma iterate_cont: shows "cont (Rep_cfun (\<Squnion>i.(iterate i\<cdot>(spfCompHelp2 f1 f2 x))))"
by simp



(* Proof comphelper properties by referring to original comphelper *)
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

lemma spfCompH2_cont[simp]: "cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                          \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
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


lemma spfcomp_tospfH2: "(spfcomp f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
  apply (subst spfcomp_def, subst spfCompHelp2_def, subst C_def, subst I_def, subst Oc_def)
  by (metis (no_types) C_def I_def Oc_def)

    

subsection \<open>channel properties\<close>
(* ----------------------------------------------------------------------- *)

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
    thus "sbDom\<cdot>x \<union> (sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) \<union> (sbDom\<cdot> (f2 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f2))) 
                = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
  qed


(* ----------------------------------------------------------------------- *)
section \<open>iterate spfCompHelp2 lemmata\<close>
(* ----------------------------------------------------------------------- *)

  
subsection \<open>domain and input channel properties\<close>
(* ----------------------------------------------------------------------- *)
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



subsection \<open>inner and output channel properties\<close>
(* ----------------------------------------------------------------------- *)
  
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
  by (metis assms(1) assms(2) assms(3) assms(4) assms(6) iterate_Suc sbrestrict_id 
      spfComp_I_domf1_eq spfCompH2_itResI subsetI)
  
lemma spfComp_serialf2: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f2" 
                       and "pL f1 f2 = {}"
  shows "(iterate (Suc (Suc (Suc i)))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                   = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))) . c"
  apply (subst iterate_Suc)
  apply (subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchR)
   apply (metis assms(1) assms(2) assms(5) inf_sup_ord(4) iterate_Suc le_supI1 spfCompH2_dom 
                spfCompH2_itDom spfRanRestrict)
    by (smt Int_absorb1 assms(1) assms(2) assms(3) assms(4) assms(6) inf_sup_ord(4) iterate_Suc 
            le_supI1 sb_eq sbrestrict2sbgetch sbrestrict_sbdom spfCompH2_dom spfComp_domranf1 
            spfCompH2_itDom spfComp_serialf1)


subsection \<open>complete channel properties\<close>
(* ----------------------------------------------------------------------- *)
(* this is the core lemma for the equality proofs *)
lemma spfComp_serial : assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "pL f1 f2 = {}"
  shows "(iterate (Suc (Suc (Suc i)))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                      \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)))" (is "?L = ?R")
  apply(rule sb_eq)
  apply (smt C_def assms(1) assms(2) assms(3) assms(4) assms(5) inf_sup_ord(4) sbunionDom sbunion_restrict 
             spfComp_I_domf1_eq spfComp_domranf1 spfCompH2_itDom spfRanRestrict sup.right_idem)
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) inf_sup_ord(4) iterate_Suc sbunionDom 
          sbunion_getchL sbunion_getchR sbunion_restrict spfComp_domranf1 spfCompH2_getch_outofrange 
          spfCompH2_itDom spfComp_serialf1 spfComp_serialf2 spfRanRestrict)



(* ----------------------------------------------------------------------- *)
section \<open>lub spfCompHelp2 lemmata\<close>
(* ----------------------------------------------------------------------- *)

(* As we proved that the iteration expressions can be simplified to static ones under certain 
   circumstance, we now use the lemmas from before to show that the lub can be simplified to a 
   static expression *)
subsection \<open>chain properties\<close>
(* ----------------------------------------------------------------------- *)
lemma spfComp_serialnf_chain: assumes "sbDom\<cdot>x = I f1 f2"
                              and "spfComp_well f1 f2"
  shows "chain (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  apply(rule sbIterate_chain)
  apply (simp add: assms C_def I_def)
  by blast

    (* show that the chain has it's maximum at the third chain element *)
lemma spfComp_serial_max: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                          and "sbDom\<cdot>x = I f1 f2" 
                          and "spfComp_well f1 f2"
                          and "no_selfloops f1 f2"
                          and "pL f1 f2 = {}"
  shows "max_in_chain 3 (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  apply(rule max_in_chainI, subst num3_eq)
  apply(subst spfComp_serial, simp_all add: assms)
  by (metis Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) assms(4) assms(5) less_Suc_eq_le 
        spfComp_serial)

subsection \<open>lub const equality\<close>
(* ----------------------------------------------------------------------- *)
  (* show that lub can be described by constant if no feedback channels exist *)
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
            = x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)))"
  by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) assms(4) assms(5)
            spfComp_serial spfComp_serial_itconst1 num3_eq)



(* ----------------------------------------------------------------------- *)
section \<open>spfComp lemmata\<close>
(* ----------------------------------------------------------------------- *)

(* NOW BRING IT ALL TOGETHER *)

(* Use the lub equality to simplify the inner expression and show that the composition is a 
   well defined spf *)



subsection \<open>lub const equality\<close>
(* ----------------------------------------------------------------------- *)
(* show that spfcomp can be simplified to SPF without iterate if the assumtion hold *)
lemma spfComp_iterconst_eq[simp]: assumes "spfComp_well f1 f2"
                                  and "no_selfloops f1 f2" 
                                  and "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                  and "pL f1 f2 = {}"  
shows
 "(\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
  = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
proof -
  have "\<forall>s. (sbDom\<cdot>s \<noteq> I f1 f2  \<or> 
        (Some ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2) 
        = Some (s \<uplus> (f1 \<rightleftharpoons> (s\<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (s\<bar>spfDom\<cdot> f1)))\<bar>Oc f1 f2)))"
    by (metis assms(1) assms(2) assms(3) assms(4) spfComp_serial_itconst2)
  then show ?thesis
    by meson
qed





subsection \<open>spf properties for sercomp\<close>
(* ----------------------------------------------------------------------- *)

lemma serial_iterconst_cont[simp]:       assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "pL f1 f2 = {}"
shows "cont (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
proof -
  
   (* show f2 (f1 (x)) is cont *) 
   have f11: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   moreover
     have f12: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s))"
       by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   ultimately
     have f13: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))"
       using cont2cont_APP cont_compose op_the_cont by blast
         
   (* show that sbUnion is cont *)      
   have f21: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   hence f22: "cont (\<lambda>s. sbUnion\<cdot> (s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))"
     by simp
   hence f23: "cont (\<lambda>s. s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) 
            \<uplus> ((Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)))))"
     using f13 cont2cont_APP cont_compose op_the_cont by blast
       
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
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                            \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2))"
 apply (simp add: spf_well_def domIff2 sbdom_rep_eq assms)
 by (smt assms(1) assms(2) assms(3) assms(4) sbunionDom spfCompH2_itDom spfComp_serial_itconst1 
         spfComp_serial_itconst2)


(* ----------------------------------------------------------------------- *)
section \<open>Main lemmata\<close>
(* ----------------------------------------------------------------------- *)

(* FINAL LEMMA *)
lemma spfCompSeriellGetch: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                           and "sbDom\<cdot>sb = I f1 f2" 
                           and "spfComp_well f1 f2"
                           and "no_selfloops f1 f2"
                           and "c \<in> spfRan\<cdot>f2" 
                           and "pL f1 f2 = {}"
  shows "((spfcomp f1 f2) \<rightleftharpoons> sb) . c = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) .c"
  apply (simp add: spfcomp_tospfH2)
  apply (subst spfComp_iterconst_eq, simp_all add: assms)
  apply (subst sbunion_getchR, simp_all add: assms)
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) domIff option.exhaust_sel 
      sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom spfComp_domranf1)


  
(* ----------------------------------------------------------------------- *)
section \<open>Serial ID Example\<close>
(* ----------------------------------------------------------------------- *)
  
  
subsection \<open>ID SPFs Instantiation\<close>
(* ----------------------------------------------------------------------- *)
  (* Note that this way of Instantiating a SPF is now obsolete, please see SPF templates 
     for a simpler method *)

subsubsection \<open>ID SPF definition\<close>
  (* the definitions use SPF Template proofs *)
lift_definition ID1 :: "nat SPF" is "(\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition ID2 :: "nat SPF" is "(\<Lambda> sb. (sbDom\<cdot>sb = {c2}) \<leadsto> ([c3 \<mapsto> sb_id\<cdot>(sb . c2)]\<Omega>))"
  by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)


(* ID rep equalities, useful for simp *)
lemma ID1_rep_eqC: "Rep_CSPF ID1 = (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>))"
  by(simp add: ID1.rep_eq Rep_CSPF_def)

lemma ID2_rep_eqC: "Rep_CSPF ID2 = (\<lambda> sb. (sbDom\<cdot>sb = {c2}) \<leadsto> ([c3 \<mapsto> sb_id\<cdot>(sb . c2)]\<Omega>))"
  by(simp add: ID2.rep_eq Rep_CSPF_def)


subsubsection \<open>ID component properties\<close>
  
lemma [simp]: "spfDom\<cdot>ID1 = {c1}"
  apply(simp add: spfdom_insert)
    apply(simp add: ID1.rep_eq Rep_CSPF_def)
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

lemma id_apply1: "(ID1 \<rightleftharpoons> ([c1 \<mapsto> s]\<Omega>)) = ([c2 \<mapsto> (s:: nat stream)]\<Omega>)"
  by(simp add: sb_id_def Rep_CSPF_def ID1.rep_eq sbdom_rep_eq)

lemma id_apply2: "(ID2 \<rightleftharpoons> ([c2 \<mapsto> s]\<Omega>)) = ([c3 \<mapsto> (s:: nat stream)]\<Omega>)"
  by(simp add: sb_id_def Rep_CSPF_def ID2.rep_eq sbdom_rep_eq)

    
subsubsection \<open>Composition prerequirements\<close>
  
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

lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> (s:: nat stream)]\<Omega>) = I ID1 ID2"
  by(simp add: sbdom_rep_eq)
    
lemma [simp]:"pL ID1 ID2 = {}"
  by(simp add: pL_def)

    
subsection \<open>Final lemma\<close>
(* ----------------------------------------------------------------------- *)
    
lemma spfSerComp_spfID : "(((spfcomp ID1 ID2) \<rightleftharpoons> ([c1 \<mapsto> s]\<Omega>)) . c3)  =  s"
  apply (simp add: spfCompSeriellGetch)
  by (simp add: id_apply1 id_apply2)


end
  
  
  
  
  
  
  
  
  
  
  
  
  
(* ----------------------------------------------------------------------- *)
section \<open>Backups\<close>
(* ----------------------------------------------------------------------- *)
 
  (*
(* fragments for spfcomp is cont *)



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

*)
