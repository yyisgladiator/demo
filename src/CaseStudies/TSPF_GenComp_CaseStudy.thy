(*  Title:  TSPF_GenComp_CaseStudy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: A CaseStudy about the general composition operator over TSPFs
*)

theory TSPF_GenComp_CaseStudy
  imports "../TSB" "../TSPF" "../TSPF_Comp" "TSPF_Template_CaseStudy" "../TStream_JB"
    
begin

subsection \<open>definitions\<close>  
  
section \<open>delayFeedComp\<close>
(* It should be shown that the composition of two delayTSPFs delivers 
    an TSB [tsInfTick, tsInftick] *)  

abbreviation delay_fp :: "nat TSB" where
"delay_fp \<equiv> [c1 \<mapsto> tsInfTick::nat tstream, c2 \<mapsto> tsInfTick::nat tstream]\<Omega>"
  

subsection \<open>delayFeedComp\<close>  
  (* some convenience lemmas for sledgi *)
 
lemma tsb_well_test2 [simp]: "tsb_well (f::channel \<Rightarrow> nat tstream option)"
   by (metis (no_types) ctype_nat_def subset_UNIV subset_image_iff 
                         transfer_int_nat_set_return_embed tsb_well_def)

                       
 
  (* delayTSPF1 *)
lemma delay_tspf1_dom: "tspfDom\<cdot>delayTSPF1 = {c1}"
  by (simp add: delayTSPF1_def)

lemma delay_tspf1_ran [simp]: "tspfRan\<cdot>delayTSPF1 = {c2}"
  by (simp add: delayTSPF1_def)
    
lemma delay_tpsf1_apply [simp]: "delayTSPF1 \<rightleftharpoons> [c1 \<mapsto> ts:: nat tstream]\<Omega> = [c2 \<mapsto> delayFun\<cdot>ts]\<Omega>"
  by (simp add: delayTSPF1_def tsbgetch_rep_eq tsbdom_rep_eq)
 
lemma delay_tspf1_apply2 [simp]: assumes "tsbDom\<cdot>tb = {c1}"
  shows "delayTSPF1 \<rightleftharpoons> tb = ([c2 \<mapsto> delayFun\<cdot>(tb . c1)]\<Omega>)"
    by (simp add: delayTSPF1_def, simp add: assms(1))
    
  (* delayTSPF 2 *)  
lemma delay_tspf2_dom: "tspfDom\<cdot>delayTSPF2 = {c2}"
  by (simp add: delayTSPF2_def)

lemma delay_tspf2_ran [simp]: "tspfRan\<cdot>delayTSPF2 = {c1}"
  by (simp add: delayTSPF2_def)
 
lemma delay_tpsf2_apply [simp]: "delayTSPF2 \<rightleftharpoons> [c2 \<mapsto> ts:: nat tstream]\<Omega> = [c1 \<mapsto> delayFun\<cdot>ts]\<Omega>"
  by (simp add: delayTSPF2_def tsbgetch_rep_eq tsbdom_rep_eq)     
    
lemma delay_tspf2_apply2 [simp]: assumes "tsbDom\<cdot>tb = {c2}"
  shows "delayTSPF2 \<rightleftharpoons> tb = ([c1 \<mapsto> delayFun\<cdot>(tb . c2)]\<Omega>)"
    by (simp add: delayTSPF2_def, simp add: assms(1))    
    
  (* composition sets *)
lemma delay_comp_I: "tspfCompI delayTSPF1 delayTSPF2 = {}"
  by (simp add: tspfCompI_def delay_tspf1_dom delay_tspf2_dom)
 
    
  (* delay fixed point *)
lemma delay_fp_well [simp]: "tsb_well  [c1 \<mapsto> tsInfTick::nat tstream, c2 \<mapsto> tsInfTick::nat tstream]"
  by simp
    
lemma delay_fp_dom: "tsbDom\<cdot>delay_fp = {c1,c2}"
  by (simp add: insert_commute tsbdom_rep_eq)
    
lemma delay_fp_res1: "delay_fp \<bar> {c1} =   [c1 \<mapsto> tsInfTick]\<Omega>"
  apply (rule tsb_eq)
  by (simp_all add: tsbdom_rep_eq tsbgetch_rep_eq)

lemma delay_fp_res2: "delay_fp \<bar> {c2} =   [c2 \<mapsto> tsInfTick]\<Omega>"
  apply (rule tsb_eq)
  by (simp_all add: tsbdom_rep_eq tsbgetch_rep_eq)    
    
lemma delay_fp_tick: "#\<surd>tsb delay_fp = \<infinity>"
proof -
  have f0a: "delay_fp . c1 = tsInfTick"
    by (simp add: tsbgetch_rep_eq)
  moreover
  have f0b: "delay_fp . c2 = tsInfTick"
    by (simp add: tsbgetch_rep_eq)
  ultimately
  have f0: "\<forall> c \<in> tsbDom\<cdot>delay_fp. delay_fp . c = tsInfTick"
    using delay_fp_dom by auto
  have f1: "\<forall> c \<in> tsbDom\<cdot>delay_fp. #\<surd> (delay_fp . c) = \<infinity>"
    by (simp add: f0)
  show ?thesis
    apply (rule tsbtickI)
      using delay_fp_dom f1 apply blast
      by (simp add: f1)
qed      
    
subsection \<open>tsbFix\<close>    
 (* show the fixed point properties of tspfCompH delayTSPF! delayTSPF2 *)
  
  (* tspfCompH is equal to a simpler version of itself *)
lemma delay_compH_simp1: assumes "tsbDom\<cdot>x = tspfCompI delayTSPF1 delayTSPF2"
    shows "tspfCompH delayTSPF1 delayTSPF2 x = 
      (\<Lambda> z. (delayTSPF1 \<rightleftharpoons>((z)  \<bar> {c1})) \<uplus>  (delayTSPF2 \<rightleftharpoons>((z)  \<bar> {c2})))"
proof -
  have f1: "tsbDom\<cdot>x = {}"
    by (simp add: assms(1) delay_comp_I)
  show ?thesis
    by (simp add: tspfCompH_def f1 delay_tspf1_dom delay_tspf2_dom)
qed
  
lemma delay_compH_simp2: assumes "tsbDom\<cdot>x = tspfCompI delayTSPF1 delayTSPF2"
  shows "(delayTSPF1\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>delayTSPF1)) \<uplus>  (delayTSPF2\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>delayTSPF2)) =
    (delayTSPF1 \<rightleftharpoons>((z)  \<bar> {c1})) \<uplus>  (delayTSPF2 \<rightleftharpoons>((z)  \<bar> {c2}))"
  by (simp add: assms delay_comp_I delay_tspf1_dom delay_tspf2_dom)

    (* delay_fp is a fixed point *)
lemma delay_compH_fp: assumes "tsbDom\<cdot>x = tspfCompI delayTSPF1 delayTSPF2"
  shows "tspfCompH delayTSPF1 delayTSPF2 x\<cdot>delay_fp = delay_fp"
    apply (simp add: tspfCompH_def)
    apply (simp add: assms delay_compH_simp2 delay_fp_res1 delay_fp_res2)
    by (simp add: insert_commute tsb_eq tsbdom_rep_eq tsbgetch_rep_eq)
    
    
(* now as we now that 'delay_fp' is a fixed point we have to show that it is the least one *)

(* \<And>z. tsbDom\<cdot>z = {c1, c2} \<Longrightarrow> tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z = z \<Longrightarrow> delay_fp \<sqsubseteq> z *)
lemma delay_compH_least_fp: assumes "tsbDom\<cdot>z = {c1, c2}" and "tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z = z"
  and "tsbDom\<cdot>x = tspfCompI delayTSPF1 delayTSPF2"
  shows "delay_fp = z"
proof -
  
  (* PART I *)
  have f0: "z = tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z"
    by (simp add: assms(2))
  hence f1: "\<And> c. c \<in> {c1, c2} \<Longrightarrow> (tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z) . c = z . c"
    by (simp)
  have f2: "tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z = (delayTSPF1 \<rightleftharpoons> z \<bar> {c1}) \<uplus> (delayTSPF2 \<rightleftharpoons> z \<bar> {c2})"
    by (simp add: tspfCompH_def, simp add: delay_compH_simp2 assms(3))
  have f3a: "tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z . c1 = (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (z . c2)"
    apply (subst f2, subst tsbunion_getchR)
    by (simp_all add: assms(1) delay_tspf2_dom tsbdom_rep_eq tsbgetch_rep_eq delayFun.rep_eq)
  have f3b: "tspfCompH delayTSPF1 delayTSPF2 x\<cdot>z . c2 = (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (z . c1)"
    apply (subst f2, subst tsbunion_getchL)
    by (simp_all add: assms(1) delay_tspf2_dom tsbdom_rep_eq tsbgetch_rep_eq delayFun.rep_eq)
      
    (* get recursive equations with alternating channel *)
  have f4a: "z . c1 = (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (z . c2)"
    by (subst  f0, simp add: f3a)
  have f4b: "z . c2 = (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (z . c1)"   
    by (subst  f0, simp add: f3b) 
  
    (* get recursive equations with same channel *)
  have f5a: "z . c1 = (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> ((Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (z . c1))"
    by (subst f4a, subst f4b, simp)
  have f5b: "z . c2 = (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> ((Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (z . c2))"
    by (subst f4b, subst f4a, simp) 
      
      
  (* PART II: now lets focus on z . c1 first *)
      (* trivial cases *)
  have f6a: "tsNth 0\<cdot>(z . c1) =  (Abs_tstream (\<up>\<surd>))"
    by (metis delayFun.rep_eq delayFun_takeFirst f5a tsnth_shd)
  have f7a: "tsNth (Suc 0)\<cdot>(z . c1) =  (Abs_tstream (\<up>\<surd>))"
    by (metis delayFun.rep_eq delayFun_dropFirst delayFun_takeFirst f5a tsNth_Suc tsnth_shd) 
  have f8a: "\<And> i. tsNth (Suc (Suc i))\<cdot>(z . c1) = tsNth i\<cdot>(z . c1)"
    by (subst f5a, metis delayFun_dropFirst delayFun_takeFirst tsNth_Suc tsTakeDropFirst)
     
      (* based in these three trivial cases we can noe deduct the following *)
  have f9a: "\<And> i. tsNth (Suc i)\<cdot>(z . c1) = tsNth i\<cdot>(z . c1)"
  proof -
    fix i
    show "tsNth ((Suc i))\<cdot>(z . c1) = tsNth i\<cdot>(z . c1)"
    proof (induct i)
      case 0
      then show ?case
        using f6a f7a by auto
    next
      case (Suc i)
      then show ?case
          by (simp add: f8a)
      qed
  qed
      (* and hence tsNth i is always equals \<surd> *)
  have f10a: "\<And> i. tsNth (i)\<cdot>(z . c1) = (Abs_tstream (\<up>\<surd>))"
  proof -
    fix i
    show "tsNth (i)\<cdot>(z . c1) = (Abs_tstream (\<up>\<surd>))"
    proof (induct i)
      case 0
      then show ?case
        using f6a by blast
    next
      case (Suc i)
      then show ?case
        by (simp add: f9a)       
    qed
  qed    
      
      (* now show the equality with tsInfTick *)
  have f11a: "(z . c1) = tsInfTick"
    apply (rule ts_tsnth_eq)
    by (simp add: f10a tsInfTick_tsNth)
   
    (* PART II: now lets  do the same for c2 *)
      (* trivial cases *)
  have f6b: "tsNth 0\<cdot>(z . c2) =  (Abs_tstream (\<up>\<surd>))"
    by (metis delayFun.rep_eq delayFun_takeFirst f5b tsnth_shd)
  have f7b: "tsNth (Suc 0)\<cdot>(z . c2) =  (Abs_tstream (\<up>\<surd>))"
    by (metis delayFun.rep_eq delayFun_dropFirst delayFun_takeFirst f5b tsNth_Suc tsnth_shd) 
  have f8a: "\<And> i. tsNth (Suc (Suc i))\<cdot>(z . c2) = tsNth i\<cdot>(z . c2)"
    by (subst f5b, metis delayFun_dropFirst delayFun_takeFirst tsNth_Suc tsTakeDropFirst)
     
      (* based in these three trivial cases we can now deduct the following *)
  have f9b: "\<And> i. tsNth (Suc i)\<cdot>(z . c2) = tsNth i\<cdot>(z . c2)"
  proof -
    fix i
    show "tsNth ((Suc i))\<cdot>(z . c2) = tsNth i\<cdot>(z . c2)"
    proof (induct i)
      case 0
      then show ?case
        using f6b f7b by auto
    next
      case (Suc i)
      then show ?case
          by (simp add: f8a)
      qed
  qed
      (* and hence tsNth i is always equals \<surd> *)
  have f10b: "\<And> i. tsNth (i)\<cdot>(z . c2) = (Abs_tstream (\<up>\<surd>))"
  proof -
    fix i
    show "tsNth (i)\<cdot>(z . c2) = (Abs_tstream (\<up>\<surd>))"
    proof (induct i)
      case 0
      then show ?case
        using f6b by blast
    next
      case (Suc i)
      then show ?case
        by (simp add: f9b)       
    qed
  qed     
      (* now show the equality with tsInfTick *)
  have f11b: "(z . c2) = tsInfTick"
    apply (rule ts_tsnth_eq)
    by (simp add: f10b tsInfTick_tsNth)

    (* PART III: for every channel z must be qual to the delay_fp bundle *)
  have f12: "\<And>c. c \<in> tsbDom\<cdot>delay_fp \<Longrightarrow> delay_fp  .  c = z  .  c"
    proof -
    fix c :: channel
    assume "c \<in> tsbDom\<cdot>delay_fp"
    then have "c \<in> {c1, c2}"
      using delay_fp_dom by blast
    then show "delay_fp . c = z . c"
      by (metis (no_types) empty_iff f11a f11b fun_upd_apply insert_iff option.sel tsb_well_test2 
            tsbgetch_rep_eq)
  qed
      
    (* PART IV: show the thesis *)
  show ?thesis
    apply (rule tsb_eq)
      apply (simp add: assms(1) delay_fp_dom)
      by (simp add: f12)
qed  
  
      
      
   (* delay_fp is the least fixpoint of tsbfix applied to tspfComp ... *)
lemma tsbfix_delayComp_eq: assumes "tsbDom\<cdot>x = tspfCompI delayTSPF1 delayTSPF2"
  shows "(tsbFix (tspfCompH delayTSPF1 delayTSPF2 x) {c1, c2}) =  delay_fp" 
  apply (rule tsbfix_eqI)
  by (simp_all add: assms delay_fp_dom delay_compH_fp delay_compH_least_fp)
  
    
subsection \<open>tspfComp\<close>    
 (* now bring the fixed point result together with our tspfComp definition *)

lemma tspfcomp_fix_eq_pre: 
"Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfCompI delayTSPF1 delayTSPF2) 
    \<leadsto> tsbFix (tspfCompH delayTSPF1 delayTSPF2 x) (tspfRan\<cdot>delayTSPF1 \<union> tspfRan\<cdot>delayTSPF2))

= Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delay_fp)"
proof -
  have f1: "{} = tspfCompI delayTSPF1 delayTSPF2"
    by (simp add: delay_comp_I)
  have f2: "tspfRan\<cdot>delayTSPF1 \<union> tspfRan\<cdot>delayTSPF2 = {c1, c2}"
    by simp
  
  have "\<forall> x. tsbDom\<cdot>x \<noteq> ( tspfCompI delayTSPF1 delayTSPF2) \<or>
             Some (tsbFix (tspfCompH delayTSPF1 delayTSPF2 x) 
                                                          (tspfRan\<cdot>delayTSPF1 \<union> tspfRan\<cdot>delayTSPF2))
            = Some (delay_fp)"
    apply (subst f2)
    by (metis tsbfix_delayComp_eq)
    
  thus ?thesis
    apply (subst f1)
    by meson
qed


  
(* before we can show the final lemma we have to proof some properties of the delay_fp first *)
lemma delay_fp_tspf_cont [simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delay_fp)"
  by simp
  
lemma delay_fp_tspf_well [simp]: "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delay_fp)"
  apply (rule tspf_wellI)
    apply (simp_all add: domIff2)
    by (simp add: delay_fp_tick)
   
      
 (* as expected the composition delivers us a component which outputs tsInfTick on channel c1 and 
     c2  :) *)
lemma tspfcomp_delay_fp_eq: assumes "tsbDom\<cdot>tb = {}"
  shows "(delayTSPF1 \<otimes> delayTSPF2) \<rightleftharpoons> tb = delay_fp"
proof -
  have f1: "(delayTSPF1 \<otimes> delayTSPF2) = Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delay_fp)"
    apply (subst tspfComp_def )
    using tspfcomp_fix_eq_pre by presburger
  show ?thesis
    apply (subst f1)
    by (simp add: assms)
qed
  
 
    
end