theory TSPF_Feedback_CaseStudy
  imports "../TSB" "../TSPF" "../TSPF_Comp" "TSPF_Template_CaseStudy" "../TStream_JB"
    
begin

section \<open>definitions\<close>  
  
lift_definition delayTSPF :: "nat TSPF" is
  "(\<Lambda> (tb::nat TSB). (tsbDom\<cdot>tb = {c1}) \<leadsto> ([c1 \<mapsto> delayFun\<cdot>(tb . c1)]\<Omega>))"
  by simp

abbreviation delayTSPF_fp :: "nat TSB" where
"delayTSPF_fp \<equiv> [c1 \<mapsto> tsInfTick::nat tstream]\<Omega>"    
    
section\<open>sledgehammer\<close>    
    
lemma tsb_well_test2 [simp]: "tsb_well (f::channel \<Rightarrow> nat tstream option)"
   by (metis (no_types) ctype_nat_def subset_UNIV subset_image_iff 
                         transfer_int_nat_set_return_embed tsb_well_def)    
    
section\<open>prerequirements\<close>

subsection\<open>delayTSPF\<close>  
  
lemma delayTSPF_dom[simp]: "tspfDom\<cdot>delayTSPF = {c1}"
  by (simp add: delayTSPF_def)
    
lemma delayTSPF_ran[simp]: "tspfRan\<cdot>delayTSPF = {c1}"
  by (simp add: delayTSPF_def)

lemma delayTSPF_apply [simp]: "delayTSPF \<rightleftharpoons> [c1 \<mapsto> ts:: nat tstream]\<Omega> = [c1 \<mapsto> delayFun\<cdot>ts]\<Omega>"
  by (simp add: delayTSPF_def tsbgetch_rep_eq tsbdom_rep_eq) 
    
lemma delayTSPF_apply2 [simp]: assumes "tsbDom\<cdot>tsb = {c1}" shows "delayTSPF \<rightleftharpoons> tsb = [c1 \<mapsto> delayFun\<cdot>(tsb . c1)]\<Omega>"
  by (simp add: delayTSPF_def assms) 

subsection\<open>delayTSPF_fp\<close>    
    
lemma delayTSPF_fp_well[simp]: "tsb_well [c1 \<mapsto> tsInfTick::nat tstream]"
  by simp
    
lemma delayTSPF_fp_tsbDom[simp]: "tsbDom\<cdot>delayTSPF_fp = {c1}"
  by (simp add: insert_commute tsbdom_rep_eq)  

lemma delayTSPF_fp_tick[simp]: "#\<surd>tsb delayTSPF_fp = \<infinity>"
proof -   
  have f0: "delayTSPF_fp . c1 = tsInfTick"
    by (simp add: tsbgetch_rep_eq) 
  then have f1: "\<forall> c \<in> tsbDom\<cdot>delayTSPF_fp. #\<surd> (delayTSPF_fp . c) = \<infinity>"    
    by simp
  show ?thesis
    apply (rule tsbtickI)
    using delayTSPF_fp_tsbDom f1 apply blast
    by (simp add: f1)
qed
    
subsection \<open>tsbFix\<close> 

lemma delayTSPF_feedbackH_fp: assumes "tsbDom\<cdot>x = tspfDom\<cdot>delayTSPF - tspfRan\<cdot>delayTSPF"
  shows "tspfFeedbackH delayTSPF x\<cdot>delayTSPF_fp = delayTSPF_fp"
proof - 
  have f1: "cont (\<lambda>z. delayTSPF \<rightleftharpoons> z \<bar> {c1})"
    using cont_compose by force
  have f2: "delayTSPF_fp \<bar> {c1} = delayTSPF_fp"
    by (metis delayTSPF_fp_tsbDom singletonI tsb_newMap_id tsb_newMap_restrict)
  show ?thesis
    apply(simp add: tspfFeedbackH_def)
    by(simp add: assms f1 f2)
qed

lemma delayTSPF_feedbackH_least_fp: assumes "tsbDom\<cdot>z = {c1}" and "tspfFeedbackH delayTSPF x\<cdot>z = z"
  and "tsbDom\<cdot>x = tspfDom\<cdot>delayTSPF - tspfRan\<cdot>delayTSPF"
  shows "delayTSPF_fp = z"
proof - 
  have f0: "cont (\<lambda>z. delayTSPF \<rightleftharpoons> z \<bar> {c1})"
    using cont_compose by force
  have f1: "z = tspfFeedbackH delayTSPF x\<cdot>z"
    by (simp add: assms(2))
  then have f2: "z . c1 = (Abs_tstream (\<up>\<surd>)) \<bullet> (z . c1)"
    apply(subst f1)
    apply(simp add: tspfFeedbackH_def assms f0)
    by (metis delayFun.rep_eq fun_upd_same option.sel tsb_well_test2 tsbgetch_rep_eq)
  have f3: "\<And>i. tsNth i\<cdot>(z . c1) = (Abs_tstream (\<up>\<surd>))"
  proof -
   fix i
   show "tsNth (i)\<cdot>(z . c1) = (Abs_tstream (\<up>\<surd>))"
   proof (induct i)
     case 0
     then show ?case
        by (metis delayFun.rep_eq delayFun_takeFirst f2 tsnth_shd)
     next
     case (Suc i)
     then show ?case
        by (metis delayFun.rep_eq delayFun_dropFirst f2 tsNth_Suc)        
     qed
  qed
  have f4: "z . c1 = tsInfTick"
    apply (rule ts_tsnth_eq)
    by (simp add: f3 tsInfTick_tsNth)
  show ?thesis  
    apply (rule tsb_eq)
     apply(simp add: assms(1))
    apply(simp)
      by (simp add: f4 tsbgetch_rep_eq)
qed
  
lemma tsbfix_delayFeedback_eq: assumes "tsbDom\<cdot>x = tspfDom\<cdot>delayTSPF - tspfRan\<cdot>delayTSPF"
  shows "(tsbFix (tspfFeedbackH delayTSPF x) {c1}) =  delayTSPF_fp" 
proof - 
  have f1: "tsbfun_io_eq (tspfFeedbackH delayTSPF x) {c1}"
    by (simp add: assms tspfFeedbackH_dom)
  show ?thesis  
    apply (rule tsbfix_eqI)
    by (simp_all add: assms delayTSPF_feedbackH_fp delayTSPF_feedbackH_least_fp f1)
qed
  
section\<open>results\<close>
  
(*lemma tspfFeedback_fix_eq_pre: 
"Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = (tspfDom\<cdot>delayTSPF - tspfRan\<cdot>delayTSPF)) \<leadsto> tsbFix (tspfFeedbackH delayTSPF x) (tspfRan\<cdot>delayTSPF))
 = Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delayTSPF_fp)"  
proof - 
  have f1: "tspfDom\<cdot>delayTSPF - tspfRan\<cdot>delayTSPF = {}"
    by simp
  have "\<forall> x. tsbDom\<cdot>x \<noteq> {} \<or> Some (tsbFix (tspfFeedbackH delayTSPF x) (tspfRan\<cdot>delayTSPF)) = Some (delayTSPF_fp)"
    by (simp add: f1 tsbfix_delayFeedback_eq)
  thus ?thesis
    apply(subst f1)
     by meson
qed      

lemma tspfFeedback_fix_cont [simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delayTSPF_fp)"
  by simp
  
lemma tspfFeedback_fix_well [simp]: "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> delayTSPF_fp)"
  apply (rule tspf_wellI)
   by(simp_all add: domIff2)*)

lemma tspfFeedback_delayTSPF_fp_eq: assumes "tsbDom\<cdot>tb = {}"
  shows "(tspfFeedback delayTSPF) \<rightleftharpoons> tb = delayTSPF_fp" 
  by (smt Abs_cfun_inverse2 Diff_insert_absorb assms delayTSPF_dom delayTSPF_fp_tick delayTSPF_ran inf_less_eq insert_absorb insert_not_empty option.sel rep_abs_tspf tsbfix_delayFeedback_eq tsbtickI_inf tspfFeedback_cont tspfFeedback_def tspfFeedback_tspfwell)    
     
end