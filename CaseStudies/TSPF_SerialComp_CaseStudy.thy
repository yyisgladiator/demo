(* Title: TSPF_Comp.thy
   Author: Jens Christoph Bürger
   e-mail: jens.buerger@rwth-aachen.de

   Description: some additional serial comp properties
*)

theory TSPF_SerialComp_CaseStudy
  imports "../TSPF_Comp"
    
begin

  (* just a small test if everything works as expected *)
lemma tspfcomp_serial_test: assumes "sercomp_well f1 f2" 
                            and "tsbDom\<cdot>x = tspfCompI f1 f2"
shows "Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> 
                    ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1))))) \<rightleftharpoons> x
                    = ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1))))"
    apply (simp add: assms)
    using assms(1) sercomp_input_ch by blast

  
text{* restriction of the serial composition  *}
lemma tspfComp_serial_restr: assumes "sercomp_well f1 f2"
                             and "tsbDom\<cdot>sb = tspfCompI f1 f2"
  shows "((tspfComp f1 f2) \<rightleftharpoons> sb) \<bar> tspfRan\<cdot>f2 = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb\<bar>tspfDom\<cdot>f1)))"
proof -
  have "tsbDom\<cdot>sb = tspfDom\<cdot>f1"
    using assms(1) assms(2) sercomp_input_ch by blast
  moreover
  have f2: "tsbDom\<cdot>(f1 \<rightleftharpoons> sb \<bar> tspfDom\<cdot>f1) = tspfDom\<cdot>f2"
      by (metis (no_types) assms(1) assms(2) sercomp_dom_f1 sercomp_well_def)
  moreover
  have "(f1 \<rightleftharpoons> sb \<bar> tspfDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> sb \<bar> tspfDom\<cdot>f1)) 
                  \<bar> tspfRan\<cdot>f2 = f2 \<rightleftharpoons> (f1 \<rightleftharpoons> sb \<bar> tspfDom\<cdot>f1)"
    by (metis (no_types) tsbunion_restrict2 tspf_ran_2_tsbdom2 f2)
  ultimately
  show ?thesis
    by (simp add: tspfcomp_serial assms(1))
qed

lemma assumes "tsbDom\<cdot>sb = tspfDom\<cdot>f"
  shows "(#\<surd>tsb sb) \<le> (#\<surd>tsb (f \<rightleftharpoons> sb))"
  by (metis assms tsbleast_tsdom tspf_least_in_dom tspf_less_in_than_out_ticks tspf_sbdomeq_to_domeq)
    
    
text{* A serial composition is strong causal if f1 is strong causal *}   
lemma tspfcomp_serial_str_causal1: assumes "sercomp_well f1 f2"
                                  and "tsbDom\<cdot>sb = tspfCompI f1 f2"
                                  and "#\<surd>tsb sb < \<infinity>"
  and f1_str: "\<And> b. tsbDom\<cdot>b = tspfDom\<cdot>f1 \<Longrightarrow> (#\<surd>tsb b) \<noteq> \<infinity>  \<Longrightarrow> (#\<surd>tsb b) < (#\<surd>tsb (f1\<rightleftharpoons>b))"
  shows "(#\<surd>tsb sb) < (#\<surd>tsb (((tspfComp f1 f2) \<rightleftharpoons> sb) \<bar> tspfRan\<cdot>f2))"
proof -
  have f1: "(#\<surd>tsb sb) \<le> (#\<surd>tsb (sb\<bar>tspfDom\<cdot>f1))"
    using tsbtick_tsbres by blast
  hence f2:  "(#\<surd>tsb sb) < (#\<surd>tsb (f1 \<rightleftharpoons> (sb\<bar>tspfDom\<cdot>f1)))"
    by (metis assms(1) assms(2) assms(3) dual_order.strict_implies_order f1_str neq_iff order_refl 
              sercomp_input_ch tsbunion_idL tsbunion_restrict2)
  have f10: "(#\<surd>tsb sb) <  (#\<surd>tsb (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb\<bar>tspfDom\<cdot>f1))))"
    by (smt f2 assms(1) assms(2) dual_order.strict_implies_order leD 
            order.not_eq_order_implies_strict sercomp_dom_f1 sercomp_well_def trans_lnle 
            tsbleast_tsdom tspf_least_in_dom tspf_less_in_than_out_ticks tspf_sbdomeq_to_domeq)
  thus ?thesis
    by (simp add: assms(1) assms(2) tspfComp_serial_restr)
qed   

text{* A serial composition is strong causal if f2 is strong causal *}  
lemma tspfcomp_serial_str_causal2: assumes "sercomp_well f1 f2"
                                   and "tsbDom\<cdot>sb = tspfCompI f1 f2"
                                   and "#\<surd>tsb sb < \<infinity>"
  and f2_str: "\<And> b. tsbDom\<cdot>b = tspfDom\<cdot>f2 \<Longrightarrow> (#\<surd>tsb b) \<noteq> \<infinity>  \<Longrightarrow> (#\<surd>tsb b) < (#\<surd>tsb (f2\<rightleftharpoons>b))"
  shows "(#\<surd>tsb sb) < (#\<surd>tsb (((tspfComp f1 f2) \<rightleftharpoons> sb) \<bar> tspfRan\<cdot>f2))"
proof -
  have f1: "(#\<surd>tsb sb) \<le> (#\<surd>tsb (sb\<bar>tspfDom\<cdot>f1))"
    using tsbtick_tsbres by blast
  hence f2:  "(#\<surd>tsb sb) \<le> (#\<surd>tsb (f1 \<rightleftharpoons> (sb\<bar>tspfDom\<cdot>f1)))"
    proof -
      have "\<exists>l\<le>#\<surd>tsb f1 \<rightleftharpoons> sb \<bar> tspfCompI f1 f2 . #\<surd>tsb sb \<le> l"
        by (metis assms(1) assms(2) inf_idem rep_tspf_well sercomp_input_ch tsbleast_tsdom 
                  tsbtick_tsbres tspf_least_in_dom tspf_type_def tspf_well_def tsresrict_dom3)
      then show ?thesis
        by (metis (no_types) assms(1) sercomp_input_ch trans_lnle)
    qed
  have f10: "(#\<surd>tsb sb) <  (#\<surd>tsb (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb\<bar>tspfDom\<cdot>f1))))"
    by (smt assms(1) assms(2) assms(3) f2 f2_str leD order.not_eq_order_implies_strict 
            sercomp_dom_f1 sercomp_well_def trans_lnle tsbleast_tsdom tspf_least_in_dom 
            tspf_less_in_than_out_ticks tspf_sbdomeq_to_domeq)
  thus ?thesis
    by (simp add: assms(1) assms(2) tspfComp_serial_restr)
qed 

text{* A serial composition is strong causal if f1 or f2 is strong causal *}
lemma tspfcomp_serial_str_causal: assumes "sercomp_well f1 f2"
                                   and "tsbDom\<cdot>sb = tspfCompI f1 f2"
                                   and "#\<surd>tsb sb < \<infinity>"
  and str: "(\<forall> b. (tsbDom\<cdot>b = tspfDom\<cdot>f1 \<longrightarrow> (#\<surd>tsb b) \<noteq> \<infinity>  \<longrightarrow> (#\<surd>tsb b) < (#\<surd>tsb (f1\<rightleftharpoons>b))))
                 \<or> (\<forall> b. (tsbDom\<cdot>b = tspfDom\<cdot>f2 \<longrightarrow> (#\<surd>tsb b) \<noteq> \<infinity>  \<longrightarrow> (#\<surd>tsb b) < (#\<surd>tsb (f2\<rightleftharpoons>b))))"
shows "(#\<surd>tsb sb) < (#\<surd>tsb (((tspfComp f1 f2) \<rightleftharpoons> sb) \<bar> tspfRan\<cdot>f2))"
  using assms(1) assms(2) assms(3) str tspfcomp_serial_str_causal1 
        tspfcomp_serial_str_causal2 by blast
  
end
  