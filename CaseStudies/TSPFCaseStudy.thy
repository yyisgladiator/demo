(* 
    Author:     Sebastian Stüber
*)



theory TSPFCaseStudy
imports TSPFTheorie
begin




(* definition delayFun *)
  (* adds a \<surd> as head *)


lemma delay_tsbi_well[simp]:
  fixes x :: "'a TSB_inf" 
  shows "ctype ch1 \<subseteq> ((ctype ch2) :: 'a set) \<Longrightarrow> ch1 \<in> tsbiDom\<cdot>x \<Longrightarrow> tsb_inf_well [ch2 \<mapsto> (delayFun\<cdot>(x . ch1))]"
apply(simp add: tsb_inf_well_def)
using tsbi_getch_type by blast

lemma delay_tsbi_ran: assumes "b \<in> (\<lambda>tb::'a TSB_inf. Abs_TSB_inf [ch2 \<mapsto> delayFun\<cdot>tb . ch1]) ` TSBi {ch1}"
          and "ctype ch1 \<subseteq> ((ctype ch2) :: 'a set)"
  shows "tsbiDom\<cdot>b = {ch2}"
proof -
  obtain x where x_def: "((\<lambda>tb::'a TSB_inf. Abs_TSB_inf [ch2 \<mapsto> delayFun\<cdot>tb . ch1]) x=b) \<and> x\<in>TSBi {ch1} " using assms by auto
  hence "tsbiDom\<cdot>x = {ch1}" by (simp add: TSBi_def mem_Collect_eq)
  hence "tsb_inf_well [ch2 \<mapsto> delayFun\<cdot>(x . ch1)]" using assms(2) delay_tsbi_well by blast
  hence "tsbiDom\<cdot> (Abs_TSB_inf [ch2 \<mapsto> delayFun\<cdot>(x . ch1)]) = {ch2}" by(simp add: tsbiDom_def)
  thus ?thesis by (simp add: x_def) 
qed

lemma delay_spf_type:
  shows "ctype ch1 \<subseteq> ((ctype ch2) :: 'a set) \<Longrightarrow> tspf_type (\<lambda>tb::'a TSB_inf. (tsbiDom\<cdot>tb = {ch1})\<leadsto>Abs_TSB_inf [ch2 \<mapsto> delayFun\<cdot>tb . ch1])"
  apply(simp add: tspf_type_def, rule)
   apply(simp add: domIff2)
   apply auto[1]
  by(simp add: part_ran2 delay_tsbi_ran)

lemma delay_spf_strong: "((ctype ch1) :: 'a set) \<subseteq> ((ctype ch2) :: 'a set) \<Longrightarrow> tspf_strongCausality (\<lambda>tb::'a TSB_inf. (tsbiDom\<cdot>tb = {ch1})\<leadsto>Abs_TSB_inf [ch2 \<mapsto> delayFun\<cdot>tb . ch1])"
  apply(rule tspf_strongCausalityI)
  apply (simp add: domIff2)
  apply (rule tsb_eq)
   apply (simp)
   apply(simp add: tsbidom_insert)
  apply (simp)
  apply(simp add: tsbidom_insert)
  apply (simp add: tsbiGetCh_rep_eq tsbidom_insert)
  apply auto
  by (metis delayFun_sCausal singletonI tsbidom_insert tsbittake_getch)


instantiation nat :: message
begin
  definition ctype_nat :: "channel \<Rightarrow> nat set" where "ctype_nat c = range nat"
 
  instance ..
end


lemma [simp]: "ns \<subseteq> ((ctype c) :: nat set)"
apply (simp add: ctype_nat_def)
using int_eq_iff by blast

lift_definition delayTspf:: "nat TSPF" is "\<lambda>tb. ((tsbiDom\<cdot>tb = {c1}) \<leadsto> (Abs_TSB_inf [c2 \<mapsto> ((delayFun\<cdot>(tb . c1)))]))" 
  apply(simp add: tspf_well_def)
  by(simp add: ctype_nat_def delay_spf_strong delay_spf_type)

lift_definition delayTspf2:: "nat TSPF" is "\<lambda>tb. ((tsbiDom\<cdot>tb = {c3}) \<leadsto> (Abs_TSB_inf [c4 \<mapsto> ((delayFun\<cdot>(tb . c3)))]))" 
  apply(simp add: tspf_well_def)
  by(simp add: ctype_nat_def delay_spf_strong delay_spf_type)


lift_definition delayTestS :: "nat tstream" is "\<up>(Msg 1) \<bullet> (\<up>\<surd>\<infinity>)"
apply(simp only: ts_well_def)
by simp

lemma [simp]: "tsDom\<cdot>delayTestS = {1}"
by(simp add: tsdom_insert delayTestS.rep_eq)

lemma [simp]: "#\<surd> delayTestS = \<infinity>"
by(simp add: tstickcount_insert "delayTestS.rep_eq")

lift_definition delayTestB :: "nat TSB_inf" is "[c1 \<mapsto> delayTestS]"
by(simp add: tsb_inf_well_def)

lemma [simp]: "tsbiDom\<cdot>delayTestB = {c1}"
by(simp add: tsbidom_insert delayTestB.rep_eq)

lemma "((Rep_TSPF delayTspf) \<rightharpoonup> delayTestB)  .  c2 = delayFun\<cdot>delayTestS"
apply(simp add: delayTspf.rep_eq)
apply(simp add: tsbiGetCh_rep_eq ctype_nat_def)
by (simp add: tsbiGetCh_def delayTestB.rep_eq)


(* composition *)
lemma [simp]: "tspfDom\<cdot>delayTspf = {c1}"
by(simp add: tspfdom_insert delayTspf.rep_eq)

lemma [simp]: "tspfDom\<cdot>delayTspf2 = {c3}"
by(simp add: tspfdom_insert delayTspf2.rep_eq)

lemma [simp]: "tspfRan\<cdot>delayTspf = {c2}"
proof -
  have "(\<lambda>t. Abs_TSB_inf [c2 \<mapsto> delayFun\<cdot>t::nat TSB_inf . c1]) ` TSBi {c1} \<noteq> {}"
    by simp
  then have "tsbiDom\<cdot> (SOME t. (t::nat TSB_inf) \<in> (\<lambda>t. Abs_TSB_inf [c2 \<mapsto> delayFun\<cdot>t . c1]) ` TSBi {c1}) = {c2}"
    by (metis ctype_nat_def delay_tsbi_ran order_refl some_in_eq)
  thus ?thesis by(simp add: tspfran_insert delayTspf.rep_eq part_ran2)
qed

lemma [simp]: "tspfRan\<cdot>delayTspf2 = {c4}"
proof -
  have "(\<lambda>t. Abs_TSB_inf [c4 \<mapsto> delayFun\<cdot>t::nat TSB_inf . c3]) ` TSBi {c3} \<noteq> {}"
    by simp
  then have "tsbiDom\<cdot> (SOME t. (t::nat TSB_inf) \<in> (\<lambda>t. Abs_TSB_inf [c4 \<mapsto> delayFun\<cdot>t . c3]) ` TSBi {c3}) = {c4}"
    by (metis ctype_nat_def delay_tsbi_ran order_refl some_in_eq)
  thus ?thesis by(simp add: tspfran_insert delayTspf2.rep_eq part_ran2)
qed

lemma [simp]: "comp_well delayTspf delayTspf2"
by(auto simp add: comp_well_def)

lemma [simp]: "tspfCompInternal delayTspf delayTspf2 = {}"
by(auto simp add: tspfCompInternal_def)


lift_definition delayCompBundle :: "nat TSB_inf" is "[c1 \<mapsto> delayTestS, c3 \<mapsto> tsInfTick]"
by(simp add: tsb_inf_well_def)

lemma [simp]: "tsbiDom\<cdot>delayCompBundle = tspfCompIn delayTspf delayTspf2"
by(simp add: tspfCompIn_def tsbidom_insert "delayCompBundle.rep_eq")

lemma [simp]: "tsbiDom\<cdot>(delayTspf2 \<rightharpoonup> (delayCompBundle \<bar> {c3})) = {c4}"
  apply(simp add: tsbirestrict_insert delayCompBundle.rep_eq)
  apply(simp add: delayTspf2.rep_eq tsbidom_rep_eq)
  apply(subst tsbidom_rep_eq )
   apply(simp add: tsb_inf_well_def)
  by simp

lemma "(Rep_TSPF (delayTspf \<otimes> delayTspf2) \<rightharpoonup> delayCompBundle)  .  c2 = delayFun\<cdot>delayTestS"
  apply(simp add: tspfCompParallel)
  apply(simp add: delayTspf.rep_eq tsbidom_insert tsbirestrict_insert)
  apply(simp add:  delayCompBundle.rep_eq)
  by(simp add: tsbigetch_rep_eq tsb_inf_well_def)

lemma "(Rep_TSPF (delayTspf \<otimes> delayTspf2) \<rightharpoonup> delayCompBundle)  .  c4 = tsInfTick"
  apply(simp add: tspfCompParallel)
  apply(simp add: delayTspf2.rep_eq tsbidom_insert tsbirestrict_insert)
  apply(simp add: delayCompBundle.rep_eq)
  by(simp add: tsbigetch_rep_eq tsb_inf_well_def)







(* Shared input channels *)

lift_definition delayTspf3:: "nat TSPF" is "\<lambda>tb. ((tsbiDom\<cdot>tb = {c1}) \<leadsto> (Abs_TSB_inf [c3 \<mapsto> ((delayFun\<cdot>(tb . c1)))]))" 
  apply(simp add: tspf_well_def)
  by(simp add: ctype_nat_def delay_spf_strong delay_spf_type)

lemma [simp]: "tspfDom\<cdot>delayTspf3 = {c1}"
by(simp add: tspfdom_insert delayTspf3.rep_eq)

lemma [simp]: "tspfRan\<cdot>delayTspf3 = {c3}"
apply (simp add: tspfran_insert delayTspf3.rep_eq)
apply(simp add: part_ran2)
proof -
  have "(\<lambda>t. Abs_TSB_inf [c3 \<mapsto> delayFun\<cdot>t::nat TSB_inf . c1]) ` TSBi {c1} \<noteq> {}"
    by simp
  then show "tsbiDom\<cdot> (SOME t. (t::nat TSB_inf) \<in> (\<lambda>t. Abs_TSB_inf [c3 \<mapsto> delayFun\<cdot>t . c1]) ` TSBi {c1}) = {c3}"
    by (metis ctype_nat_def delay_tsbi_ran order_refl some_in_eq)
qed

lemma [simp]: "comp_well delayTspf delayTspf3"
by(auto simp add: comp_well_def)

lemma [simp]: "tspfCompInternal delayTspf delayTspf3 = {}"
by(auto simp add: tspfCompInternal_def)


lift_definition delayCompBundle2 :: "nat TSB_inf" is "[c1 \<mapsto> delayTestS]"
by(simp add: tsb_inf_well_def)

lemma [simp]: "tsbiDom\<cdot>delayCompBundle2 = tspfCompIn delayTspf delayTspf3"
by(simp add: tspfCompIn_def tsbidom_insert "delayCompBundle2.rep_eq")


lemma [simp]: "tsbiDom\<cdot>(delayTspf3 \<rightharpoonup> (delayCompBundle2 \<bar> {c1})) = {c3}"
  apply(simp add: tsbirestrict_insert delayCompBundle2.rep_eq)
  apply(simp add: delayTspf3.rep_eq tsbidom_rep_eq)
  apply(subst tsbidom_rep_eq )
   apply(simp add: tsb_inf_well_def)
  by simp

lemma "(Rep_TSPF (delayTspf \<otimes> delayTspf3) \<rightharpoonup> delayCompBundle2)  .  c2 = delayFun\<cdot>delayTestS"
  apply(simp add: tspfCompParallel)
  apply(simp add: delayTspf.rep_eq tsbidom_insert tsbirestrict_insert)
  apply(simp add:  delayCompBundle2.rep_eq)
  by(simp add: tsbigetch_rep_eq tsb_inf_well_def)

lemma "(Rep_TSPF (delayTspf \<otimes> delayTspf3) \<rightharpoonup> delayCompBundle2)  .  c3 = delayFun\<cdot>delayTestS"
  apply(simp add: tspfCompParallel)
  apply(simp add: delayTspf.rep_eq tsbidom_insert tsbirestrict_insert)
  apply(simp add:  delayCompBundle2.rep_eq)
  apply(simp add: delayTspf3.rep_eq)
  apply(subst tsbidom_rep_eq)
   apply (metis delayCompBundle2.rsp eq_onp_same_args)
  apply(simp add: tsbigetch_rep_eq)
  apply(subst tsbigetch_rep_eq)
   apply (metis delayCompBundle2.rsp eq_onp_def)
  apply rule+
   apply(subst tsbigetch_rep_eq)
    apply(simp add: tsb_inf_well_def)
   apply simp
  apply rule+
  by (metis delayCompBundle2.abs_eq delayCompBundle2.rep_eq dom_eq_singleton_conv tsbidom_insert)







(* Neu *)
(* sequential composition neue lemmas *)

(* die componenten: *)
 

(* delayTspf ::  c1 \<longrightarrow> c2 , hängt \<surd> vorne an *)


(* delayTspf3 :: c2 \<longrightarrow> c3, dito *)
lift_definition delayTspf3:: "nat TSPF" is "\<lambda>tb. ((tsbiDom\<cdot>tb = {c2}) \<leadsto> (Abs_TSB_inf [c3 \<mapsto> ((delayFun\<cdot>(tb . c2)))]))" 
  apply(simp add: tspf_well_def)
  by(simp add: ctype_nat_def delay_spf_strong delay_spf_type)


lemma [simp]: "tspfDom\<cdot>delayTspf3 = {c2}"
by(simp add: tspfdom_insert delayTspf3.rep_eq)

lemma [simp]: "\<exists>x. x\<in>TSBi cs"
by (simp add: ex_in_conv)

lemma [simp]: "tspfRan\<cdot>delayTspf3 = {c3}"
apply(simp add: tspfran_insert delayTspf3.rep_eq)
apply(subst part_ran2)
proof -
  have "(\<lambda>t. Abs_TSB_inf [c3 \<mapsto> delayFun\<cdot>t::nat TSB_inf . c2]) ` TSBi {c2} \<noteq> {}"
    by auto
  then show "tsbiDom\<cdot> (SOME t. (t::nat TSB_inf) \<in> (\<lambda>t. Abs_TSB_inf [c3 \<mapsto> delayFun\<cdot>t . c2]) ` TSBi {c2}) = {c3}"
    by (metis ctype_nat_def delay_tsbi_ran order_refl some_in_eq)
qed

lemma [simp]: "comp_well delayTspf delayTspf3"
by (auto simp add: comp_well_def)

lemma [simp]: "tspfDom\<cdot>delayTspf3 \<subseteq> tspfRan\<cdot>delayTspf" 
by auto

lemma [simp]: "\<not>tspfDom\<cdot>delayTspf \<subseteq> tspfRan\<cdot>delayTspf3" 
by auto







(* Allgemeine lemmas über sequentielle composition *)

lemma tspf_comp_helper_seq: assumes "tspfCompInternal f1 f2 \<subseteq> tspfDom\<cdot>f2"
        and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
        and "comp_well f1 f2"
        and "c\<in>tspfRan\<cdot>f1" 
     shows "(comp_helper_inf i f1 f2 tb)  .  c = (f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1))  . c \<down> i" (is "?L i = ?R i")
sorry

lemma tspfCompSequential2:
  assumes "tspfCompInternal f1 f2 \<subseteq> tspfDom\<cdot>f2" (* alle internen channels gehen in f2 rein *)
      and "comp_well f1 f2"
      and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
      and "c\<in>tspfRan\<cdot>f1" and "c\<notin>tspfDom\<cdot>f2"
    shows "(f1\<otimes>f2) \<rightharpoonup> tb . c = (f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1))  . c"
apply(simp add: tspfComp_def assms(3))
apply(auto simp add: assms tspfCompOut_def tspfCompInternal_def tspfCompIn_def comp_well_def)
sorry

lemma tspfCompSequential:
  assumes "tspfCompInternal f1 f2 \<subseteq> tspfDom\<cdot>f2" (* alle internen channels gehen in f2 rein *)
      and "comp_well f1 f2"
      and "tsbiDom\<cdot>tb = tspfCompIn f1 f2"
  shows "(f1\<otimes>f2) \<rightharpoonup> tb = ((f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1)) \<bar> tspfCompOut f1 f2) \<uplus>  (f2 \<rightharpoonup> ((tb \<uplus> (f1 \<rightharpoonup> (tb\<bar>tspfDom\<cdot>f1)))\<bar>tspfDom\<cdot>f2))" (is "?L = ?R")
apply(rule tsbi_eq)
apply simp


lemma [simp]: "tspfCompInternal delayTspf delayTspf3 = {c2}"
by (auto simp add: tspfCompInternal_def)

lemma [simp]: "tspfCompIn delayTspf delayTspf3 = {c1}"
by (auto simp add: tspfCompIn_def)

lemma tsbi_restrict_id [simp]:"cs = tsbiDom\<cdot>tbi \<Longrightarrow> tbi \<bar> cs = tbi"
by (metis inf.idem tsbiRestrict_getch tsbi_eq tsbirestrict_dom3)

lemma "(delayTspf \<otimes> delayTspf3) \<rightharpoonup> delayTestB   .  c3 = delayFun\<cdot>(delayFun\<cdot>delayTestS)"
apply(subst tspfCompSequential, simp_all)
apply(simp add: delayTspf.rep_eq)
apply (subst tsbiunion_getchR)

oops

end
