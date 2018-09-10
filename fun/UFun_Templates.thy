(*  Title:  UFun_Templates.thy
    Author: Jens Christoph Bürger, David Duc Duong, Mathias Pfeiffer
    e-mail: jens.buerger@rwth-aachen.de, david.duong@rwth-aachen.de, mathias.pfeiffer@rwth-aachen.de
    
    Description: Aggregates commonly used Ufun patterns with constructors.
    To instantiate a Ufun use the Ufun1x1, Ufun2x1 definition with an appropriate function which 
    automatically proves cont, ufun_well, dom, range for your definition.   
*)

(* NOTE: This instantiation uses the old cont, mono prove technique, for a more 
         modern/simplified approach use the ufun_contI and ufun_monoI2 lemmata from Ufun.thy *)

theory UFun_Templates
  imports  UFun_Comp stream.Streams bundle.UBundle_Pcpo

begin

default_sort uscl_pcpo


(* --------------------------------------------------------------------------------------------- *)
section \<open>Predicates to ensure the mapping conforms to channel types\<close>
(* --------------------------------------------------------------------------------------------- *)

subsection \<open>Definitions\<close>

definition map_io_well_1x1 :: "(channel \<Rightarrow> 'a::uscl \<Rightarrow> bool) \<Rightarrow> ('a \<rightarrow> 'a) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> bool" 
  where "map_io_well_1x1 P f ch1 ch2 \<equiv> \<forall> x. P ch1 x = P ch2 (f\<cdot>x)"
                
definition map_io_well_2x1 :: "(channel \<Rightarrow> 'a::uscl \<Rightarrow> bool) \<Rightarrow> ('a \<rightarrow> 'a \<rightarrow> 'a) 
                            \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> bool" 
  where "map_io_well_2x1 P f ch1 ch2 ch3 \<equiv> \<forall> x y. (P ch1 x \<and> P ch2 y) = P ch3 (f\<cdot>x\<cdot>y)"

definition map_io_well_2x2 :: "(channel \<Rightarrow> 'a::uscl \<Rightarrow> bool) \<Rightarrow> ('a \<rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ('a \<rightarrow> 'a \<rightarrow> 'a) 
                            \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> bool" 
  where "map_io_well_2x2 P f g ch1 ch2 ch3 ch4 \<equiv> \<forall> x y. (P ch1 x \<and> P ch2 y)
                                                      = (P ch3 (f\<cdot>x\<cdot>y) \<and> P ch4 (g\<cdot>x\<cdot>y)) \<and> ch3 \<noteq> ch4"


subsection \<open>Lemmas\<close>

subsubsection \<open>1x1\<close>

lemma map_io_well_1x1_ubwell: assumes "map_io_well_1x1 usclOkay f ch1 ch2" 
                                  and "usclOkay ch1 x"
                                shows "ubWell [ch2 \<mapsto> f\<cdot>x]"
  apply (rule ubwellI)
  apply (simp add: domIff)
  using assms map_io_well_1x1_def by blast

lemma map_io_well_1x1_ubwell2: assumes "map_io_well_1x1 usclOkay f ch1 ch2" 
                                   and "ch1 \<in> ubDom\<cdot>ub"
                                 shows "ubWell [ch2 \<mapsto> f\<cdot>(ub . ch1)]"
  by (metis assms map_io_well_1x1_ubwell ubdom_channel_usokay ubgetch_insert)


subsubsection \<open>2x1\<close>

lemma map_io_well_2x1_ubwell: assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3" 
                                  and "usclOkay ch1 x"
                                  and "usclOkay ch2 y"
                                shows "ubWell [ch3 \<mapsto> f\<cdot>x\<cdot>y]"
  apply (rule ubwellI)
  apply (simp add: domIff)
  by (meson assms map_io_well_2x1_def)

lemma map_io_well_2x1_ubwell2: assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3" 
                                   and "ch1 \<in> ubDom\<cdot>ub"
                                   and "ch2 \<in> ubDom\<cdot>ub"
                                 shows "ubWell [ch3 \<mapsto> f\<cdot>(ub . ch1)\<cdot>(ub . ch2)]"
  by (metis assms map_io_well_2x1_ubwell ubdom_channel_usokay ubgetch_insert)


subsubsection \<open>2x2\<close>

lemma map_io_well_2x2_ubwell: assumes "map_io_well_2x2 usclOkay f g ch1 ch2 ch3 ch4" 
                                  and "usclOkay ch1 x"
                                  and "usclOkay ch2 y"
                                shows "ubWell [ch3 \<mapsto> f\<cdot>x\<cdot>y, ch4 \<mapsto> g\<cdot>x\<cdot>y]"
  proof -
    have h1: "usclOkay ch3 (f\<cdot>x\<cdot>y)"
      by (meson assms(1) assms(2) assms(3) map_io_well_2x2_def)
    have h2: "usclOkay ch4 (g\<cdot>x\<cdot>y)"
      by (meson assms(1) assms(2) assms(3) map_io_well_2x2_def)
    show ?thesis
      by (metis (full_types) h1 h2 ubWell_empty ubrep_ubabs ubsetch_well)
  qed

lemma map_io_well_2x2_ubwell2: assumes "map_io_well_2x2 usclOkay f g ch1 ch2 ch3 ch4" 
                                   and "ch1 \<in> ubDom\<cdot>ub"
                                   and "ch2 \<in> ubDom\<cdot>ub"
                                 shows "ubWell [ch3 \<mapsto> f\<cdot>(ub .ch1)\<cdot>(ub .ch2), ch4 \<mapsto> g\<cdot>(ub .ch1)\<cdot>(ub .ch2)]"
  by (metis assms(1) assms(2) assms(3) map_io_well_2x2_ubwell ubdom_channel_usokay ubgetch_insert)


(* --------------------------------------------------------------------------------------------- *)
section \<open>Definitions\<close>
(* --------------------------------------------------------------------------------------------- *)

(* General 1x1 Ufun constructor with 1 input and 1 output channel *)
definition uf_1x1 :: "('a \<rightarrow> 'a) \<Rightarrow> (channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_1x1 f cs \<equiv> Abs_cufun (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {(fst cs)}) 
                             \<leadsto> (Abs_ubundle [(snd cs) \<mapsto> f\<cdot>(sb . (fst cs))]))"

(* General 2x1 Ufun constructor with 2 input and 1 output channel *)
definition uf_2x1 :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<Rightarrow>  (channel \<times> channel \<times> channel)  \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_2x1 f cs \<equiv> Abs_cufun (\<lambda>b. (ubDom\<cdot>b = {(fst cs), (fst (snd cs))}) 
                          \<leadsto> (Abs_ubundle [(snd (snd cs))\<mapsto>f\<cdot>(b . (fst cs))\<cdot>(b . (fst (snd cs)))]))"

(* General 2x2 Ufun constructor with 2 input and 2 output channels *)
definition uf_2x2 :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ('a \<rightarrow> 'a \<rightarrow> 'a)
                      \<Rightarrow> (channel \<times> channel) \<Rightarrow> (channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_2x2 f1 f2 Ics Ocs \<equiv> Abs_cufun (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {(fst Ics), (snd Ics)}) 
                          \<leadsto> (Abs_ubundle [(fst Ocs)\<mapsto>f1\<cdot>(sb . (fst Ics))\<cdot>(sb . (snd Ics)),
                               (snd Ocs)\<mapsto>f2\<cdot>(sb . (fst Ics))\<cdot>(sb . (snd Ics))]))"


(* --------------------------------------------------------------------------------------------- *)
section \<open>Lemmas\<close>
(* --------------------------------------------------------------------------------------------- *)

subsection \<open>1x1\<close>

(* 1x1 construction is monotonic *)
lemma uf_1x1_mono[simp]: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "monofun (\<lambda>sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))"
  apply (fold ubclDom_ubundle_def)
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x \<noteq> {ch1}")
  apply (simp_all add: ubcldom_fix)
  apply (rule some_below)
  apply (rule ub_below)
  apply (simp add: ubdom_insert)
  apply (simp_all add: assms map_io_well_1x1_ubwell2 ubclDom_ubundle_def)
  apply (simp add: assms map_io_well_1x1_ubwell2 ubdom_below)
  by (simp add: assms fun_upd_same map_io_well_1x1_ubwell2 monofun_cfun_arg ubdom_below ubgetch_ubrep_eq)

(* 1x1 construction preserves chain properties *)
lemma uf_1x1_chain1[simp]: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i . ch1)])"
  apply(rule chainI)
  apply(rule ub_below)
  apply (simp add: assms map_io_well_1x1_ubwell2 ubdom_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: assms map_io_well_1x1_ubwell2 ubdom_ubrep_eq)
  by (simp add: assms map_io_well_1x1_ubwell2 monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)

lemma uf_1x1_chain_lub[simp]: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [ch2 \<mapsto> f\<cdot>((Y i) . ch1)])"
  by (simp add: assms)
    
lemma uf_1x1_chain2: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> chain(\<lambda> i. (ubDom\<cdot>(Y i) = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>((Y i) . ch1)]))"
  apply(rule chainI, simp)
  apply(rule impI, rule some_below, rule ub_below)
  apply (simp add: assms map_io_well_1x1_ubwell2 ubdom_ubrep_eq)
  by (simp add: assms map_io_well_1x1_ubwell2 monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)
    
(* LUB and 1x1 construction are commutative *)
lemma uf_1x1_lub[simp]: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow>  (\<Squnion>i. f\<cdot>(Y i . c1)) = f\<cdot>((Lub Y) . c1)"
  by (metis ch2ch_Rep_cfunR contlub_cfun_arg)

(* Monotonic & Chain/LUB properties \<Longrightarrow> resulting function from 1x1 construction is continous *)
lemma uf_1x1_cont[simp] : 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "cont (\<lambda>sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))"
proof- 
  have f1: " \<And>(x::'a\<^sup>\<Omega>) y::'a\<^sup>\<Omega>. ubclDom\<cdot>x = {ch1} \<Longrightarrow> x \<sqsubseteq> y 
      \<Longrightarrow> Abs_ubundle [ch2 \<mapsto> f\<cdot>(x  .  ch1)] \<sqsubseteq> Abs_ubundle [ch2 \<mapsto> f\<cdot>(y  .  ch1)]"
    apply (simp_all add: ubclDom_ubundle_def)
    apply (rule ub_below)
    apply (simp add: assms map_io_well_1x1_ubwell2 ubdom_below ubdom_ubrep_eq) +
    apply (simp add: ubgetch_ubrep_eq assms map_io_well_1x1_ubwell2 ubdom_below)
    by (simp add: monofun_cfun_arg)
  have f2: "\<And>Y::nat \<Rightarrow> 'a\<^sup>\<Omega>.
       chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow> chain (\<lambda>i::nat. Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)])"
    by (simp add: assms ubclDom_ubundle_def)    
  have f3: "\<And> Y. chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       ubDom\<cdot>(Abs_ubundle [ch2 \<mapsto> f\<cdot>((\<Squnion>i::nat. Y i)  .  ch1)]) = {ch2}"
    by (simp add: assms map_io_well_1x1_ubwell2 ubclDom_ubundle_def ubdom_ubrep_eq)
  have f31: "\<And> Y. chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       (\<Squnion>i::nat. ubDom\<cdot>(Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)])) = {ch2}"
    apply (simp add: ubdom_insert)
    by (simp add: assms map_io_well_1x1_ubwell2 ubclDom_ubundle_def)
  have f5: "\<And>(Y::nat \<Rightarrow> 'a\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       Abs_ubundle [ch2 \<mapsto> f\<cdot>((\<Squnion>i::nat. Y i)  .  ch1)]  .  ch2 = f\<cdot>((\<Squnion>i::nat. Y i)  .  ch1)"
    by (simp add: assms map_io_well_1x1_ubwell2 ubgetch_ubrep_eq)
  have f6: "\<And>(Y::nat \<Rightarrow> 'a\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       (\<Squnion>i::nat. Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)])  .  ch2 = (\<Squnion>i::nat. f\<cdot>(Y i  .  ch1))"
    apply (subst ubgetch_lub, simp add: f2)
    apply (metis (mono_tags) contlub_cfun_arg f2 f31 insertI1 ubclDom_ubundle_def)
    by (simp add: assms map_io_well_1x1_ubwell2 ubgetch_ubrep_eq)
  show ?thesis
    apply (fold ubclDom_ubundle_def)
    apply (rule ufun_contI)
    apply (simp add: f1)
    apply (rule ub_below)
    apply (subst contlub_cfun_arg, simp) +
    apply (subst contlub_cfun_arg)
    apply (simp add:f2 ubclDom_ubundle_def)
    apply (simp add: ubdom_insert)
    apply (subst ubrep_ubabs)
    apply (metis assms ch2ch_Rep_cfunR contlub_cfun_arg insertI1 map_io_well_1x1_ubwell2 ubclDom_ubundle_def)
    apply (simp add: assms map_io_well_1x1_ubwell2 ubclDom_ubundle_def)
    apply (simp add: f3 ubclDom_ubundle_def)
    apply (simp add: f5 f6)
    by (metis below_refl ch2ch_Rep_cfunR contlub_cfun_arg)
qed

(* As the general 1x1 Ufun is continous and has fixed input and output channels it is a ufun *)
lemma uf_1x1_well[simp]: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "ufWell (Abs_cfun (\<lambda>sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)])))"  
  apply (rule ufun_wellI)
  apply (simp_all add: domIff2 assms)
  apply (simp_all add: ubclDom_ubundle_def)
  apply (simp add: ubdom_insert)
  by (simp add: assms map_io_well_1x1_ubwell2 ubdom_insert)

(* The domain is ch1 *)
lemma uf_1x1_rep_dom: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "ufDom\<cdot>(Abs_cufun(\<lambda> sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))) = {ch1}"
  apply(simp add: ufdom_insert)
  apply(simp add: assms domIff2)
  apply (fold ubclDom_ubundle_def)
  apply (rule someI_ex)
  by (simp add: ubundle_ex)

lemma uf_1x1_dom[simp]: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "ufDom\<cdot>(uf_1x1 f (ch1, ch2)) = {ch1}"
  apply(simp only: uf_1x1_def fst_conv snd_conv)
  by(simp add: assms uf_1x1_rep_dom)

(* The range is ch2 *)
lemma uf_1x1_rep_ran:
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "ufRan\<cdot>(Abs_cufun(\<lambda> sb::('a::uscl_pcpo)\<^sup>\<Omega>. (ubDom\<cdot>sb = {ch1}) 
                                                   \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))) = {ch2}"
  apply (simp add: ufran_least)
  apply (subst rep_abs_cufun)
  apply (simp add: assms) +
  apply (fold ubclDom_ubundle_def)
  apply (simp add: ubcldom_least_cs)
  apply (simp add: ubclDom_ubundle_def)
  apply(simp add: assms uf_1x1_rep_dom)
  by (metis assms dom_empty dom_fun_upd map_io_well_1x1_ubwell2 option.simps(3) singletonI
            ubclDom_ubundle_def ubcldom_least_cs ubdom_ubrep_eq)

lemma uf_1x1_ran[simp]: assumes "map_io_well_1x1 usclOkay f ch1 ch2"
                          shows "ufRan\<cdot>(uf_1x1 f (ch1, ch2)) = {ch2}"
  apply(simp only: uf_1x1_def fst_conv snd_conv)
  by(simp add: uf_1x1_rep_ran assms)  

(* Equation for Rep_cufun *)
lemma uf_1x1_rep_eq: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
    shows "Rep_cufun (uf_1x1 f (ch1, ch2)) 
                                = (\<lambda>b. (ubDom\<cdot>b = {(fst (ch1,ch2))}) 
                                        \<leadsto> (Abs_ubundle [(snd (ch1,ch2)) \<mapsto> f\<cdot>(b . (fst (ch1,ch2)))]))"
  apply(simp add: uf_1x1_def)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  by(simp add: assms)

(* Applying uf_1x1 *)
lemma uf_1x1_apply: 
  assumes "map_io_well_1x1 usclOkay f ch1 ch2"
      and "usclOkay ch1 s"
    shows "(uf_1x1 f (ch1, ch2)) \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s]) = (Abs_ubundle [ch2 \<mapsto> f\<cdot>s])"
  apply(simp add: assms(1) uf_1x1_rep_eq ub_eq ubgetch_insert)
  by(simp add: ubWell_def assms(2) ubdom_ubrep_eq)


subsection \<open>2x1\<close>

(* TODO: Der Beweis ist ein 'ne Katastrophe *)
lemma uf_2x1_mono[simp]: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "monofun (\<lambda>b. (ubDom\<cdot>b = {ch1, ch2}) \<leadsto> (Abs_ubundle [ch3 \<mapsto> f\<cdot>(b .ch1)\<cdot>(b .ch2)]))"
  apply (fold ubclDom_ubundle_def)
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x \<noteq> {ch1}")
  apply (simp_all add: ubcldom_fix)
  apply(rule impI)
defer (* LOL *)
  apply(rule impI)
defer
  proof - 
    fix x::"'a\<^sup>\<Omega>"
    fix y::"'a\<^sup>\<Omega>"
    assume "x \<sqsubseteq> y"
    moreover assume "ubclDom\<cdot>y = {ch1, ch2}"
    moreover have "ubclDom\<cdot>x = {ch1, ch2}"
      using calculation(1) calculation(2) ubcldom_fix by blast
    moreover have "[ch3 \<mapsto> f\<cdot>(x  .  ch1)\<cdot>(x  .  ch2)] \<sqsubseteq> [ch3 \<mapsto> f\<cdot>(y  .  ch1)\<cdot>(y  .  ch2)]"
      by (simp add: calculation(1) monofun_cfun part_below)
    moreover have "ubWell [ch3 \<mapsto> f\<cdot>(x  .  ch1)\<cdot>(x  .  ch2)]"
      apply(simp add: ubWell_def)
      by (metis assms calculation(3) insert_iff map_io_well_2x1_def ubclDom_ubundle_def ubdom_channel_usokay ubgetch_insert)
    ultimately show "Some (Abs_ubundle [ch3 \<mapsto> f\<cdot>(x  .  ch1)\<cdot>(x  .  ch2)]) \<sqsubseteq>
       Some (Abs_ubundle [ch3 \<mapsto> f\<cdot>(y  .  ch1)\<cdot>(y  .  ch2)])" 
        proof -
          have f1: "\<forall>c. usclOkay c (y . c) \<or> c \<notin> {ch1, ch2}"
            by (metis (full_types) \<open>ubclDom\<cdot>(y::'a\<^sup>\<Omega>) = {ch1::channel, ch2::channel}\<close> ubclDom_ubundle_def ubdom_channel_usokay ubgetch_insert)
          then have "usclOkay ch2 (y . ch2)"
            by blast
          then have "usclOkay ch3 (f\<cdot>(y . ch1)\<cdot>(y . ch2))"
            using f1 by (meson assms insertI1 map_io_well_2x1_def)
          then have "ubWell [ch3 \<mapsto> f\<cdot>(y . ch1)\<cdot>(y . ch2)]"
            by (metis (no_types) ubWell_empty ubrep_ubabs ubsetch_well)
          then show ?thesis
            by (simp add: \<open>[ch3::channel \<mapsto> (f::'a \<rightarrow> 'a \<rightarrow> 'a)\<cdot> ((x::'a\<^sup>\<Omega>) . (ch1::channel))\<cdot> (x . (ch2::channel))] \<sqsubseteq> [ch3 \<mapsto> f\<cdot>((y::'a\<^sup>\<Omega>) . ch1)\<cdot>(y . ch2)]\<close> \<open>ubWell [ch3::channel \<mapsto> (f::'a \<rightarrow> 'a \<rightarrow> 'a)\<cdot> ((x::'a\<^sup>\<Omega>) . (ch1::channel))\<cdot> (x . (ch2::channel))]\<close> below_ubundle_def some_below)
        qed
  next
    fix x::"'a\<^sup>\<Omega>"
    fix y::"'a\<^sup>\<Omega>"
    assume "x \<sqsubseteq> y"
    moreover assume "ubclDom\<cdot>y = {ch1}"
    moreover assume "ch2 = ch1"
    moreover have "[ch3 \<mapsto> f\<cdot>(x  .  ch1)\<cdot>(x  .  ch2)] \<sqsubseteq> [ch3 \<mapsto> f\<cdot>(y  .  ch1)\<cdot>(y  .  ch2)]"
      by (simp add: calculation(1) monofun_cfun part_below)
    moreover have "ubWell [ch3 \<mapsto> f\<cdot>(x  .  ch1)\<cdot>(x  .  ch2)]"
      apply(simp add: ubWell_def)
      by (metis (full_types) assms calculation(1) calculation(2) calculation(3) insertI1 map_io_well_2x1_def ubclDom_ubundle_def ubdom_below ubdom_channel_usokay ubgetch_insert)
    show "Some (Abs_ubundle [ch3 \<mapsto> f\<cdot>(x  .  ch1)\<cdot>(x  .  ch1)]) \<sqsubseteq>
       Some (Abs_ubundle [ch3 \<mapsto> f\<cdot>(y  .  ch1)\<cdot>(y  .  ch1)])"
      by (metis \<open>ubWell [ch3::channel \<mapsto> (f::'a \<rightarrow> 'a \<rightarrow> 'a)\<cdot> ((x::'a\<^sup>\<Omega>) . (ch1::channel))\<cdot> (x . (ch2::channel))]\<close> assms below_ubundle_def calculation(2) calculation(3) calculation(4) map_io_well_2x1_ubwell2 singletonI some_below ubclDom_ubundle_def ubrep_ubabs)
  qed

lemma map_lub: assumes "chain (A::nat \<Rightarrow> 'a::cpo)"
                 shows "(\<Squnion>i. [ch3 \<mapsto> A i]) = [ch3 \<mapsto> (\<Squnion>i. A i)]"
  proof -
    have h0: "chain (\<lambda>i. [ch3 \<mapsto> A i])"
      by (simp add: assms part_map_chain)
    have h1: "\<And>i. dom [ch3 \<mapsto> A i] = {ch3}"
      by auto
    have h2: "\<And>i. [ch3 \<mapsto> A i] \<sqsubseteq> (\<Squnion>i. [ch3 \<mapsto> A i])"
      using assms is_ub_thelub h0 by auto
    have h3: "dom (\<Squnion>i. [ch3 \<mapsto> A i]) = {ch3}"
      by (metis dom_eq_singleton_conv h2 part_dom_eq)
    obtain x where x_def: "(\<Squnion>i. [ch3 \<mapsto> A i]) = [ch3 \<mapsto> x]"
      using dom_eq_singleton_conv h3 by force
    have h4: "\<And>i. A i \<sqsubseteq> x"
      by (metis fun_belowD fun_upd_same h2 some_below2 x_def)    
    have h5: "x = (\<Squnion>i. A i)"
      proof (rule ccontr)
        assume gegenteil: "x \<noteq> (\<Squnion>i. A i)"
        have g3: "(\<Squnion>i. [ch3 \<mapsto> A i]) \<noteq> [ch3 \<mapsto> x]"
          by (metis (mono_tags, lifting) fun_upd_same gegenteil h0 lub_eq option.sel part_the_lub)
        show False
          using g3 x_def by auto
      qed
    show ?thesis
      by (simp add: h5 x_def)
  qed

lemma uf_2x1_cont[simp]: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "cont (\<lambda>b. (ubDom\<cdot>b = {ch1, ch2}) \<leadsto> (Abs_ubundle [ch3 \<mapsto> f\<cdot>(b .ch1)\<cdot>(b .ch2)]))"
  proof (rule contI)
    fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume a1: "chain Y"
    show "range (\<lambda>i. (ubDom\<cdot>(Y i) = {ch1, ch2}) \<leadsto> Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])
            <<| (ubDom\<cdot>(\<Squnion>i. Y i) = {ch1, ch2}) \<leadsto> Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)]"
      proof (cases "\<exists>i. ubDom\<cdot>(Y i) = {ch1, ch2}")
        case True
        have h0: "\<And>i. ubDom\<cdot>(Y i) = {ch1, ch2}"
          using True a1 by auto
        have h1: "range (\<lambda>i. (ubDom\<cdot>(Y i) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])
                = range (\<lambda>i. Some (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))"
          by (simp add: h0)
        have h2: "((ubDom\<cdot>(\<Squnion>i. Y i) = {ch1, ch2}) \<leadsto> Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)])
                                            = Some (Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)])"
          using a1 h0 by auto
        have well1: "\<And>i. ubWell [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]"
          by (simp add: assms h0 map_io_well_2x1_ubwell2)
        have well2: "ubWell [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)]"
          using a1 assms h0 map_io_well_2x1_ubwell2 by fastforce
        then have c: "chain (\<lambda>i. (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))"
          proof -
            have h0: "chain (\<lambda>i. [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])"
              by (simp add: a1 part_map_chain)
            have h1: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> ubWell x \<Longrightarrow> ubWell y  \<Longrightarrow> Abs_ubundle x \<sqsubseteq> Abs_ubundle y"
              by (simp add: below_ubundle_def)
            show ?thesis
              apply(rule chainI)
              using h0 h1 po_class.chain_def well1 by blast
          qed
        have r: "range (\<lambda>i. (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])) <<| (\<Squnion>i. (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))"
          by (simp add: c cpo_lubI)
        have e: "(\<Squnion>i. (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])) = (Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)])" 
          proof -
            have g1: "(\<Squnion>i. (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])) = (Abs_ubundle (\<Squnion>i. [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))"
              by (simp add: a1 assms h0 map_io_well_2x1_ubwell2 part_map_chain)
            have g2: "(Abs_ubundle (\<Squnion>i. [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])) = (Abs_ubundle [ch3 \<mapsto> (\<Squnion>i. f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2))])"
              by (simp add: map_lub a1)
            have g3: "(Abs_ubundle [ch3 \<mapsto> (\<Squnion>i. f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2))]) = (Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i .ch1))\<cdot>((\<Squnion>i. Y i .ch2))])"
              by (simp add: a1 lub_APP)
            have g4: "(Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i .ch1))\<cdot>((\<Squnion>i. Y i .ch2))]) = (Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)])"
              by (simp add: a1 contlub_cfun_arg)
            show ?thesis
              using g1 g2 g3 g4 by auto      
          qed
        have f2: "range (\<lambda>i. (Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])) <<| (Abs_ubundle [ch3 \<mapsto> f\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)])"
          using e r by auto
        show ?thesis
          apply(simp add: h1 h2)
          using h0 is_lub_Some f2 by fastforce
      next
        case False
        have h1: "range (\<lambda>i. (ubDom\<cdot>(Y i) = {ch1, ch2}) \<leadsto> Abs_ubundle [ch3 \<mapsto> f\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]) = {None}"
          using False by auto
        then show ?thesis
          using False a1 is_lub_singleton by auto
      qed
  qed

lemma uf_2x1_well[simp]: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "ufWell (\<Lambda> b. (ubDom\<cdot>b = {ch1, ch2}) \<leadsto> (Abs_ubundle [ch3 \<mapsto> f\<cdot>(b .ch1)\<cdot>(b .ch2)]))"  
  apply (rule ufun_wellI)
  apply (simp_all add: domIff2 assms)
  apply (simp_all add: ubclDom_ubundle_def)
  apply (simp add: ubdom_insert)
  by (simp add: assms map_io_well_2x1_ubwell2 ubdom_insert)

lemma uf_2x1_rep_dom: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "ufDom\<cdot>(Abs_cufun (\<lambda>b::'a\<^sup>\<Omega>. (ubDom\<cdot>b = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f\<cdot>(b  .  ch1)\<cdot>(b  .  ch2)])) = {ch1, ch2}"
  apply(simp add: ufDom_def assms)
  apply(simp add: assms domIff2)
  apply (fold ubclDom_ubundle_def)
  apply (rule someI_ex)
  by (simp add: ubundle_ex)

lemma uf_2x1_dom[simp]: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "ufDom\<cdot>(uf_2x1 f (ch1, ch2, ch3)) = {ch1, ch2}"
  apply(simp only: uf_2x1_def fst_conv snd_conv)
  by(simp add: uf_2x1_rep_dom assms)

lemma uf_2x1_ran[simp]: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "ufRan\<cdot>(uf_2x1 f (ch1, ch2, ch3)) = {ch3}"
  apply(simp only: uf_2x1_def fst_conv snd_conv)
  apply(simp add: ufran_least)
  apply(subst rep_abs_cufun)
  apply(simp add: assms) +
  apply(fold ubclDom_ubundle_def)
  apply(simp add: ubcldom_least_cs)
  apply(simp add: ubclDom_ubundle_def)
  apply(simp add: assms uf_2x1_rep_dom)
  apply(simp add: ubclLeast_ubundle_def)
  by (metis (full_types) assms dom_eq_singleton_conv map_io_well_2x1_def ubWell_empty
                         ubdom_ubrep_eq ubrep_ubabs ubsetch_well usclOkay_bot)

(* Equation for Rep_cufun *)
lemma uf_2x1_rep_eq: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
    shows "Rep_cufun (uf_2x1 f (ch1, ch2, ch3)) 
                                = (\<lambda>b. (ubDom\<cdot>b = {ch1, ch2}) 
                                        \<leadsto> (Abs_ubundle [ch3 \<mapsto> f\<cdot>(b .ch1)\<cdot>(b .ch2)]))"
  apply(simp add: uf_2x1_def)
  apply(subst snd_conv, subst fst_conv)+
  apply(simp add: assms)
  apply(subst snd_conv)
  by simp

(* Applying uf_2x1 *)
lemma uf_2x1_apply: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
      and "usclOkay ch1 s1"
      and "usclOkay ch2 s2"
      and "ch1 \<noteq> ch2"
    shows "(uf_2x1 f (ch1, ch2, ch3)) \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2]) = (Abs_ubundle [ch3 \<mapsto> f\<cdot>s1\<cdot>s2])"
  apply(simp add: assms(1) uf_2x1_rep_eq ub_eq ubgetch_insert)
  apply(simp add: ubWell_def assms(2) assms(3) ubdom_ubrep_eq)
  apply(simp add: assms(4))
  by (simp add: doubleton_eq_iff)

lemma uf_2x1_apply2: 
  assumes "map_io_well_2x1 usclOkay f ch1 ch2 ch3"
      and "usclOkay ch1 s1"
      and "ch1 = ch2"
    shows "(uf_2x1 f (ch1, ch2, ch3)) \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s1]) = (Abs_ubundle [ch3 \<mapsto> f\<cdot>s1\<cdot>s1])"
  apply(simp add: assms(1) uf_2x1_rep_eq ub_eq ubgetch_insert)
  apply(simp add: ubWell_def assms(2)  ubdom_ubrep_eq)
  using assms(2) assms(3) by auto


subsection \<open>2x2\<close>

lemma uf_2x2_mono[simp]:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "monofun (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {ch1, ch2}) 
                          \<leadsto> (Abs_ubundle [ch3\<mapsto>f1\<cdot>(sb .ch1)\<cdot>(sb .ch2), ch4\<mapsto>f2\<cdot>(sb .ch1)\<cdot>(sb .ch2)]))"
  proof (rule monofunI)
    fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
    assume a1: "x \<sqsubseteq> y"
    show "(ubDom\<cdot>x = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(x .ch1)\<cdot>(x .ch2), ch4 \<mapsto> f2\<cdot>(x .ch1)\<cdot>(x .ch2)] \<sqsubseteq>
          (ubDom\<cdot>y = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(y .ch1)\<cdot>(y .ch2), ch4 \<mapsto> f2\<cdot>(y .ch1)\<cdot>(y .ch2)]"
      proof (cases "(ubDom\<cdot>x = {ch1, ch2})")
        case True
        have h1: "(ubDom\<cdot>y = {ch1, ch2})"
          proof -
            have f1: "(ubclDom\<cdot>x = {ch1, ch2})"
              by(simp add: True ubclDom_ubundle_def)
            have f2: "(ubclDom\<cdot>y = {ch1, ch2})"
              using a1 f1 ubcldom_fix by blast
            show ?thesis
              by (metis f2 ubclDom_ubundle_def)
          qed
        have h2: "(ubDom\<cdot>x = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(x .ch1)\<cdot>(x .ch2), ch4 \<mapsto> f2\<cdot>(x .ch1)\<cdot>(x .ch2)]
                                 = Some (Abs_ubundle [ch3 \<mapsto> f1\<cdot>(x .ch1)\<cdot>(x .ch2), ch4 \<mapsto> f2\<cdot>(x .ch1)\<cdot>(x .ch2)])"
          using True by auto
        have h3: "(ubDom\<cdot>y = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(y .ch1)\<cdot>(y .ch2), ch4 \<mapsto> f2\<cdot>(y .ch1)\<cdot>(y .ch2)]
                                 = Some (Abs_ubundle [ch3 \<mapsto> f1\<cdot>(y .ch1)\<cdot>(y .ch2), ch4 \<mapsto> f2\<cdot>(y .ch1)\<cdot>(y .ch2)])"
          using h1 by auto
        have h4: "ubWell [ch3 \<mapsto> f1\<cdot>(x .ch1)\<cdot>(x .ch2), ch4 \<mapsto> f2\<cdot>(x .ch1)\<cdot>(x .ch2)]"
          by (simp add: True assms map_io_well_2x2_ubwell2)
        have h5: "ubWell [ch3 \<mapsto> f1\<cdot>(y .ch1)\<cdot>(y .ch2), ch4 \<mapsto> f2\<cdot>(y .ch1)\<cdot>(y .ch2)]"
          by (simp add: h1 assms map_io_well_2x2_ubwell2)
        have hh12: "Abs_ubundle [ch3 \<mapsto> f1\<cdot>(x .ch1)\<cdot>(x .ch2), ch4 \<mapsto> f2\<cdot>(x .ch1)\<cdot>(x .ch2)] \<sqsubseteq>
                    Abs_ubundle [ch3 \<mapsto> f1\<cdot>(y .ch1)\<cdot>(y .ch2), ch4 \<mapsto> f2\<cdot>(y .ch1)\<cdot>(y .ch2)]"
          by (simp add: a1 fun_upd_same h4 h5 monofun_Rep_cfun2 monofun_cfun monofun_def ubrep_lessI)      
        show ?thesis
          by(simp add: h3 h4 True h1 some_below hh12)
      next
        case False
        then show ?thesis
          proof -
            have h1: "ubDom\<cdot>y \<noteq> {ch1, ch2}"
              proof -
                have f1: "(ubclDom\<cdot>x \<noteq> {ch1, ch2})"
                  by(simp add: False ubclDom_ubundle_def)
                have f2: "(ubclDom\<cdot>y \<noteq> {ch1, ch2})"
                  using a1 f1 ubcldom_fix by blast
                show ?thesis
                  by (metis f2 ubclDom_ubundle_def)
              qed
            show ?thesis
              using False h1 by auto
          qed
      qed
  qed

lemma ufun_2x2_chain[simp]:
  assumes "chain Y"
      and "ubDom\<cdot>(Y 0) = {ch1,ch2}"
      and "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "chain (\<lambda> i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>((Y i) .ch1)\<cdot>((Y i) .ch2),
                                    ch4 \<mapsto> f2\<cdot>((Y i) .ch1)\<cdot>((Y i) .ch2)])"
  apply(rule chainI)
  apply(rule ub_below)
  proof -
    have h1: "\<And>i. ubWell [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]"
      using assms map_io_well_2x2_ubwell2 ubdom_chain_eq3 by fastforce
    show "\<And>i::nat. ubDom\<cdot>(Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]) =
              ubDom\<cdot>(Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y (Suc i) .ch1)\<cdot>(Y (Suc i) .ch2), ch4 \<mapsto> f2\<cdot>(Y (Suc i) .ch1)\<cdot>(Y (Suc i) .ch2)])"
      by(simp add: ubDom_def h1)
  next
    have h1: "\<And>i. ubWell [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]"
      using assms map_io_well_2x2_ubwell2 ubdom_chain_eq3 by fastforce
    show "\<And>(i::nat) c::channel.
       c \<in> ubDom\<cdot>(Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2), ch4 \<mapsto> f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2)]) \<Longrightarrow>
       Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2), ch4 \<mapsto> f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2)]  .  c \<sqsubseteq>
       Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y (Suc i)  .  ch1)\<cdot>(Y (Suc i)  .  ch2), ch4 \<mapsto> f2\<cdot>(Y (Suc i)  .  ch1)\<cdot>(Y (Suc i)  .  ch2)]  .  c"
      apply(simp add: ubDom_def h1)
      apply(simp add: h1 ubgetch_ubrep_eq)  
      by (meson assms(1) monofun_cfun monofun_cfun_arg po_class.chain_def)  
  qed

lemma ufun_2x2_chain_lub[simp]: 
  assumes "chain Y"
      and "ubDom\<cdot>(Lub Y) = {ch1,ch2}"
      and "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "chain (\<lambda> i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2),
                                    ch4 \<mapsto> f2\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)])"
  proof -
    have a: "ubDom\<cdot>(Y 0) = {ch1,ch2}"
      using assms(1) assms(2) by auto
    show ?thesis
      by (simp add: a assms(1) assms(3))
  qed
    
lemma ufun_2x2_Lub:
  assumes "chain Y" 
      and "ubDom\<cdot>(Lub Y) = {ch1,ch2}"
      and "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
     shows "(\<Squnion>i. f\<cdot>(Y i . ch1)\<cdot>(Y i . ch2)) = f\<cdot>((Lub Y) . ch1)\<cdot>((Lub Y). ch2)"
  proof -
    have f1: "\<forall>f fa. (\<not> chain f \<or> \<not> chain fa) \<or> (\<Squnion>n. (f n\<cdot>(fa n::'a)::'c)) = Lub f\<cdot>(Lub fa)"
      using lub_APP by blast
    have f2: "\<forall>f c. \<not> chain f \<or> chain (\<lambda>n. c\<cdot>(f n::'a\<^sup>\<Omega>)::'a)"
      using ch2ch_Rep_cfunR by blast
    have f3: "\<forall>f c. \<not> chain f \<or> chain (\<lambda>n. c\<cdot>(f n::'a)::'a \<rightarrow> 'c)"
      using ch2ch_Rep_cfunR by blast
    have f4: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'a\<^sup>\<Omega>)::'a) = (\<Squnion>n. c\<cdot>(f n))"
      using contlub_cfun_arg by blast
    have "(\<Squnion>n. f\<cdot>(Y n . ch1)) = f\<cdot>(Lub Y . ch1)"
      by (simp add: assms(1) contlub_cfun_arg)
    then show ?thesis
      using f4 f3 f2 f1 assms(1) by presburger
  qed

lemma uf_2x2_cont[simp]:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "cont (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {ch1, ch2}) 
                          \<leadsto> (Abs_ubundle [ch3\<mapsto>f1\<cdot>(sb .ch1)\<cdot>(sb .ch2), ch4\<mapsto>f2\<cdot>(sb .ch1)\<cdot>(sb .ch2)]))"
  apply(rule contI2)
  apply(simp add: assms)
  apply(rule allI, rule impI) (* TODO Beweis ist Katastrophe *)
  proof -
    fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume a1: "chain Y"
    show "(ubDom\<cdot>(\<Squnion>i. Y i) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2), ch4 \<mapsto> f2\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)]
       \<sqsubseteq> (\<Squnion>i. (ubDom\<cdot>(Y i) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i. ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])"
      proof (cases "ubDom\<cdot>(\<Squnion>i. Y i) =  {ch1, ch2}")
        case True
        have h1: "(ubDom\<cdot>(\<Squnion>i. Y i) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2), ch4 \<mapsto> f2\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)]
                  = Some (Abs_ubundle [ch3 \<mapsto> f1\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2), ch4 \<mapsto> f2\<cdot>((\<Squnion>i. Y i) .ch1)\<cdot>((\<Squnion>i. Y i) .ch2)])"
          by (simp add: True)
        have h2: "(\<Squnion>i. (ubDom\<cdot>(Y i) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i. ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])
                  = (\<Squnion>i. Some (Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i. ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))"
          using True a1 by auto
        have h4: "(\<Squnion>i. Some (Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i. ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))
                 =  Some (\<Squnion>i. (Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i. ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)]))"
          by (simp add: a1 assms True some_lub_chain_eq)
        have h31: "\<And>i. ubWell [ch3 \<mapsto> f1\<cdot>(Y i  .ch1)\<cdot>(Y i  .ch2), ch4 \<mapsto> f2\<cdot>(Y i  .ch1)\<cdot>(Y i  .ch2)]"
          by (simp add: True a1 assms map_io_well_2x2_ubwell2)
        have h331: "usclOkay ch4 (\<Squnion>i::nat. f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2))"
          proof -
            have f1: "\<forall>c. usclOkay c Rep_ubundle (Lub Y)\<rightharpoonup>c \<or> c \<notin> {ch1, ch2}"
              by (metis (no_types) True ubdom_channel_usokay)
            have f2: "\<forall>c f. (\<Squnion>n. (f n . c::'a)) = Rep_ubundle (Lub f)\<rightharpoonup>c \<or> \<not> chain f"
              by (metis (no_types) contlub_cfun_arg ubgetch_insert)
            then have f3: "\<forall>c f fa. (Lub f\<cdot>Rep_ubundle (Lub fa)\<rightharpoonup>c = (\<Squnion>n. (f n\<cdot>(fa n . c::'a)::'a)) \<or> \<not> chain f) \<or> \<not> chain fa"
              by (metis (no_types) ch2ch_Rep_cfunR lub_APP)
            have f4: "\<forall>C c ca. (ca::channel) \<in> insert c (insert ca C)"
              by blast
            have f5: "\<forall>c ca cb cc a cd ce. ((usclOkay c (cd\<cdot>a\<cdot>Rep_ubundle (Lub Y)\<rightharpoonup>ca) \<or> ca \<notin> {ch1, ch2}) \<or> \<not> map_io_well_2x2 usclOkay cd cc ce ca c cb) \<or> \<not> usclOkay ce a"
              using f1 by (meson map_io_well_2x2_def)
            have "\<forall>c ca cb cc cd. (usclOkay c (cb\<cdot>Rep_ubundle (Lub Y)\<rightharpoonup>ch1\<cdot> Rep_ubundle (Lub Y)\<rightharpoonup>ch2) \<or> map_io_well_2x2 usclOkay f2 f1 cc ch2 ch4 ch3) \<or> \<not> map_io_well_2x2 usclOkay cd cb ch1 ch2 ca c"
              using f4 f1 by (meson assms insertI1 map_io_well_2x2_def)
            then have "usclOkay ch4 (f2\<cdot>(\<Squnion>n. Y n . ch1)\<cdot> Rep_ubundle (Lub Y)\<rightharpoonup>ch2) \<and> chain (\<lambda>n. Y n . ch1)"
              using f5 f4 f2 f1 by (metis (no_types) a1 assms ch2ch_Rep_cfunR insertI1)
            then show ?thesis
              using f3 by (metis (no_types) a1 ch2ch_Rep_cfunR contlub_cfun_arg)
          qed
        have h332: "usclOkay ch3 (\<Squnion>i::nat. f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2))"
          proof -
            have f1: "\<forall>c. usclOkay c Rep_ubundle (Lub Y)\<rightharpoonup>c \<or> c \<notin> {ch1, ch2}"
              by (metis (no_types) True ubdom_channel_usokay)
            have f2: "\<forall>c f. (\<Squnion>n. (f n . c::'a)) = Rep_ubundle (Lub f)\<rightharpoonup>c \<or> \<not> chain f"
              by (metis (no_types) contlub_cfun_arg ubgetch_insert)
            then have f3: "\<forall>c f fa. (Lub f\<cdot>Rep_ubundle (Lub fa)\<rightharpoonup>c = (\<Squnion>n. (f n\<cdot>(fa n . c::'a)::'a)) \<or> \<not> chain f) \<or> \<not> chain fa"
              by (metis (no_types) ch2ch_Rep_cfunR lub_APP)
            have f4: "\<forall>C c ca. (ca::channel) \<in> insert c (insert ca C)"
              by blast
            have f5: "\<forall>c ca cb cc a cd ce. ((usclOkay c (cd\<cdot>a\<cdot>Rep_ubundle (Lub Y)\<rightharpoonup>ca) \<or> ca \<notin> {ch1, ch2}) \<or> \<not> map_io_well_2x2 usclOkay cd cc ce ca c cb) \<or> \<not> usclOkay ce a"
              using f1 by (meson map_io_well_2x2_def)
            have "\<forall>c ca cb cc cd. (usclOkay c (cb\<cdot>Rep_ubundle (Lub Y)\<rightharpoonup>ch1\<cdot> Rep_ubundle (Lub Y)\<rightharpoonup>ch2) \<or> map_io_well_2x2 usclOkay f2 f1 cc ch2 ch4 ch3) \<or> \<not> map_io_well_2x2 usclOkay cd cb ch1 ch2 ca c"
              using f4 f1 by (meson assms insertI1 map_io_well_2x2_def)
            then have "usclOkay ch3 (f1\<cdot>(\<Squnion>n. Y n . ch1)\<cdot> Rep_ubundle (Lub Y)\<rightharpoonup>ch2) \<and> chain (\<lambda>n. Y n . ch1)"
              using f5 f4 f2 f1 by (metis (no_types) a1 assms ch2ch_Rep_cfunR insertI1)
            then show ?thesis
              using f3 by (metis (no_types) a1 ch2ch_Rep_cfunR contlub_cfun_arg)
          qed
        have h33: "ubWell [ch3 \<mapsto> \<Squnion>i::nat. f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2), ch4 \<mapsto> \<Squnion>i::nat. f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2)]"
          apply(simp add: ubWell_def)
          apply(rule conjI, rule impI)
          by(simp add: h331 h332)+
        have dom: "\<And>i. ubDom\<cdot>(Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2), ch4 \<mapsto> f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2)]) = {ch3, ch4}"
          by (simp add: h31 insert_commute ubdom_ubrep_eq)  
        have dom_lub: "ubDom\<cdot>(\<Squnion>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2), ch4 \<mapsto> f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2)]) = {ch3, ch4}"    
          proof -
            have chain: "chain (\<lambda>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2), ch4 \<mapsto> f2\<cdot>(Y i  .  ch1)\<cdot>(Y i  .  ch2)])"
              by (simp add: True a1 assms)
            then show ?thesis
              using dom ubdom_chain_eq2 by blast
          qed
        have h60: "ch3 \<noteq> ch4"
          by (metis assms map_io_well_2x2_def)
        have h61: "chain (\<lambda>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])"
          by (simp add: True a1 assms)
        have h62: "ch3 \<in> ubDom\<cdot>(\<Squnion>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])"
          using dom_lub by blast
        have h62b: "ch4 \<in> ubDom\<cdot>(\<Squnion>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])"
          using dom_lub by blast
        have h63: "\<And>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)] .ch3 = f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)"
          apply (simp add: h31 ubgetch_ubrep_eq)
          by (metis assms map_io_well_2x2_def)
        have h63b: "\<And>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)] .ch4 = f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)"
          by (simp add: h31 ubgetch_ubrep_eq)
        from h33 have h64: "Abs_ubundle [ch3 \<mapsto> \<Squnion>i. f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> \<Squnion>i. f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)] .ch3 = (\<Squnion>i. f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2))"
          apply (simp add: h33 ubgetch_ubrep_eq)
          by (metis assms map_io_well_2x2_def)
        from h33 have h64b: "Abs_ubundle [ch3 \<mapsto> \<Squnion>i. f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> \<Squnion>i. f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)] .ch4 = (\<Squnion>i. f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2))"
          by (simp add: h33 ubgetch_ubrep_eq)
        have h6: "(\<Squnion>i. Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2), ch4 \<mapsto> f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)])
                = Abs_ubundle [ch3 \<mapsto> (\<Squnion>i. f1\<cdot>(Y i .ch1)\<cdot>(Y i .ch2)), ch4 \<mapsto> (\<Squnion>i. f2\<cdot>(Y i .ch1)\<cdot>(Y i .ch2))]"
          apply(rule ubgetchI)
          apply(simp add: dom_lub)
          apply (simp add: h33 insert_commute ubdom_ubrep_eq)
          apply(simp add: dom_lub)
          apply auto
          apply (simp add:  h61 h62 ubgetch_lub h33 ubgetch_ubrep_eq h60 h63 h64)
          by (simp add:  h61 h62b ubgetch_lub h31 ubgetch_ubrep_eq h60 h63b h64b)
        show ?thesis 
          apply(simp only: h1 h2 h4 h6)
          proof - (* TODO müsste viel leichter mit _Lub Lemma gehen *)
            have f1: "\<forall>f c. \<not> chain f \<or> chain (\<lambda>n. c\<cdot>(f n::'a\<^sup>\<Omega>)::'a)"
              using ch2ch_Rep_cfunR by blast
            then have f2: "chain (\<lambda>n. Y n . ch1)"
              by (metis a1)
            then have f3: "(\<Squnion>n. f1\<cdot>(Y n . ch1)\<cdot>(Y n . ch2)) = (\<Squnion>n. f1\<cdot>(Y n . ch1))\<cdot>(\<Squnion>n. Y n . ch2)"
              using f1 a1 ch2ch_Rep_cfunR lub_APP by blast
            have f4: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'a\<^sup>\<Omega>)::'a) = (\<Squnion>n. c\<cdot>(f n))"
              by (metis contlub_cfun_arg)
            have f5: "(\<Squnion>n. f1\<cdot>(Y n . ch1)\<cdot>(Y n . ch2)) = f1\<cdot>(Lub Y . ch1)\<cdot>(Lub Y . ch2)"
              using f3 by (simp add: a1 contlub_cfun_arg)
            have f6: "(\<Squnion>n. f2\<cdot>(Y n . ch1)\<cdot>(Y n . ch2)) = (\<Squnion>n. f2\<cdot>(Y n . ch1))\<cdot>(\<Squnion>n. Y n . ch2)"
              using f2 f1 a1 ch2ch_Rep_cfunR lub_APP by blast
            have "(\<Squnion>n. f2\<cdot>(Y n . ch1)) = f2\<cdot>(Lub Y . ch1)"
              by (simp add: a1 contlub_cfun_arg)
            then show "Some (Abs_ubundle [ch3 \<mapsto> f1\<cdot>((\<Squnion>n. Y n) . ch1)\<cdot> ((\<Squnion>n. Y n) . ch2), ch4 \<mapsto> f2\<cdot>((\<Squnion>n. Y n) . ch1)\<cdot> ((\<Squnion>n. Y n) . ch2)]) \<sqsubseteq> Some (Abs_ubundle [ch3 \<mapsto> \<Squnion>n. f1\<cdot>(Y n . ch1)\<cdot>(Y n . ch2), ch4 \<mapsto> \<Squnion>n. f2\<cdot>(Y n . ch1)\<cdot>(Y n . ch2)])"
              using f6 f5 f4 a1 by auto
          qed
      next
        case False
        show ?thesis
          by (simp add: False a1)
      qed
  qed

lemma uf_2x2_well[simp]:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "ufWell (\<Lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {ch1, ch2}) 
                          \<leadsto> (Abs_ubundle [ch3\<mapsto>f1\<cdot>(sb .ch1)\<cdot>(sb .ch2), ch4\<mapsto>f2\<cdot>(sb .ch1)\<cdot>(sb .ch2)]))"
  apply(simp add: ufWell_def)
  apply(rule conjI)
  subgoal
  apply (rule_tac x="{ch1, ch2}" in exI)
  apply (rule allI) 
  apply (simp add: ubclDom_ubundle_def)
  apply (simp add: assms)
  by (simp add: domIff)
  apply (rule_tac x="{ch3, ch4}" in exI)
  apply(rule allI)
  apply (simp add: ubclDom_ubundle_def)
  apply (simp add: assms)
  apply(rule impI)
  proof -
    fix b :: "'a\<^sup>\<Omega>"
    assume a1: "b \<in> ran (\<lambda>sb. (ubDom\<cdot>sb = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(sb . ch1)\<cdot>(sb . ch2), ch4 \<mapsto> f2\<cdot>(sb . ch1)\<cdot> (sb . ch2)])"
    have f2: "\<forall>c ca cb cc cd ce u. (\<not> map_io_well_2x2 usclOkay c ca cb cc cd ce \<or> cb \<notin> ubDom\<cdot>u \<or> cc \<notin> ubDom\<cdot>u) \<or> ubWell [cd \<mapsto> c\<cdot>(u . cb::'a)\<cdot>(u . cc), ce \<mapsto> ca\<cdot>(u . cb)\<cdot>(u . cc)]"
      using map_io_well_2x2_ubwell2 by blast
    obtain uu :: "('a\<^sup>\<Omega> \<Rightarrow> ('a\<^sup>\<Omega>) option) \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega>" where f3: "\<forall>u f. u \<notin> ran f \<or> f (uu f u) = Some u"
      by (meson ran2exists)
    then have "(ubDom\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2), ch4 \<mapsto> f2\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2)] = Some b"
      using a1 by blast
    then have f4: "ubDom\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b) = {ch1, ch2}"
      by (metis option.simps(3))
    have f5: "(ubDom\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b) = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2), ch4 \<mapsto> f2\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2)] = Some b"
      using f3 a1 by auto
    have f6: "{ch3, ch4} = insert ch4 (dom [ch3 \<mapsto> f1\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2)])"
      by (simp add: insert_commute)
    have "ubDom\<cdot> (Abs_ubundle [ch3 \<mapsto> f1\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2), ch4 \<mapsto> f2\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2)]) = dom [ch3 \<mapsto> f1\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2), ch4 \<mapsto> f2\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch1)\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {ch1, ch2})\<leadsto>Abs_ubundle [ch3 \<mapsto> f1\<cdot>(u . ch1)\<cdot>(u . ch2), ch4 \<mapsto> f2\<cdot>(u . ch1)\<cdot>(u . ch2)]) b . ch2)]"
      using f4 f2 by (simp add: assms ubdom_ubrep_eq)
    then show "ubDom\<cdot>b = {ch3, ch4}"
      using f6 f5 f4 by simp
  qed

lemma uf_2x2_rep_dom:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "ufDom\<cdot>(Abs_cufun (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {ch1, ch2}) 
                          \<leadsto> (Abs_ubundle [ch3\<mapsto>f1\<cdot>(sb . ch1)\<cdot>(sb . ch2),
                                           ch4\<mapsto>f2\<cdot>(sb . ch1)\<cdot>(sb . ch2)]))) = {ch1, ch2}"
  apply(simp add:  ufDom_def)
  apply(simp only: assms uf_2x2_well uf_2x2_cont rep_abs_cufun fst_conv snd_conv)
  apply(simp add: ubclDom_ubundle_def)
  apply(simp add: assms domIff2)
  apply (fold ubclDom_ubundle_def)
  apply (rule someI_ex)
  by (simp add: ubundle_ex)

lemma uf_2x2_dom:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "ufDom\<cdot>(uf_2x2 f1 f2 (ch1, ch2) (ch3, ch4)) = {ch1, ch2}"
  apply(simp add: uf_2x2_def)
  apply(subst fst_conv)+
  apply(subst snd_conv)+
  by(simp add: assms uf_2x2_rep_dom)

lemma uf_2x2_ran:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
    shows "ufRan\<cdot>(uf_2x2 f1 f2 (ch1, ch2) (ch3, ch4)) = {ch3, ch4}"
  apply(simp only: uf_2x2_def fst_conv snd_conv)
  apply(simp add: ufran_least)
  apply(subst rep_abs_cufun)
  apply(simp add: assms) +
  apply(fold ubclDom_ubundle_def)
  apply(simp add: ubcldom_least_cs)
  apply(simp add: ubclDom_ubundle_def)
  apply(simp add: assms uf_2x2_rep_dom)
  apply(simp add: ubclLeast_ubundle_def)
  proof -
    have "ubWell [ch3 \<mapsto> f1\<cdot>\<bottom>\<cdot>\<bottom>, ch4 \<mapsto> f2\<cdot>\<bottom>\<cdot>\<bottom>]"
      by (metis (no_types) assms map_io_well_2x2_ubwell usclOkay_bot)
    then show "ubDom\<cdot> (Abs_ubundle [ch3 \<mapsto> f1\<cdot>\<bottom>\<cdot>\<bottom>, ch4 \<mapsto> f2\<cdot>\<bottom>\<cdot>\<bottom>]) = {ch3, ch4}"
      by (simp add: insert_commute ubdom_ubrep_eq)
  qed

lemma uf_2x2_apply:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
      and "usclOkay ch1 s1"
      and "usclOkay ch2 s2"
      and "ch1 \<noteq> ch2"
      and "ch3 \<noteq> ch4"
    shows "(uf_2x2 f1 f2 (ch1, ch2) (ch3, ch4)) \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2])
         = (Abs_ubundle [ch3 \<mapsto> f1\<cdot>s1\<cdot>s2, ch4 \<mapsto> f2\<cdot>s1\<cdot>s2])"
  apply(simp add: uf_2x2_def)
  apply(subst fst_conv)+
  apply(subst snd_conv)+
  apply(simp add: assms)
  apply(rule conjI)
  apply(rule impI)
  proof -
    have "\<forall>c a u. \<not> usclOkay c (a::'a) \<or> ubWell (Rep_ubundle u(c \<mapsto> a))"
      using ubsetch_well by blast
    then have f1: "ubWell [ch1 \<mapsto> s1, ch2 \<mapsto> s2]"
      by (metis assms(2) assms(3) ubWell_empty ubrep_ubabs)
    then have f2: "Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2] . ch1 = Some\<rightharpoonup>s1"
      by (simp add: assms(4) ubgetch_ubrep_eq)
    have "Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2] . ch2 = Some\<rightharpoonup>s2"
      using f1 by (simp add: ubgetch_ubrep_eq)
    then show "Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2] . ch1)\<cdot> (Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2] . ch2), ch4 \<mapsto> f2\<cdot>(Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2] . ch1)\<cdot> (Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2] . ch2)] = Abs_ubundle [ch3 \<mapsto> f1\<cdot>s1\<cdot>s2, ch4 \<mapsto> f2\<cdot>s1\<cdot>s2]"
      using f2 by simp
  next
    show "ubDom\<cdot>(Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2]) \<noteq> {ch1, ch2} \<longrightarrow> the None = Abs_ubundle [ch3 \<mapsto> f1\<cdot>s1\<cdot>s2, ch4 \<mapsto> f2\<cdot>s1\<cdot>s2]"
      by (metis (full_types) assms(2) assms(3) dom_empty dom_fun_upd insert_commute option.simps(3) ubWell_empty ubdom_ubrep_eq ubrep_ubabs ubsetch_well)
  qed

lemma uf_2x2_apply2:
  assumes "map_io_well_2x2 usclOkay f1 f2 ch1 ch2 ch3 ch4"
      and "usclOkay ch1 s"
      and "ch1 = ch2"
      and "ch3 \<noteq> ch4"
    shows "(uf_2x2 f1 f2 (ch1, ch2) (ch3, ch4)) \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s])
         = (Abs_ubundle [ch3 \<mapsto> f1\<cdot>s\<cdot>s, ch4 \<mapsto> f2\<cdot>s\<cdot>s])"
  apply(simp add: uf_2x2_def)
  apply(subst fst_conv)+
  apply(subst snd_conv)+
  apply(simp add: assms(1))
  apply(rule conjI)
  apply(rule impI)
  apply(simp add: assms)
  proof -
    assume a1: "ubDom\<cdot>(Abs_ubundle [ch2 \<mapsto> s]) = {ch2}"
    have h2: "Abs_ubundle [ch2 \<mapsto> s] .ch2 = s"
      by (metis (full_types) assms(2) assms(3) fun_upd_same option.sel ubWell_empty ubgetch_ubrep_eq ubrep_ubabs ubsetch_well)
    show "Abs_ubundle [ch3 \<mapsto> f1\<cdot>(Abs_ubundle [ch2 \<mapsto> s]  .  ch2)\<cdot>(Abs_ubundle [ch2 \<mapsto> s]  .  ch2), ch4 \<mapsto> f2\<cdot>(Abs_ubundle [ch2 \<mapsto> s]  .  ch2)\<cdot>(Abs_ubundle [ch2 \<mapsto> s]  .  ch2)] =
    Abs_ubundle [ch3 \<mapsto> f1\<cdot>s\<cdot>s, ch4 \<mapsto> f2\<cdot>s\<cdot>s]"
      by(simp add: h2)
  next
    show "ubDom\<cdot>(Abs_ubundle [ch1 \<mapsto> s]) \<noteq> {ch1, ch2} \<longrightarrow> the None = Abs_ubundle [ch3 \<mapsto> f1\<cdot>s\<cdot>s, ch4 \<mapsto> f2\<cdot>s\<cdot>s]"
      by (metis assms(2) assms(3) dom_empty dom_fun_upd insert_absorb2 option.simps(3) ubWell_empty ubdom_ubrep_eq ubrep_ubabs ubsetch_well)
  qed  


(* ----------------------------------------------------------------------- *)
section \<open>Predefined UFuns\<close>
(* ----------------------------------------------------------------------- *)

subsection \<open>Definitions\<close>

(* 1x1 -- Universal identity function *)
definition uf_id :: "(channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_id cs \<equiv> uf_1x1 ID cs"

(* 2x1 -- Universal function adding two streams *)
instantiation nat :: message
begin
  fun ctype_nat :: "channel \<Rightarrow> nat set" where
    "ctype_nat c = range nat"
  instance ..
end

definition uf_add :: "(channel \<times> channel \<times> channel) \<Rightarrow> (nat stream\<^sup>\<Omega>) ufun" where
"uf_add cs \<equiv> uf_2x1 add cs"

(* 2x2 -- Universal function swapping two channels around *)
definition swap1 :: "'a \<rightarrow> 'a \<rightarrow> 'a" where
"swap1 \<equiv> \<Lambda> a b. a"

definition swap2 :: "'a \<rightarrow> 'a \<rightarrow> 'a" where
"swap2 \<equiv> \<Lambda> a b. b"

definition uf_swap :: "(channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_swap cs \<equiv> uf_2x2 (swap1::'a \<rightarrow> 'a \<rightarrow> 'a) (swap2::'a \<rightarrow> 'a \<rightarrow> 'a) cs (snd cs, fst cs)"


subsection \<open>Lemmas\<close>

subsubsection \<open>uf_id\<close>

lemma uf_id_dom: assumes "map_io_well_1x1 usclOkay (ID::'a \<rightarrow> 'a) ch1 ch2"
                   shows "ufDom\<cdot>((uf_id::(channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun) (ch1, ch2)) = {ch1}"
  by(simp add: uf_id_def assms)

lemma uf_id_ran: assumes "map_io_well_1x1 usclOkay (ID::'a \<rightarrow> 'a) ch1 ch2"
                   shows "ufRan\<cdot>((uf_id::(channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun) (ch1, ch2)) = {ch2}"
  by(simp add: uf_id_def assms)

lemma uf_id_apply: assumes "map_io_well_1x1 usclOkay (ID::'a \<rightarrow> 'a) ch1 ch2"
                       and "usclOkay ch1 s"
                     shows "((uf_id::(channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun) (ch1, ch2))
                                             \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s]) = (Abs_ubundle [ch2 \<mapsto> s])"
  by(simp add: uf_id_def assms uf_1x1_apply)


subsubsection \<open>uf_add\<close>

lemma uf_add_dom:
  assumes "map_io_well_2x1 usclOkay (add::nat stream \<rightarrow> nat stream \<rightarrow> nat stream) ch1 ch2 ch3"
    shows "ufDom\<cdot>((uf_add::(channel\<times>channel\<times>channel)\<Rightarrow>(nat stream\<^sup>\<Omega>) ufun) (ch1,ch2,ch3)) = {ch1,ch2}"
  by(simp add: uf_add_def assms)

lemma uf_add_ran:
  assumes "map_io_well_2x1 usclOkay (add::nat stream \<rightarrow> nat stream \<rightarrow> nat stream) ch1 ch2 ch3"
    shows "ufRan\<cdot>((uf_add::(channel\<times>channel\<times>channel) \<Rightarrow> (nat stream\<^sup>\<Omega>) ufun) (ch1,ch2,ch3)) = {ch3}"
  by(simp add: uf_add_def assms)

lemma uf_add_apply:
  assumes "map_io_well_2x1 usclOkay (add::nat stream \<rightarrow> nat stream \<rightarrow> nat stream) ch1 ch2 ch3"
      and "usclOkay ch1 s1"
      and "usclOkay ch2 s2"
      and "ch1 \<noteq> ch2"
    shows "((uf_add::(channel \<times> channel \<times> channel) \<Rightarrow> (nat stream\<^sup>\<Omega>) ufun) (ch1, ch2, ch3))
                           \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2]) = (Abs_ubundle [ch3 \<mapsto> add\<cdot>s1\<cdot>s2])"
  by(simp add: uf_add_def assms uf_2x1_apply)

lemma uf_add_apply2:
  assumes "map_io_well_2x1 usclOkay (add::nat stream \<rightarrow> nat stream \<rightarrow> nat stream) ch1 ch2 ch3"
      and "usclOkay ch1 s"
      and "ch1 = ch2"
    shows "((uf_add::(channel \<times> channel \<times> channel) \<Rightarrow> (nat stream\<^sup>\<Omega>) ufun) (ch1, ch2, ch3))
                           \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s]) = (Abs_ubundle [ch3 \<mapsto> add\<cdot>s\<cdot>s])"
  apply(simp add: uf_add_def)
  using assms uf_2x1_apply2 by auto


subsection \<open>uf_swap\<close>

lemma uf_swap_dom:
  assumes "map_io_well_2x2 usclOkay (swap1::'a \<rightarrow> 'a \<rightarrow> 'a) (swap2::'a \<rightarrow> 'a \<rightarrow> 'a) ch1 ch2 ch2 ch1"
    shows "ufDom\<cdot>((uf_swap::(channel\<times>channel)\<Rightarrow>('a\<^sup>\<Omega>) ufun) (ch1,ch2)) = {ch1,ch2}"
  by(simp add: uf_swap_def assms uf_2x2_dom)

lemma uf_swap_ran:
  assumes "map_io_well_2x2 usclOkay (swap1::'a \<rightarrow> 'a \<rightarrow> 'a) (swap2::'a \<rightarrow> 'a \<rightarrow> 'a) ch1 ch2 ch2 ch1"
    shows "ufRan\<cdot>((uf_swap::(channel\<times>channel)\<Rightarrow>('a\<^sup>\<Omega>) ufun) (ch1,ch2)) = {ch2,ch1}"
  by(simp add: uf_swap_def assms uf_2x2_ran)

lemma uf_swap_apply:
  assumes "map_io_well_2x2 usclOkay (swap1::'a \<rightarrow> 'a \<rightarrow> 'a) (swap2::'a \<rightarrow> 'a \<rightarrow> 'a) ch1 ch2 ch2 ch1"
      and "usclOkay ch1 s1"
      and "usclOkay ch2 s2"
      and "ch1 \<noteq> ch2"
    shows "((uf_swap::(channel\<times>channel)\<Rightarrow>('a\<^sup>\<Omega>) ufun) (ch1,ch2))
           \<rightleftharpoons> (Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2]) = (Abs_ubundle [ch2 \<mapsto> s1, ch1 \<mapsto> s2])"
  proof -
    have h1: "uf_2x2 swap1 swap2 (ch1, ch2) (ch2, ch1) \<rightleftharpoons> Abs_ubundle [ch1 \<mapsto> s1, ch2 \<mapsto> s2]
             = Abs_ubundle [ch2 \<mapsto> swap1\<cdot>s1\<cdot>s2, ch1 \<mapsto> swap2\<cdot>s1\<cdot>s2]"
      using assms uf_2x2_apply by blast
    have h2: "\<And>s1 s2. swap1\<cdot>s1\<cdot>s2 = s1"
      by(simp add: swap1_def)  
    have h3: "\<And>s1 s2. swap2\<cdot>s1\<cdot>s2 = s2"
      by(simp add: swap2_def)   
    show ?thesis
      by (simp add: h1 h2 h3 uf_swap_def)
  qed


end
