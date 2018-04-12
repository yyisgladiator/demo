(*  Title:  UFun_Templates.thy
    Author: Jens Christoph Bürger, David Duc Duong
    e-mail: jens.buerger@rwth-aachen.de, david.duong@rwth-aachen.de
    
    Description: Aggregates commonly used Ufun patterns with constructors.
    To instantiate a Ufun use the Ufun1x1, Ufun2x1 definition with an appropriate function which 
    automatically proves cont, ufun_well, dom, range for your definition.   
*)

(* NOTE: This instantiation uses the old cont, mono prove technique, for a more 
         modern/simplified approach use the ufun_contI and ufun_monoI2 lemmata from Ufun.thy *)

theory UFun_Templates
  imports UBundle_Pcpo UFun_Comp

begin

default_sort uscl_pcpo

definition map_io_well:: "(channel \<Rightarrow> 'a::uscl \<Rightarrow> bool) \<Rightarrow> ('a \<rightarrow> 'a) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> bool" 
  where "map_io_well P f ch1 ch2 \<equiv> \<forall> x. P ch1 x = P ch2 (f\<cdot>x)"

(* ----------------------------------------------------------------------- *)
section \<open>General\<close>
(* ----------------------------------------------------------------------- *)

subsection\<open>1x1\<close>

(* General 1x1 Ufun constructor with one input and one output channel *)
definition uf_1x1 :: "('a \<rightarrow> 'a) \<Rightarrow> (channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_1x1 f cs \<equiv> Abs_cufun (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {(fst cs)}) 
                             \<leadsto> (Abs_ubundle [(snd cs) \<mapsto> f\<cdot>(sb . (fst cs))]))"

subsubsection\<open>Ufun requirements\<close>
(* Show that our definition of general Ufuns with one input and one output are in fact Ufuns *)

lemma map_io_well2_ubwell: assumes "map_io_well (usclOkay::(channel \<Rightarrow> 'a::uscl \<Rightarrow> bool)) f ch1 ch2" 
                               and "usclOkay ch1 x"
                             shows "ubWell [ch2 \<mapsto> f\<cdot>x]"
  apply (rule ubwellI)
  apply (simp add: domIff)
  using assms(1) assms(2) map_io_well_def by blast

lemma map_io_well2_ubwell2: assumes "map_io_well (usclOkay::(channel \<Rightarrow> 'a::uscl \<Rightarrow> bool)) f ch1 ch2" 
                                and "ch1 \<in> ubDom\<cdot>ub"
                              shows "ubWell [ch2 \<mapsto> f\<cdot>(ub . ch1)]"
  by (metis assms(1) assms(2) map_io_well2_ubwell ubdom_channel_usokay ubgetch_insert)

(* 1x1 construction is monotonic *)
lemma uf_1x1_mono[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "monofun (\<lambda>sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))"
  apply (fold ubclDom_ubundle_def)
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x \<noteq> {ch1}")
  apply (simp_all add: ubcldom_fix)
  apply (rule some_below)
  apply (rule ub_below)
  apply (simp add: ubdom_insert)
  apply (simp_all add: assms map_io_well2_ubwell2 ubclDom_ubundle_def)
  apply (simp add: assms map_io_well2_ubwell2 ubdom_below)
  by (simp add: assms fun_upd_same map_io_well2_ubwell2 monofun_cfun_arg ubdom_below ubgetch_ubrep_eq)

(* 1x1 construction preserves chain properties *)
lemma uf_1x1_chain1[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i . ch1)])"
  apply(rule chainI)
  apply(rule ub_below)
  apply (simp add: assms map_io_well2_ubwell2 ubdom_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: assms map_io_well2_ubwell2 ubdom_ubrep_eq)
  by (simp add: assms map_io_well2_ubwell2 monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)

lemma uf_1x1_chain_lub[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [ch2 \<mapsto> f\<cdot>((Y i) . ch1)])"
  by (simp add: assms)
    
lemma uf_1x1_chain2: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> chain(\<lambda> i. (ubDom\<cdot>(Y i) = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>((Y i) . ch1)]))"
  apply(rule chainI, simp)
  apply(rule impI, rule some_below, rule ub_below)
  apply (simp add: assms map_io_well2_ubwell2 ubdom_ubrep_eq)
  by (simp add: assms map_io_well2_ubwell2 monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)
    
(* LUB and 1x1 construction are commutative *)
lemma uf_1x1_lub[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow>  (\<Squnion>i. f\<cdot>(Y i . c1)) = f\<cdot>((Lub Y) . c1)"
  by (metis ch2ch_Rep_cfunR contlub_cfun_arg)


(* Monotonic & Chain/LUB properties \<Longrightarrow> resulting function from 1x1 construction is continous *)
lemma uf_1x1_cont[simp] : 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "cont (\<lambda>sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))"
proof- 
  have f1: " \<And>(x::'a\<^sup>\<Omega>) y::'a\<^sup>\<Omega>. ubclDom\<cdot>x = {ch1} \<Longrightarrow> x \<sqsubseteq> y 
      \<Longrightarrow> Abs_ubundle [ch2 \<mapsto> f\<cdot>(x  .  ch1)] \<sqsubseteq> Abs_ubundle [ch2 \<mapsto> f\<cdot>(y  .  ch1)]"
    apply (simp_all add: ubclDom_ubundle_def)
    apply (rule ub_below)
    apply (simp add: assms map_io_well2_ubwell2 ubdom_below ubdom_ubrep_eq) +
    apply (simp add: ubgetch_ubrep_eq assms map_io_well2_ubwell2 ubdom_below)
    by (simp add: monofun_cfun_arg)
  have f2: "\<And>Y::nat \<Rightarrow> 'a\<^sup>\<Omega>.
       chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow> chain (\<lambda>i::nat. Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)])"
    by (simp add: assms ubclDom_ubundle_def)    
  have f3: "\<And> Y. chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       ubDom\<cdot>(Abs_ubundle [ch2 \<mapsto> f\<cdot>((\<Squnion>i::nat. Y i)  .  ch1)]) = {ch2}"
    by (simp add: assms map_io_well2_ubwell2 ubclDom_ubundle_def ubdom_ubrep_eq)
  have f31: "\<And> Y. chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       (\<Squnion>i::nat. ubDom\<cdot>(Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)])) = {ch2}"
    apply (simp add: ubdom_insert)
    by (simp add: assms map_io_well2_ubwell2 ubclDom_ubundle_def)
  have f5: "\<And>(Y::nat \<Rightarrow> 'a\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       Abs_ubundle [ch2 \<mapsto> f\<cdot>((\<Squnion>i::nat. Y i)  .  ch1)]  .  ch2 = f\<cdot>((\<Squnion>i::nat. Y i)  .  ch1)"
    by (simp add: assms map_io_well2_ubwell2 ubgetch_ubrep_eq)
  have f6: "\<And>(Y::nat \<Rightarrow> 'a\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {ch1} \<Longrightarrow>
       (\<Squnion>i::nat. Abs_ubundle [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)])  .  ch2 = (\<Squnion>i::nat. f\<cdot>(Y i  .  ch1))"
    apply (subst ubgetch_lub, simp add: f2)
    apply (metis (mono_tags) contlub_cfun_arg f2 f31 insertI1 ubclDom_ubundle_def)
    by (simp add: assms map_io_well2_ubwell2 ubgetch_ubrep_eq)
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
    apply (metis assms ch2ch_Rep_cfunR contlub_cfun_arg insertI1 map_io_well2_ubwell2 ubclDom_ubundle_def)
    apply (simp add: assms map_io_well2_ubwell2 ubclDom_ubundle_def)
    apply (simp add: f3 ubclDom_ubundle_def)
    apply (simp add: f5 f6)
    by (metis below_refl ch2ch_Rep_cfunR contlub_cfun_arg)
qed

(* As the general 1x1 Ufun is continous and has fixed input and output channels it is a ufun *)
lemma uf_1x1_well[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "ufWell (Abs_cfun (\<lambda>sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)])))"  
  apply (rule ufun_wellI)
  apply (simp_all add: domIff2 assms)
  apply (simp_all add: ubclDom_ubundle_def)
  apply (simp add: ubdom_insert)
  by (simp add: assms map_io_well2_ubwell2 ubdom_insert)

subsubsection\<open>Properties\<close>
(* Show some properties, like dom and range *)

(* The domain is ch1 *))
lemma uf_1x1_dom[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "ufDom\<cdot>(Abs_cufun(\<lambda> sb. (ubDom\<cdot>sb = {ch1}) \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))) = {ch1}"
  apply(simp add: ufdom_insert)
  apply(simp add: assms domIff2)
  apply (fold ubclDom_ubundle_def)
  apply (rule someI_ex)
  by (simp add: ubundle_ex)
    
(* The range is ch2 *)
lemma uf_1x1_ran[simp]:
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "ufRan\<cdot>(Abs_cufun(\<lambda> sb::('a::uscl_pcpo)\<^sup>\<Omega>. (ubDom\<cdot>sb = {ch1}) 
                                                   \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(sb . ch1)]))) = {ch2}"
  apply (simp add: ufran_least)
  apply (subst rep_abs_cufun)
  apply (simp add: assms) +
  apply (fold ubclDom_ubundle_def)
  apply (simp add: ubcldom_least_cs)
  apply (simp add: ubclDom_ubundle_def)
  by (metis assms dom_eq_singleton_conv map_io_well2_ubwell2 singletonI 
      ubclDom_ubundle_def ubcldom_least_cs ubdom_ubrep_eq)

subsection\<open>2x2\<close>

(* general 2x2 Ufun constructor with Ics as input and Ocs as output channel *)
definition Ufun2x2 :: "('a \<rightarrow> 'a \<rightarrow> 'a) \<Rightarrow> ('a \<rightarrow> 'a \<rightarrow> 'a) 
                      \<Rightarrow>  (channel \<times> channel)  \<Rightarrow>  (channel  \<times> channel)  \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"Ufun2x2 f1 f2 Ics Ocs \<equiv> Abs_cufun (\<lambda> (sb::('a\<^sup>\<Omega>)). (ubDom\<cdot>sb = {(fst Ics), (snd Ics)}) 
                          \<leadsto> (Abs_ubundle [(fst Ocs)\<mapsto>f1\<cdot>(sb . (fst Ics))\<cdot>(sb . (snd Ics)),
                               (snd Ocs)\<mapsto>f2\<cdot>(sb . (fst Ics))\<cdot>(sb . (snd Ics))]))"

(* ----------------------------------------------------------------------- *)
section \<open>Templates\<close>
(* ----------------------------------------------------------------------- *)

subsection\<open>Identity\<close>

(* Identity function *)  
definition id :: "'a \<rightarrow> 'a" where
"id \<equiv> \<Lambda> x . x"

(* Universal identity function *)
definition uf_id :: "(channel \<times> channel) \<Rightarrow> ('a\<^sup>\<Omega>) ufun" where
"uf_id cs \<equiv> uf_1x1 id cs"

end

(*
lift_definition Ufun1x1_2 :: "('a \<rightarrow> 'a) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('a\<^sup>\<Omega>) ufun" is
"\<lambda> (f::('a \<rightarrow> 'a)) ch1 ch2. (\<Lambda> (ub::('a\<^sup>\<Omega>)). (ubDom\<cdot>ub = {ch1}) 
                             \<leadsto> (Abs_ubundle [ch2 \<mapsto> f\<cdot>(ub . ch1)]))"
by simp
      
 
subsection \<open>Ufun1x1 constructor lemmata\<close>
(* As we now know that the general Ufun1x1 is in fact an Ufun we can proof properties for the general
   Ufun1x1 constructor *)
  
lemma second_channel: "snd (a, b) = b"
  by simp
  
lemma Ufun1x1_dom[simp]: "ufunDom\<cdot>(Ufun1x1 f (ch1, ch2)) = {ch1}"
proof -
  have "ufunDom\<cdot> (Abs_CUfun (\<lambda>s. (sbDom\<cdot>s = {fst (ch1, ch2)})
                                            \<leadsto>[snd (ch1, ch2) \<mapsto> f\<cdot>(s . fst (ch1, ch2))]\<Omega>)) = {ch1}"
    by (metis (no_types) prod.sel(1) uf_1x1_dom)
  then show ?thesis
    using Ufun1x1_def by presburger
qed
  
lemma Ufun1x1_ran[simp]: "ufunRan\<cdot>(Ufun1x1 f (ch1, ch2)) = {ch2}"
  apply(simp add: Ufun1x1_def)
  by (metis fst_conv uf_1x1_ran second_channel)
    
lemma Ufun1x1_rep_eq: "Rep_CUfun (Ufun1x1 f (ch1, ch2)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1,ch2))}) 
                                        \<leadsto> ([(snd (ch1,ch2)) \<mapsto> f\<cdot>(sb . (fst (ch1,ch2)))]\<Omega>))"
  apply(simp add: Ufun1x1_def)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  apply(subst Product_Type.snd_conv, subst Product_Type.fst_conv)
  by simp
    
lemma Ufun1x1_apply: "(Ufun1x1 f (ch1, ch2)) \<rightleftharpoons> ([ch1 \<mapsto> s]\<Omega>) = ([ch2 \<mapsto> f\<cdot>(s:: nat stream)]\<Omega>)"
  apply(simp add:  Ufun1x1_rep_eq  sb_id_def  sbgetch_insert)
  by(simp add: sbdom_rep_eq)
    


(* ----------------------------------------------------------------------- *)
section \<open>2x1 Ufun\<close>
(* ----------------------------------------------------------------------- *)

  subsection \<open>Ufun2x1 prerequirements\<close>
(* anlogue to before we first show some prerequirements *)
  
lemma ufun_2x1_general_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
 ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule ufun_mono2monofun)
   apply (rule ufun_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  by (rule, simp add: domIff2)
    
lemma ufun_2x1_general_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1,ch2} 
                        \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)
                                    \<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma ufun_2x1_general_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} 
                                \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)
  \<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma ufun_2x1_general_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} \<Longrightarrow> 
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

lemma ufun_2x1_general_cont[simp]: "cont 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
  ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule ufun_cont2cont)
    apply (rule ufun_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg  ufun_2x1_general_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2ufun_mono)
  by(simp add: domIff2, rule+)
    
lemma  ufun_2x1_general_well[simp] : "ufun_well (\<Lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
  ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply(simp add: ufun_well_def)
  apply(simp add: domIff2)
  by(auto simp add: sbdom_rep_eq)

(* Now explicitly show the domain properties of the general 2x1 Ufun *)
lemma ufun_2x1_general_dom[simp]: "ufunDom\<cdot>(Abs_CUfun(\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
    \<leadsto> ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))) = {ch1, ch2}"
  apply(simp add: ufundom_insert)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)
    
lemma ufun_2x1_general_ran[simp]: "ufunRan\<cdot>(Abs_CUfun(\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
    \<leadsto> ([ch3 \<mapsto> (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))) = {ch3}"
  apply(simp add: ufunran_least)
  by(simp add: ufunran_least sbdom_insert)
    
    
subsection \<open>2x1 Ufun lift_definitions\<close>
lift_definition Ufun2x1_2 :: "(nat stream \<rightarrow> nat stream \<rightarrow> nat stream) \<Rightarrow> (channel \<times> channel) \<Rightarrow> channel \<Rightarrow> nat Ufun" is
"\<lambda> f cs ch3. (\<Lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (snd cs)}) 
                          \<leadsto> ([ch3\<mapsto>f\<cdot>(sb . (fst cs))\<cdot>(sb . (snd cs))]\<Omega>))"
by simp
    
    
subsection \<open>Ufun2x1 constructor lemmata\<close>
(* As we now know that the general Ufun2x1 is in fact an Ufun we can proof properties for the general
   Ufun2x1 constructor *)
    
lemma Ufun2x1_dom[simp]: "ufunDom\<cdot>(Ufun2x1 f (ch1, ch2, ch3)) = {ch1, ch2}"
  apply(simp add: Ufun2x1_def)
  apply(subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv, subst snd_conv)
  by simp  
    
lemma Ufun2x1_ran[simp]: "ufunRan\<cdot>(Ufun2x1 f (ch1, ch2, ch3)) = {ch3}"
  apply(subst ufunran_least)
    (* the next step is very ugly, but effectively removes fst, snds *)
  apply(simp add: Ufun2x1_def, subst snd_conv, subst fst_conv, 
      subst snd_conv, subst fst_conv, subst snd_conv)
  by (simp)
    
lemma  Ufun2x1_rep_eq: "Rep_CUfun (Ufun2x1 f (ch1, ch2, ch3)) 
    =  (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1, ch2, ch3)), (fst (snd (ch1, ch2, ch3)))}) 
          \<leadsto> ([(snd (snd (ch1, ch2, ch3)))\<mapsto>f\<cdot>(sb . (fst (ch1, ch2, ch3)))
                \<cdot>(sb . (fst (snd (ch1, ch2, ch3))))]\<Omega>))"
  apply(simp add: Ufun2x1_def)
  apply(subst snd_conv, subst fst_conv)
  apply(subst snd_conv, subst fst_conv)
  apply(subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv, subst snd_conv, 
        subst snd_conv)
  by simp
      
lemma Ufun2x1_apply: assumes "ch1 \<noteq> ch2"
  shows "(Ufun2x1 f (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) 
    = ([ch3 \<mapsto> (f\<cdot>s1\<cdot>s2)]\<Omega>)"
  apply(simp add: Ufun2x1_rep_eq sb_id_def sbgetch_insert)
  by(auto simp add: sbdom_rep_eq assms)
    
    

(* ----------------------------------------------------------------------- *)
section \<open>2x2 Ufun\<close>
(* ----------------------------------------------------------------------- *)

  subsection \<open>Ufun2x2 prerequirements\<close>
(* anlogue to before we first show some prerequirements *)
  
lemma ufun_2x2_general_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
 ([ch3 \<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2), 
   ch4 \<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2) ]\<Omega>))"
  apply (rule ufun_mono2monofun)
   apply (rule ufun_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  by (rule, simp add: domIff2)
    
lemma ufun_2x2_general_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1,ch2} 
                        \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2),
                  ch4\<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma ufun_2x2_general_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} 
  \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2),
                  ch4\<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  by(auto simp add: sbChain_dom_eq2)

    
lemma ufun_2x2_general_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} \<Longrightarrow> 
  (\<Squnion>i. (f::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(Y i . ch1)\<cdot>(Y i . ch2)) 
  = f\<cdot>((Lub Y) . ch1)\<cdot>((Lub Y). ch2)"
  by simp


lemma ufun_2x2_general_cont[simp]: "cont 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
  ([ch3 \<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2),
    ch4 \<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule ufun_cont2cont)
    apply (rule ufun_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg  ufun_2x2_general_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2ufun_mono)
  by(simp add: domIff2, rule+)
    
lemma  ufun_2x2_general_well[simp] : "ufun_well (\<Lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> 
  ([ch3 \<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2),
    ch4 \<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply(simp add: ufun_well_def)
  apply(simp add: domIff2)
  by(auto simp add: sbdom_rep_eq)

(* Now explicitly show the domain properties of the general 2x2 Ufun *)
lemma ufun_2x2_general_dom[simp]: "ufunDom\<cdot>(Abs_CUfun(\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
    \<leadsto> ([ch3 \<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2),
         ch4 \<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))) 
      = {ch1, ch2}"
  apply(simp add: ufundom_insert)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)
    
lemma ufun_2x2_general_ran[simp]: "ufunRan\<cdot>(Abs_CUfun(\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
    \<leadsto> ([ch3 \<mapsto> (f1::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2),
         ch4 \<mapsto> (f2::nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))) = {ch3,ch4}"
  apply(simp add: ufunran_least)
  by(auto simp add: ufunran_least sbdom_insert)
    

subsection \<open>Ufun2x2 constructor lemmata\<close>
  
lemma Ufun2x2_dom[simp]: "ufunDom\<cdot>(Ufun2x2 f1 f2 (ch1, ch2) (ch3,ch4)) = {ch1, ch2}"
  apply(simp add: Ufun2x2_def)
  apply(subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv, subst snd_conv,
        subst fst_conv)
  by simp 
    
    
lemma Ufun2x2_ran[simp]: "ufunRan\<cdot>(Ufun2x2 f1 f2 (ch1, ch2) (ch3,ch4)) = {ch3,ch4}"
  apply(subst ufunran_least)
    (* the next step is very ugly, but effectively removes fst, snds *)
  apply(simp add: Ufun2x2_def, subst snd_conv, subst fst_conv, 
      subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv)
  by simp
    
    
lemma  Ufun2x2_rep_eq: "Rep_CUfun (Ufun2x2 f1 f2 (ch1, ch2) (ch3,ch4)) 
    =  (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1, ch2)), (snd (ch1, ch2))}) 
          \<leadsto> ([(fst (ch3,ch4))\<mapsto>f1\<cdot>(sb . (fst (ch1,ch2)))\<cdot>(sb . (snd  (ch1,ch2))),
               (snd (ch3,ch4))\<mapsto>f2\<cdot>(sb . (fst  (ch1,ch2)))\<cdot>(sb . (snd  (ch1,ch2)))]\<Omega>))"
  apply(simp add: Ufun2x2_def)
  apply(subst snd_conv, subst fst_conv)
  apply(subst snd_conv, subst fst_conv)
  apply(subst snd_conv, subst fst_conv, subst snd_conv, subst fst_conv, subst snd_conv, 
        subst snd_conv, subst fst_conv, subst fst_conv)
  by simp
    
lemma Ufun2x2_apply: assumes "ch1 \<noteq> ch2"
  shows "(Ufun2x2 f1 f2 (ch1, ch2) (ch3,ch4)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) 
    = ([ch3 \<mapsto> (f1\<cdot>s1\<cdot>s2), ch4 \<mapsto> (f2\<cdot>s1\<cdot>s2)]\<Omega>)"
  apply(simp add: Ufun2x2_rep_eq sb_id_def sbgetch_insert)
  by(auto simp add: sbdom_rep_eq assms)
    
    
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

lemma appendUfun_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"
  apply(simp only: appendElem_def)
  apply (rule ufun_mono2monofun)
   apply (rule ufun_monoI)
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

lemma appendUfun_chain_lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs)} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd cs)\<mapsto>(appendElem a ((Y i).(fst cs)))]\<Omega>)"
  by (simp add: append_chain sbChain_dom_eq2)  

lemma appendUfun_Lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs)} 
                        \<Longrightarrow> (\<Squnion>i.(appendElem a ((Y i).(fst cs)))) = appendElem a ((Lub Y).(fst cs))"
  apply(simp only: appendElem_def)    
  by (simp add: lub_distribs(1) lub_eval)

lemma appendUfun_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"
    apply (rule ufun_cont2cont)
    apply (rule ufun_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg appendUfun_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub appendUfun_chain_lub appendUfun_Lub)
   apply (simp add: appendUfun_mono monofun2ufun_mono)
proof -
   show "\<forall>b. (b \<in> dom (\<lambda>sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))) 
                = (sbDom\<cdot>b = {fst cs})" 
     by (simp add: domIff)
qed

(* ----------------------------------------------------------------------- *)
section \<open>legacy\<close>
(* ----------------------------------------------------------------------- *)
  (* In the following you find obsolete lemmas, kept only for compatibility purposes *)
  
subsubsection \<open>idUfun lemmata\<close>
  (* the following lemmata are only there for legacy/didactic purposes *)
  (* the functionality is now moved to the general Ufun1x1 lemmata *)
  
lemma ufun_sb_id_cont[simp] : "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>))"
  by simp

lemma ufun_sb_id_well[simp] : "ufun_well (Abs_cfun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) 
                                                  \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>)))"  
  by simp  
  
lemma ufun1x1_sb_id_eq: "Ufun1x1 sb_id cs = idUfun cs"
  by(simp add: Ufun1x1_def idUfun_def)

lemma idUfun_rep_eq_C: "Rep_CUfun (idUfun (ch1, ch2)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1,ch2))}) 
                                        \<leadsto> ([(snd (ch1,ch2)) \<mapsto> sb_id\<cdot>(sb . (fst (ch1,ch2)))]\<Omega>))"
proof -
  have f1: "\<forall>cs. idUfun cs = Ufun1x1 sb_id cs"
    by(simp add:  ufun1x1_sb_id_eq)
  thus ?thesis
    by(subst f1, simp add:  Ufun1x1_rep_eq)
qed
      
lemma idUfun_dom[simp]: "ufunDom\<cdot>(idUfun (ch1, ch2)) = {ch1}"
  by (metis Ufun1x1_dom ufun1x1_sb_id_eq)
    
lemma idUfun_ran[simp]: "ufunRan\<cdot>(idUfun (ch1, ch2)) = {ch2}"
  by (metis Ufun1x1_ran ufun1x1_sb_id_eq)
    
lemma idUfun_apply: "(idUfun (ch1, ch2)) \<rightleftharpoons> ([ch1 \<mapsto> s]\<Omega>) = ([ch2 \<mapsto> (s:: nat stream)]\<Omega>)"
proof -
  have f1: "\<forall>cs. idUfun cs = Ufun1x1 sb_id cs"
    by(simp add:  ufun1x1_sb_id_eq)
  thus ?thesis
    by(subst f1, simp add:  Ufun1x1_apply sb_id_def)
qed
  
(* testing general lemmas 
lemma monotest: assumes "\<And>b1 b2. sbDom\<cdot>b1 = cs \<Longrightarrow> sbDom\<cdot>b2 = cs \<Longrightarrow> b1 \<sqsubseteq> b2 \<Longrightarrow> sbDom\<cdot>(f(b1)) = sbDom\<cdot>(f(b2))"
                    and "\<And>b1 b2 c. sbDom\<cdot>b1 = cs \<Longrightarrow> sbDom\<cdot>b2 = cs \<Longrightarrow> b1 \<sqsubseteq> b2 \<Longrightarrow> c \<in> sbDom\<cdot>(f(b1)) \<Longrightarrow> f(b1) . c \<sqsubseteq> f(b2) . c"
                    and " \<forall>b. (b \<in> dom (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))) = (sbDom\<cdot>b = In)"
                  shows "monofun (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))"
  sorry
    
   apply (rule ufun_mono2monofun)
   apply (rule ufun_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below) 
    
lemma conttest: assumes "monofun (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))"
                    and "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = cs 
                        \<Longrightarrow> chain (\<lambda> i. f(Y i))"
                    and "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = cs 
                        \<Longrightarrow> chain (\<lambda> i. f(Y i))"
                  shows "cont (\<lambda> sb. (sbDom\<cdot>sb = cs) \<leadsto> f(sb))"
  sorry siehe Ufun_CaseStudy contUfun *)
    
    


(*lift_definition addUfun2 :: "nat Ufun" is
"(\<lambda> cs. (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))) (ch1,ch2,ch3)"
sorry*)
  
lemma appendUfun_Ufun1x1_eq: "Ufun1x1 (appendElem2 a) (ch1,ch2) = appendUfun (ch1,ch2) a"
  oops (* @Marc: can you resolve this *)
    
lemma addUfun_Ufun2x1_eq: "addUfun (ch1,ch2,ch3) = Ufun2x1 add (ch1,ch2,ch3)"
  by(simp add: Ufun2x1_def addUfun_def)
    
lemma multUfun_Ufun2x1_eq: "multUfun (ch1,ch2,ch3) = Ufun2x1 mult (ch1,ch2,ch3)"
  by(simp add: Ufun2x1_def multUfun_def)
    
(* ----------------------------------------------------------------------- *)
subsection \<open>add_componentwise\<close>
(* ----------------------------------------------------------------------- *) 
  

lemma addUfun_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  by simp

     
lemma add_chain: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {(fst cs), (fst (snd cs))} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>)"
  by simp


lemma addUfun_chain_lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (fst (snd cs))} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>)"
  by simp

lemma addUfun_Lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (fst (snd cs))} \<Longrightarrow> 
  (\<Squnion>i. add\<cdot>(Y i . (fst cs))\<cdot>(Y i . (fst (snd cs)))) = add\<cdot>((Lub Y) . (fst cs))\<cdot>((Lub Y). (fst (snd cs)))"
   by simp


lemma addUfun_chain: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>((Y i) . (fst cs))\<cdot>((Y i) . (fst (snd cs)))]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)


lemma addUfun_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  by simp

lemma addUfun_well: "ufun_well (\<Lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> 
  ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
  by simp

lemma addUfun_rep_eqC: "Rep_CUfun (addUfun cs) = 
  (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs), (fst (snd cs))}) \<leadsto> ([(snd (snd cs))\<mapsto>add\<cdot>(sb . (fst cs))\<cdot>(sb . (fst (snd cs)))]\<Omega>))"
by(simp add: addUfun_def add2_def)


    
(* ----------------------------------------------------------------------- *)
subsection \<open>mult_componentwise\<close>
(* ----------------------------------------------------------------------- *) 
  

(* TODO: remove [simp] *)

lemma ufunmult_cont[simp]: "cont 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  by simp

    

lemma ufunmult_well[simp] : "ufun_well (\<Lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  by simp

     
    
subsection \<open>multUfun lemmata\<close>
(* LEMMAS below work if ufunmult_well is proven *)
  
  
lemma multUfun_rep_eq_C: "Rep_CUfun (multUfun (ch1, ch2, ch3)) 
                                = (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {(fst (ch1, ch2, ch3)), (fst (snd (ch1, ch2, ch3)))}) \<leadsto> ([(snd (snd (ch1, ch2, ch3)))\<mapsto>mult\<cdot>(sb . (fst (ch1, ch2, ch3)))\<cdot>(sb . (fst (snd (ch1, ch2, ch3))))]\<Omega>))"
  by (simp add: Ufun2x1_rep_eq multUfun_Ufun2x1_eq)
      
lemma multUfun_dom[simp]: "ufunDom\<cdot>(multUfun (ch1, ch2, ch3)) = {ch1, ch2}"
    by (simp add: multUfun_Ufun2x1_eq)
    
lemma multUfun_ran[simp]: "ufunRan\<cdot>(multUfun (ch1, ch2, ch3)) = {ch3}"
  by (simp add: multUfun_Ufun2x1_eq)
 
lemma multUfun_apply: assumes "ch1 \<noteq> ch2"
shows "(multUfun (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) = ([ch3 \<mapsto> (mult\<cdot>s1\<cdot>s2)]\<Omega>)"
  by (simp add: multUfun_Ufun2x1_eq  Ufun2x1_apply assms)

end
 
(*
BACKUP Section

lemma ufun_sb_id_mono[simp] : "monofun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>(sb . ch1)]\<Omega>))"
  apply (rule ufun_mono2monofun)
  apply(rule ufun_monoI)
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

lemma ufun_sb_id_chain[simp]: "chain Y \<Longrightarrow> chain(\<lambda> i. (sbDom\<cdot>(Y i) = {ch1}) \<leadsto> ([ch2 \<mapsto> sb_id\<cdot>((Y i) . ch1)]\<Omega>))"
  apply(rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply(rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma ufun_sb_id_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> (\<Squnion>i. sb_id\<cdot>(Y i . c1)) = sb_id\<cdot>((Lub Y) . c1)"
  by (simp add: contlub_cfun_arg contlub_cfun_fun)


MULTIPLICATION

(* multiplication component *)
lemma ufunmult_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> mult\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule ufun_mono2monofun)
   apply (rule ufun_monoI)
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
*)