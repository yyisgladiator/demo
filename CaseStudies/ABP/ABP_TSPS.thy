(*  Title:        ABP_TSPS.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  ABP modeled with TSPS
*)

theory ABP_TSPS
  imports "../../timed/TSPS" Sender Receiver Composition Medium "../../timed/TSPF" "../../UFun_Comp" "../../USpec_Comp"

begin

default_sort countable


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)


datatype 'a::countable MABP = BoolPair "('a * bool)" | Bool bool | Data 'a
print_theorems

instantiation MABP ::  (countable) countable
begin
instance
   by (countable_datatype)
end

instantiation MABP ::  (countable) message
begin
fun ctype_MABP :: "channel \<Rightarrow> 'a MABP set" where
  "ctype_MABP c_abpIn = range Data" |
  "ctype_MABP c_abpOut = range Data" |
  "ctype_MABP c_ds = range BoolPair" |
  "ctype_MABP c_dr = range BoolPair" |
  "ctype_MABP c_as = range Bool" |
  "ctype_MABP c_ar = range Bool" |
  "ctype_MABP c_idOut = range Data" |
  "ctype_MABP other = undefined"

  instance ..
end


declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


(* ----------------------------------------------------------------------- *)
section \<open>Helper Definitions\<close>
(* ----------------------------------------------------------------------- *)


subsection \<open>datatype destructors\<close>

abbreviation invBoolPair :: "'a MABP \<Rightarrow> ('a \<times> bool)" where
"invBoolPair \<equiv> (inv BoolPair)"

abbreviation invBool :: "'a MABP \<Rightarrow> bool" where
"invBool \<equiv> (inv Bool)"

abbreviation invData :: "'a MABP \<Rightarrow> 'a" where
"invData \<equiv> (inv Data)"       


(* ----------------------------------------------------------------------- *)
section \<open>Component Helper Definitions\<close>
(* ----------------------------------------------------------------------- *)


subsection \<open>receiver\<close>


abbreviation recvAbb where
"recvAbb \<equiv>
let recRes = (\<lambda> x. tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))
in (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle([c_ar    \<mapsto> tsMap Bool\<cdot>(fst (recRes x)),
                                        c_abpOut \<mapsto> tsMap Data\<cdot>(snd (recRes x))]))"

definition recvTSPF :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"recvTSPF \<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle([c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"


subsection \<open>medium\<close>


definition med_TSPF :: "bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun" where
"med_TSPF bst In Out f \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(x . In))\<cdot>bst)]))"

abbreviation tsMedAbb  :: "bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option" where
"tsMedAbb bst In Out f x \<equiv> ((ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(x . In))\<cdot>bst)]))"


subsection \<open>medium_sr\<close>
  (* medium from sender to receiver *)
  (* input: c_ds, output: c_dr, transport (data, bool) tuples *)
abbreviation medSR_TSPF :: "bool stream \<Rightarrow>('a MABP tstream\<^sup>\<Omega>)ufun" where
"medSR_TSPF bst\<equiv> med_TSPF bst c_ds c_dr BoolPair"


subsection \<open>medium_rs\<close>
  (* medium from receiver to sender *)
  (* input: c_ar, output: c_as, transport booleans *)
abbreviation medRS_TSPF :: "bool stream \<Rightarrow>('a MABP tstream\<^sup>\<Omega>)ufun" where
"medRS_TSPF bst\<equiv> med_TSPF bst c_ar c_as Bool"


subsection \<open>sender\<close>


  (* lift a sender function to a TSPF *)
definition senderTSPF :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"senderTSPF se \<equiv> Abs_cufun (\<lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"


subsection \<open>id\<close>


definition idTSPF :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"idTSPF \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> x)"

definition idTSPF2 :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"idTSPF2 \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> x . c_abpOut])"


(* ----------------------------------------------------------------------- *)
section \<open>lemmata\<close>
(* ----------------------------------------------------------------------- *)


subsection \<open>general\<close>


lemma tsmap_id[simp]: assumes "inj f" shows "tsMap (inv f)\<cdot>(tsMap f\<cdot>ts) = ts"
apply(induction ts)
by(simp_all add: assms tsmap_delayfun  tsmap_mlscons)

lemma med_ora_length: assumes "#({True} \<ominus> ora) = \<infinity>"
  shows "#ora = \<infinity>"
  using assms sfilterl4 by auto  


subsection \<open>datatype\<close>


  (* inverse BoolPair applied to BoolPair is identity *)
lemma data_bool_pair_inv [simp]: "(invBoolPair) (BoolPair x) = x"
  by (meson MABP.inject(1) f_inv_into_f rangeI)

  (* inverse Bool applied to Bool is identity *)
lemma data_bool_inv [simp]: "(inv Bool) (Bool x) = x"
  by (meson MABP.inject(2) f_inv_into_f rangeI)

  (* inverse Data applied to Data is identity *)
lemma data_data_inv [simp]: "(inv Data) (Data x) = x"
  by (meson MABP.inject(3) f_inv_into_f rangeI)


subsection \<open>receiver\<close>


subsubsection \<open>defs\<close>


(* helper functions to prove cont *)
definition recvCH1 :: "'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"recvCH1 \<equiv> (\<lambda> x. tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr)))))"

definition recvCH2 :: "'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"recvCH2 \<equiv> (\<lambda> x. tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr)))))"


subsubsection \<open>mono/cont\<close>


lemma recvCH1_contlub: assumes "chain Y"
  shows "recvCH1 ((\<Squnion>i. Y i)) = (\<Squnion>i. (recvCH1 ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms recvCH1_def)

lemma recvCH2_contlub: assumes "chain Y"
  shows "recvCH2 ((\<Squnion>i. Y i)) = (\<Squnion>i. (recvCH2 ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms recvCH2_def)

lemma to_recvch1: "tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr))))
                    = (recvCH1::'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) x"
  by (simp add: recvCH1_def)

lemma to_recvch2: "tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .c_dr))))
                    = (recvCH2::'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) x"
  by (simp add: recvCH2_def)

lemma recv_tsb_well [simp]:
  shows "ubWell [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                  c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]"
  apply (rule ubwellI)
  apply (simp add: tsmap_tsdom_range)
  by (metis ctype_MABP.simps(2) ctype_MABP.simps(6) tsmap_tsdom_range usclOkay_tstream_def)

lemma recv_tsb_dom: "ubclDom\<cdot>(Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                              c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))
                     = {c_ar, c_abpOut}"
  by (simp add: insert_commute ubclDom_ubundle_def ubdom_ubrep_eq)

lemma rec_tsb_mono: "\<And>(x::'a MABP tstream ubundle) y::'a MABP tstream ubundle. ubclDom\<cdot>x = {c_dr} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow>
          Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr)))),
          c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_dr))))])
          \<sqsubseteq> Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  c_dr)))),
             c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  c_dr))))])"
      apply (rule ub_below)
       apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
       by (simp add: fst_monofun snd_monofun monofun_cfun_arg ubgetch_below)     

lemma recvTSPF_mono [simp]: "monofun (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto>
                                    Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                     c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x = {c_dr}")
   apply (simp add: ubdom_below rec_tsb_mono some_below ubcldom_fix)
  by (simp add: ubdom_below ubcldom_fix)

lemma recvTSPF_tsb_getc: assumes "chain Y" and "ubclDom\<cdot>(\<Squnion>i. Y i) = {c_dr}"
  and "c \<in>  {c_ar, c_abpOut}"
  shows " (\<Squnion>i.
           Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])) . c
          = (\<Squnion> i. (Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])) . c)"
proof (rule lubgetCh)
   have f2: "\<And> i. ubclDom\<cdot>(Y i) =  ubclDom\<cdot>(\<Squnion>i. Y i)"
     by (simp add: assms(1) ubclDom_ubundle_def)
   show tb_chain: "chain (\<lambda>i::nat. Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))),
                             c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
     by (simp add: assms(1) assms(2) f2 po_class.chainE po_class.chainI rec_tsb_mono)

   show " c \<in> ubclDom\<cdot>(\<Squnion>i::nat.
                          Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))),
                       c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
     using assms(3) recv_tsb_dom tb_chain ubcldom_lub_eq2I by blast
qed

  (* show that recTSPF is cont, proof concept taken from TSPF_Template_CaseStudy *)
lemma recvTSPF_cont [simp]:
  shows "cont (\<lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto>
                      Abs_ubundle([c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                       c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"
proof (rule ufun_contI, simp add: rec_tsb_mono)
    fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
    assume Y_is_chain: "chain Y" and chain_Y_dom: "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_dr}"
    have f1: "\<And> i. (ubclDom\<cdot>(\<Squnion>i. Y i)) =  (ubclDom\<cdot>(Y i))"
      by (simp add: Y_is_chain ubclDom_ubundle_def)
    have f11: "\<And>i . (ubclDom\<cdot>(Y i)) = {c_dr}"
      using chain_Y_dom f1 by auto
    have "\<And> i. ubWell [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]"
      by simp
    have f12: "(ubclDom\<cdot>(\<Squnion>i::nat. Y i) =
        {c_dr})\<leadsto>Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))] = 
            Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))])"
      by (simp add: chain_Y_dom)
    have f13: "(\<Squnion>i::nat. (ubclDom\<cdot>(Y i) = {c_dr})\<leadsto>Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]) = 
            (\<Squnion>i::nat. Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      by (simp add: f11)
    have f14:"Some (\<Squnion>i::nat. (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))
          = (\<Squnion>i::nat. Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      apply (rule some_lub_chain_eq)
      apply (simp add: chain_def)
      by (simp add: Y_is_chain f11 po_class.chainE rec_tsb_mono)
    have f15: "ubclDom\<cdot>(Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))]) =
                ubclDom\<cdot>(\<Squnion>i::nat. (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      apply (simp add: ubclDom_ubundle_def)
      by (metis (mono_tags, lifting) Y_is_chain f11 po_class.chain_def rec_tsb_mono recv_tsb_dom ubclDom_ubundle_def ubdom_chain_eq2)
    have f17: "\<And> c::channel. (\<Squnion>i::nat. Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])  .  c =
          (\<Squnion>i::nat. Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))] . c)"
      apply (rule cont2contlubE)
      by (simp add: Y_is_chain f11 po_class.chainE po_class.chainI rec_tsb_mono) +
    have f20: "Some (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))]) \<sqsubseteq>
       Some (\<Squnion>i::nat. (Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))]))"
      apply (rule some_below)
      apply (rule ub_below)
       apply (metis (no_types, lifting) f15 ubclDom_ubundle_def)      
      apply (subst f17)
      apply (simp add: recvTSPF_tsb_getc ubdom_ubrep_eq ubgetch_ubrep_eq) 
      by (metis (mono_tags, lifting) Y_is_chain eq_imp_below lub_eq recvCH1_contlub recvCH2_contlub to_recvch1 to_recvch2)
    show "Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  c_dr))))] \<sqsubseteq>
       (\<Squnion>i::nat. Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  c_dr))))])"
      using f20 some_below2 by blast
qed


subsubsection \<open>uf_well/tickCount\<close>


declare [[simp_trace_new]]
 (* show that the recvTSPF fulfills the tickcount property *)
lemma recvTSPF_tick: assumes "ubDom\<cdot>b = {c_dr}" and "(ubLen b) = n"
  shows "n \<le> (ubLen (Abs_ubundle([c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))),
                       c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr))))])))"
proof -
  have "(ubLen b) = usclLen\<cdot>(b . c_dr)"
    using assms(1) uslen_ubLen_ch3 by auto
  hence f1: "n = #\<surd>(b . c_dr)"
    by (metis assms(2) usclLen_tstream_def)
  hence f2: "n \<le> #\<surd>(tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))))"
    by (simp add: tsrec_insert)
  with f1 have f3: "n \<le> #\<surd>(tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))))"
    by (simp add: tsrec_insert)
  have f4: "ubDom\<cdot>(Abs_ubundle [c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  c_dr))))])
    = {c_ar, c_abpOut}"
    by (metis recv_tsb_dom ubclDom_ubundle_def)
  show ?thesis 
    apply (rule ubLen_geI)
      apply (simp_all add: f4)
    apply (simp add: ubgetch_ubrep_eq)
    by (metis f2 f3 usclLen_tstream_def)
qed

  (* recvTSPF is an actual TSPF *)
lemma recvTSPF_well [simp]:
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = {c_dr}) \<leadsto>
                      Abs_ubundle([c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                       c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))]))"
  apply (rule ufun_wellI)
  by (simp_all add: domIff2 recv_tsb_dom)
                                     
lemma recv_revsubst: "Abs_cufun (recvAbb) = recvTSPF"
  by (simp add: recvTSPF_def)
    
lemma recv_tspfdom: "ufDom\<cdot>(recvTSPF) = {c_dr}"
  apply (simp add: ufDom_def recvTSPF_def)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)

lemma recv_tspfran: "ufRan\<cdot>(recvTSPF) = {c_ar, c_abpOut}"
  apply (simp add: ufran_least)
    apply (subst recv_tspfdom)
    apply (simp only: recvTSPF_def)
  by (simp add:  recv_tsb_dom ubcldom_least_cs) 


subsection \<open>sender\<close>


subsubsection \<open>defs\<close>


definition senderCH :: "'a sender \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"senderCH se \<equiv> (\<lambda> x. tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))))"


subsubsection \<open>mono/cont\<close>


lemma senderCH_contlub: assumes "chain Y"
  shows "senderCH se ((\<Squnion>i. Y i)) = (\<Squnion>i. (senderCH se ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: senderCH_def assms)

lemma to_senderch: "tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))
                    = senderCH se x"
  by (simp add: senderCH_def)

lemma sender_tsb_well [simp]: "ubWell [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]"
  apply (rule ubwellI)
  by (simp add: tsmap_tsdom_range usclOkay_tstream_def)

lemma sender_tsb_dom1: "ubclDom\<cdot>(Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))
                     = {c_ds}"
  by (simp add: ubclDom_ubundle_def ubdom_ubrep_eq)

lemma sender_tsb_mono: "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubclDom\<cdot>x = {c_as, c_abpIn} \<Longrightarrow>
       x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(x  .  c_as)))] \<sqsubseteq> Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(y  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(y  .  c_as)))]"
  apply (rule ub_below)
  apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
  by (simp add: monofun_cfun)

lemma sender_tspf_cont [simp]: "cont (\<lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((se::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"
proof (rule ufun_contI, simp add: sender_tsb_mono)
  fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
  assume a1: "chain Y" and a2: "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_as, c_abpIn}"
  have f1: "chain (\<lambda> i. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))])"
    apply (rule chainI)
    apply (rule ub_below)
     apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
    by (simp add: a1 monofun_cfun po_class.chainE)
  have f2: "(\<Squnion>i::nat. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))])  .  c_ds =
    (\<Squnion>i::nat. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))]  .  c_ds)"
    apply (rule cont2contlubE)
    by (simp add: f1) +
  have f4: "tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>((Lub Y)  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((Lub Y)  .  c_as))) =
    (senderCH se (Lub Y))"
    by (simp add: senderCH_def)
  have f5: "\<And> i. tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as))) = 
    (senderCH se (Y i))"
    by (simp add: senderCH_def)
  show "Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>((\<Squnion>i::nat. Y i)  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_as)))] \<sqsubseteq>
       (\<Squnion>i::nat. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Y i  .  c_as)))])"
    apply (rule ub_below)
     apply (simp_all add: ubclDom_ubundle_def ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
     apply (simp add: cont2contlubE f1 ubdom_ubrep_eq) 
    apply (subst f2)
    apply (simp_all add: ubgetch_ubrep_eq)
    apply (subst f4)
    apply (subst f5)
    by (simp add: a1 senderCH_contlub)
qed


subsubsection \<open>uf_well/tickCount\<close>


lemma ublen_min_eq_2_ch: assumes "ubDom\<cdot>b = {ch1, ch2}"
  shows "(ubLen b) = min (usclLen\<cdot>(b . ch1)) (usclLen\<cdot>(b . ch2))"
  apply (simp add: ubLen_def assms(1))
  apply (rule Least_equality)
   apply (metis min_def_raw)
  by auto

lemma senderTSPF_tick: assumes "ubDom\<cdot>b = {c_as, c_abpIn}" and "(ubLen b) = n" and "se \<in> tsSender"
  shows "n \<le> (ubLen (Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((se::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(b . c_abpIn))\<cdot>(tsMap invBool\<cdot>(b . c_as)))])))"  
proof -  
  have f00: "#\<surd> (b . c_abpIn) = #\<surd> (tsMap invData\<cdot>(b  .  c_abpIn))"
    by simp
  have f01: "#\<surd> (b . c_as) = #\<surd> (tsMap invBool\<cdot>(b  .  c_as))"
    by simp
  have f02: "n = ubLen b"
    by (simp add: assms(2))
  have f07: "n = min (usclLen\<cdot>(b . c_abpIn)) (usclLen\<cdot>(b . c_as))"
    by (simp add: assms(1) f02 min.commute ublen_min_eq_2_ch)
  have f08: "min (usclLen\<cdot>(b  .  c_abpIn)) (usclLen\<cdot>(b  .  c_as)) = 
          min (#\<surd> (tsMap invData\<cdot>(b  .  c_abpIn))) (#\<surd> (tsMap invData\<cdot>(b  .  c_as)))"
    by (simp add: usclLen_tstream_def)
  have f20: "min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)) = \<infinity> 
    \<Longrightarrow> #\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b  .  c_as)))) = \<infinity>"
  proof -
    assume a1: "min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)) = \<infinity>"
    obtain Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>" where Y_def: "Y \<equiv> (\<lambda> i. b \<down> i)"
      by simp
    have f200: "chain Y"
      apply (rule chainI, simp add: Y_def)
      apply (rule ub_below)
      by simp+
    have f201: "b = (\<Squnion> i. Y i)"
      by (simp add: Y_def)
    have f202: "\<And>i. Y i = b \<down> i"
      by (simp add: Y_def)
    have f203: "\<And> i. ubLen (Y i) = min (#\<surd> tsMap invData\<cdot>((Y i) .  c_abpIn)) (#\<surd> tsMap invData\<cdot>((Y i) .  c_as))"
      apply (simp add: Y_def ubLen_def assms(1))
      apply (rule Least_equality)
       apply (metis (no_types, lifting) a1 assms(1) f08 inf_ub insertI1 min.absorb2 min_def tsbttake2ttakeI tstake_len usclLen_tstream_def)
      by (metis (no_types, lifting) assms(1) insertI1 insert_commute min.commute min.orderI min.right_idem tsbttake2ttakeI tstake_len usclLen_tstream_def)
    obtain se_y::"'a MABP tstream\<^sup>\<Omega> \<Rightarrow> lnat" where se_y_def: "se_y \<equiv> (\<lambda> b. #\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b .  c_as)))))"
      by simp
    obtain min_y::"'a MABP tstream\<^sup>\<Omega> \<Rightarrow> lnat" where min_y_def: "min_y \<equiv> (\<lambda> b. min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)))"
      by simp
    have se_tsmap_data_below: "\<And> i. se\<cdot>(tsMap invData\<cdot>(Y i  .  c_abpIn)) \<sqsubseteq> se\<cdot>(tsMap invData\<cdot>(Y (Suc i)  .  c_abpIn))"
      apply (subst cont_pref_eq1I) +
      by (simp_all add: f200 po_class.chainE)
    have ts_map_bool_below: "\<And> i. (tsMap invBool\<cdot>(Y i  .  c_as)) \<sqsubseteq> (tsMap invBool\<cdot>(Y (Suc i)  .  c_as))"
      apply (subst cont_pref_eq1I) +
      by (simp_all add: f200 po_class.chainE)
    have chain_se_y: "chain (\<lambda> i. se_y (Y i))"
      apply (simp add: se_y_def)
      apply (rule chainI)
      apply (subst cont_pref_eq1I)
       apply (meson below_trans cfun_below_iff cont_pref_eq2I se_tsmap_data_below ts_map_bool_below)
      by simp
    have chain_min_y: "chain (\<lambda>i . min_y (Y i))"
      apply (simp add: min_y_def)
      apply (rule chainI)
      by (meson cont_pref_eq1I f200 lnle_def min.mono po_class.chainE)
    have f299: "#\<surd> se\<cdot>(tsMap invData\<cdot>(Lub Y  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(Lub Y  .  c_as)) = 
      #\<surd> se\<cdot>(tsMap invData\<cdot>((\<Squnion>i. Y i .  c_abpIn)))\<cdot>(tsMap invBool\<cdot>((\<Squnion>i. Y i  .  c_as)))"
      by (simp add: contlub_cfun_arg f200)
    have f300: "min_y (Lub Y) = ubLen b"
      using f02 f07 f08 f201 min_y_def by auto
    have f301: "\<And> j. min_y (Y j) \<sqsubseteq> se_y (Y j)"
      by (metis (no_types, lifting) Y_def a1 assms(1) assms(3) inf_less_eq insertI1 less_imp_le 
          lnle_conv min_def_raw min_y_def neqE notinfI3 se_y_def set2tssnd_strcausal tsbttake2ttakeI 
          tsmap_tstickcount tstake_len)
    have f302: "\<And> j. se_y (Y j) \<le> (\<Squnion> i. se_y (Y i))"
      using chain_se_y is_ub_thelub lnle_def by blast
    have f303: "(\<Squnion> i. min_y (Y i)) \<sqsubseteq> (\<Squnion> i. se_y (Y i))"
      using chain_min_y chain_se_y f301 lub_mono by blast
    have f304: "\<And>i. min_y (Y i) = Fin i"
      by (metis (no_types, lifting) Fin_neq_inf Y_def a1 assms(1) inf_less_eq insertI1 
          insert_commute min.cobounded1 min.cobounded2 min_def_raw min_y_def 
          tsbttake2ttakeI tsmap_tstickcount tstake_len)
    have f305: "(\<Squnion> i. min_y (Y i)) = \<infinity>"
      using chain_min_y f304 inf_belowI is_ub_thelub by fastforce
    have f50: " (\<Squnion> i. se_y (Y i)) = se_y (\<Squnion>i. Y i)"
      apply (simp add: se_y_def contlub_cfun_arg f200)
      apply (subst contlub_cfun_fun)
       apply (simp add: po_class.chainI se_tsmap_data_below)
      apply (subst contlub_cfun_arg)
      apply (simp add: po_class.chainI se_tsmap_data_below)
      apply (subst diag_lub)
       by (simp_all add: f200 po_class.chainE) +
     show "#\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b  .  c_as)))) = \<infinity>"
       apply (subst f201)
       using f201 f303 f305 f50 se_y_def by auto
  qed
  have f2: "n \<le> #\<surd> (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(b  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(b  .  c_as))))"
    apply (subst f07)
    apply (subst f08)
    apply (case_tac "min (#\<surd> tsMap invData\<cdot>(b  .  c_abpIn)) (#\<surd> tsMap invData\<cdot>(b  .  c_as)) < \<infinity>")
     apply (simp, metis assms(3) f00 f01 f08 less_imp_le set2tssnd_strcausal usclLen_tstream_def)
    using f20 by (simp add: less_le)
  show ?thesis
    apply (rule ubLen_geI)
    apply (simp_all add: ubclDom_ubundle_def ubdom_ubrep_eq ubgetch_ubrep_eq)
    by (metis f2 usclLen_tstream_def)
qed

lemma sendTSPF_well [simp]:
  shows "ufWell (\<Lambda> x. (ubclDom\<cdot>x = {c_as, c_abpIn})
                \<leadsto> Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((se::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as)))]))"
  apply (rule ufun_wellI)
  by (simp_all add: domIff2 sender_tsb_dom1)


lemma sender_tspfdom: "ufDom\<cdot>(senderTSPF se) = {c_as, c_abpIn}"
  apply (simp add: ufDom_def senderTSPF_def)
  apply (simp add: domIff)
  by (simp add: ubclDom_h)


lemma sender_tspfran: "ufRan\<cdot>(senderTSPF se) = {c_ds}"
  apply (simp add: ufran_least)
    apply (subst sender_tspfdom)
    apply (simp only: senderTSPF_def)
  by (simp add:  sender_tsb_dom1 ubcldom_least_cs) 


subsection \<open>medium\<close>

subsubsection \<open>defs\<close>

definition medH :: "bool stream \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"medH bst In f\<equiv> (\<lambda> x. tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(x  .  In))\<cdot>bst))"

lemma medh_cont [simp]: "cont (medH bst In f)"
  by (simp add: medH_def)

lemma medh_contlub: assumes "chain Y"
  shows "(medH bst In f) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medH bst In f) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medh: "tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(x  .  In))\<cdot>bst)
                  = ((medH :: bool stream \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) bst In f) x"
  by (simp add: medH_def)

subsubsection \<open>pre\<close>

lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast
(*
lemma medrs_tsb_well [simp]: "ubWell [as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]"
  apply (rule ubwellI)
  apply (simp add: usOkay_tstream_def)
  by (simp add: tsmap_tsdom_range) (*"tsDom\<cdot>(tsMap f\<cdot>ts) \<subseteq> range f"*)
  (*by (simp add: tsmap_tsdom_range usOkay_tstream_def)*)*)

lemma med_tsb_well [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"        (*bool \<rightarrow> f*)
  shows "ubWell [Out \<mapsto> (tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)]"
  apply (rule ubwellI)
  apply (simp add: usclOkay_tstream_def)
  by (simp add: assms tsmap_tsdom_range)


lemma med_tsb_dom: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ubDom\<cdot>(Abs_ubundle([Out \<mapsto> (tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)])) = {Out}"
  by  (simp add: assms ubdom_ubrep_eq)


subsubsection \<open>cont\<close>

  (* prerequirement for the mono proofs of the tspf *)
lemma med_tsb_mono: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubDom\<cdot>x = {In} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle([Out \<mapsto> (tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)]) \<sqsubseteq> Abs_ubundle([Out \<mapsto> (tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((y . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)])"
  apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
  apply (rule ub_below)
  apply (simp_all add: assms ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
  by (simp add: monofun_cfun_arg monofun_cfun_fun)

lemma med_mono [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "monofun (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> tsMap
                                f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst)]))"
  by (simp add: assms med_tsb_mono monofun_def some_below ubdom_below)

lemma med_tsb_getc: assumes "chain (Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>)" and "ubDom\<cdot>(\<Squnion>i::nat. Y i) = {In}"
                      and "c = Out" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "(\<Squnion>i::nat. Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Y i  .  In))\<cdot>bst)]))  .  Out
          =  (\<Squnion>i::nat. (Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Y i  .  In))\<cdot>bst)])) . Out)"
proof -
  have f1: "\<forall>c f u ca ua s. ((ctype c::'a MABP set) \<noteq> range f \<or> ubDom\<cdot>u \<noteq> {ca} \<or> u \<notsqsubseteq> ua) \<or> Abs_ubundle [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot> s)] \<sqsubseteq> Abs_ubundle [c \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(ua . ca))\<cdot>s)]"
    using med_tsb_mono by blast
  obtain nn :: "(nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) \<Rightarrow> nat" where
    f2: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
    using po_class.chain_def by moura
  then have f3: "\<forall>n. Y n \<sqsubseteq> Y (Suc n)"
    by (metis (no_types) assms(1))
  have "ubDom\<cdot> (Y (nn (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Y n . In))\<cdot> bst)]))) = {In}"
    by (simp add: assms(1) assms(2))
  then have "chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Y n . In))\<cdot>bst)])"
    using f3 f2 f1 by (meson assms(4))
  then show ?thesis
    using contlub_cfun_arg by blast
qed
(*proof (rule lubgetCh)
  have f2: "\<And> i. ubDom\<cdot>(Y i) =  ubDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  show tb_chain: "chain (\<lambda>i::nat. Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Y i  .  In))\<cdot>bst)]))"
    by (simp add: assms po_class.chainE po_class.chainI med_tsb_mono)
  show "Out \<in> ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Y i  .  In))\<cdot>bst)]))"
    by (metis (mono_tags, lifting) assms(4) insertCI med_tsb_dom tb_chain ubdom_chain_eq2)
qed*)

lemma med_cont [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "cont (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> (tsMap
                                f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)]))"
proof -
  have g1: " \<And>Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {In} \<Longrightarrow>
       ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Y i  .  In))\<cdot>bst)])) = {Out}"
  proof -
    fix Y :: "nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
    assume a1: "chain Y"
    assume a2: "UBundle.ubDom\<cdot>(\<Squnion>i. Y i) = {In}"
    obtain nn :: "(nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) \<Rightarrow> nat" where
      f3: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
      using po_class.chain_def by moura
    have f4: "\<forall>c f u ca ua s. ((ctype c::'a MABP set) \<noteq> range f \<or> UBundle.ubDom\<cdot>u \<noteq> {ca} \<or> u \<notsqsubseteq> ua) \<or> Abs_ubundle [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot> s)] \<sqsubseteq> Abs_ubundle [c \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(ua . ca))\<cdot>s)]"
      using med_tsb_mono by blast
    have "UBundle.ubDom\<cdot> (Y (nn (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Y n . In))\<cdot> bst)]))) = {In}"
      using a2 a1 by simp
    then have "chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Y n . In))\<cdot>bst)])"
      using f4 f3 a1 by (meson assms)
    then show "UBundle.ubDom\<cdot> (\<Squnion>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Y n . In))\<cdot>bst)]) = {Out}"
      using assms med_tsb_dom ubdom_chain_eq2 by blast
  qed
  (*  by (metis (mono_tags, lifting) assms med_tsb_dom med_tsb_mono po_class.chain_def ubdom_chain_eq2)*) (*geht auch, aber langsam*)

  have g2: "\<And>Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {In} \<Longrightarrow>
       Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((\<Squnion>i::nat. Y i)  .  In))\<cdot>bst)]) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle([Out \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Y i  .  In))\<cdot>bst)]))"
    apply (rule ub_below)
    apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq g1)
    apply (simp add: assms med_tsb_getc ubdom_ubrep_eq ubgetch_ubrep_eq)
    apply (simp add: medh_contlub to_medh)
    proof -
      fix Y :: "nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>" and c :: channel
      assume a1: "chain Y"
      assume a2: "UBundle.ubDom\<cdot>(\<Squnion>i. Y i) = {In}"
      assume a3: "c \<in> UBundle.ubDom\<cdot> (Abs_ubundle [Out \<mapsto> \<Squnion>i. medH bst In f (Y i)])"
      have f4: "\<forall>f. \<not> ubWell f \<or> Rep_ubundle (Abs_ubundle f::'a MABP tstream\<^sup>\<Omega>) = f"
        by auto
      obtain nn :: "(nat \<Rightarrow> 'a MABP tstream) \<Rightarrow> (nat \<Rightarrow> 'a MABP tstream) \<Rightarrow> nat" where
        f5: "\<forall>f fa. f (nn fa f) \<noteq> fa (nn fa f) \<or> Lub f = Lub fa"
        by (meson lub_eq)
      have f6: "\<forall>c f ca u s. (ctype c::'a MABP set) \<noteq> range f \<or> ubWell [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot>s)]"
        by auto
      then have f7: "ubWell [Out \<mapsto> medH bst In f (Y (nn (\<lambda>n. medH bst In f (Y n)) (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out)))]"
        by (simp add: assms to_medh)
      have f8: "\<forall>f n. \<not> chain f \<or> UBundle.ubDom\<cdot>(f n::'a MABP tstream\<^sup>\<Omega>) = UBundle.ubDom\<cdot>(Lub f)"
        using ubdom_chain_eq2 by blast
      have f9: "\<forall>c f u ca ua s. ((ctype c::'a MABP set) \<noteq> range f \<or> UBundle.ubDom\<cdot>u \<noteq> {ca} \<or> u \<notsqsubseteq> ua) \<or> Abs_ubundle [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot> s)] \<sqsubseteq> Abs_ubundle [c \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(ua . ca))\<cdot>s)]"
        using med_tsb_mono by blast
      obtain nna :: "(nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) \<Rightarrow> nat" where
        f10: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nna f) \<notsqsubseteq> f (Suc (nna f)))"
        using po_class.chain_def by moura
      then have "Abs_ubundle [Out \<mapsto> medH bst In f (Y (nna (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])))] \<sqsubseteq> Abs_ubundle [Out \<mapsto> medH bst In f (Y (Suc (nna (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]))))]"
        using f9 a2 a1 by (simp add: assms to_medh)
      then have f11: "chain (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])"
        using f10 by auto
      then have "UBundle.ubDom\<cdot> (Abs_ubundle [Out \<mapsto> medH bst In f (Y (nn (\<lambda>n. medH bst In f (Y n)) (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out)))]) = UBundle.ubDom\<cdot> (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])"
        using f8 by meson
      then have "[Out \<mapsto> medH bst In f (Y (nn (\<lambda>n. medH bst In f (Y n)) (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out)))] Out = Some (Abs_ubundle [Out \<mapsto> medH bst In f (Y (nn (\<lambda>n. medH bst In f (Y n)) (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out)))] . Out)"
        using f8 f7 ubdom_insert ubgetchE by fastforce
      then have "Abs_ubundle [Out \<mapsto> medH bst In f (Y (nn (\<lambda>n. medH bst In f (Y n)) (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out)))] . Out = medH bst In f (Y (nn (\<lambda>n. medH bst In f (Y n)) (\<lambda>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out)))"
        by force
      then have "(\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)] . Out) = (\<Squnion>n. medH bst In f (Y n))"
        using f5 by meson
      then have "ubWell [Out \<mapsto> (Rep_ubundle (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]))\<rightharpoonup>Out] \<longrightarrow> [Out \<mapsto> (Rep_ubundle (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]))\<rightharpoonup>Out] c = Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (Y n)] . c)"
        using f11 f4 a3 by (metis (no_types) contlub_cfun_arg ubgetchE ubgetch_insert)
      then have f12: "ubWell [Out \<mapsto> (Rep_ubundle (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]))\<rightharpoonup>Out] \<longrightarrow> c = Out \<and> (((Rep_ubundle (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]))\<rightharpoonup>Out) = ((Rep_ubundle (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (Y n)]))\<rightharpoonup>c)) \<or> c \<noteq> Out \<and> (None = Some ((Rep_ubundle (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (Y n)]))\<rightharpoonup>c))"
        using map_upd_Some_unfold ubgetch_insert by fastforce
      then have f13: "ubWell [Out \<mapsto> (Rep_ubundle (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]))\<rightharpoonup>Out] \<longrightarrow> Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (Y n)] . c = (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]) . Out"
        by (metis (no_types) option.simps(3) ubgetch_insert)
      have f14: "Rep_ubundle (Abs_ubundle [Out \<mapsto> medH bst In f (Y (v2_4 (\<lambda>n. UBundle.ubDom\<cdot> (Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])) (\<lambda>n. UBundle.ubDom\<cdot>(Y n))))]) = [Out \<mapsto> medH bst In f (Y (v2_4 (\<lambda>n. UBundle.ubDom\<cdot> (Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])) (\<lambda>n. UBundle.ubDom\<cdot>(Y n))))]"
        using f6 by (simp add: assms to_medh)
      have "dom [Out \<mapsto> medH bst In f (Y (v2_4 (\<lambda>n. UBundle.ubDom\<cdot> (Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])) (\<lambda>n. UBundle.ubDom\<cdot>(Y n))))] = insert Out (dom (Map.empty::channel \<Rightarrow> 'a MABP tstream option))"
        by force
      then have "Out \<in> UBundle.ubDom\<cdot> (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)])"
        using f14 f11 f8 by (metis (no_types) dom_empty singletonI ubdom_insert)
      then show "Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (Y n)] . c \<sqsubseteq> (\<Squnion>n. Abs_ubundle [Out \<mapsto> medH bst In f (Y n)]) . c"
        using f13 f12 by (simp add: ubWell_single_channel)
    qed

  show ?thesis
    apply (rule contI2)
    apply (simp add: assms ub_below)
    apply (simp add: med_tsb_getc ubdom_ubrep_eq ubgetch_ubrep_eq)
    apply (simp add: medh_contlub to_medh)
    proof -
      have f1: "\<forall>u ua. (u::'a MABP tstream\<^sup>\<Omega>) \<notsqsubseteq> ua \<or> Some u \<sqsubseteq> Some ua"
        using some_below by blast
      have f2: "\<forall>fa. (\<not> chain fa \<or> UBundle.ubDom\<cdot>(Lub fa) \<noteq> {In}) \<or> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub fa . In))\<cdot> bst)] \<sqsubseteq> (\<Squnion>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(fa n . In))\<cdot>bst)])"
        using g2 by blast
      obtain nn :: "(nat \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option) \<Rightarrow> (nat \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option) \<Rightarrow> nat" where
        f3: "\<forall>f fa. f (nn fa f) \<noteq> fa (nn fa f) \<or> Lub f = Lub fa"
        by (meson lub_eq)
      have "Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 (nn (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)])) (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))))]) = Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (v0_0 (nn (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)])) (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))) . In))\<cdot> bst)])"
        by (simp add: to_medh)
      then have f4: "(\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)])) = (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot>bst)]))"
        using f3 by meson
      have f5: "\<forall>f. \<not> chain f \<or> (\<Squnion>n. Some (f n::'a MABP tstream\<^sup>\<Omega>)) = Some (Lub f)"
        using some_lub_chain_eq3 by blast
      have f6: "\<forall>c f u ca ua s. ((ctype c::'a MABP set) \<noteq> range f \<or> UBundle.ubDom\<cdot>u \<noteq> {ca} \<or> u \<notsqsubseteq> ua) \<or> Abs_ubundle [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot> s)] \<sqsubseteq> Abs_ubundle [c \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(ua . ca))\<cdot>s)]"
        by (metis (no_types) med_tsb_mono)
      obtain nna :: "(nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) \<Rightarrow> nat" where
        f7: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nna f) \<notsqsubseteq> f (Suc (nna f)))"
        using po_class.chain_def by moura
      then have f8: "(\<not> chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)]) \<or> (\<forall>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)] \<sqsubseteq> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 (Suc n) . In))\<cdot> bst)])) \<and> (chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)]) \<or> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (v0_0 (nna (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)])) . In))\<cdot> bst)] \<notsqsubseteq> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (v0_0 (Suc (nna (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot> bst)]))) . In))\<cdot> bst)])"
        by auto
      { assume "Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (v0_0 n)]) \<notsqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))"
        { assume "(Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (v0_0 n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))) \<noteq> (Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub v0_0 . In))\<cdot> bst)]) \<sqsubseteq> Some (\<Squnion>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot>bst)]))"
        then have "(\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)])) \<noteq> Some (\<Squnion>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0 n . In))\<cdot>bst)]) \<or> (\<Squnion>n. medH bst In f (v0_0 n)) \<noteq> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub v0_0 . In))\<cdot>bst)"
          by auto
        moreover
          { assume "(\<Squnion>n. medH bst In f (v0_0 n)) \<noteq> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub v0_0 . In))\<cdot>bst)"
          then have "(UBundle.ubDom\<cdot>(Lub v0_0) \<noteq> {In} \<or> \<not> chain v0_0) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (v0_0 n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))"
            by (metis (no_types) cont2contlubE medh_cont to_medh)
          }
        ultimately have "(UBundle.ubDom\<cdot>(Lub v0_0) \<noteq> {In} \<or> \<not> chain v0_0) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (v0_0 n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))"
          using f8 f7 f6 f5 f4 assms by force
        }
        then have "(UBundle.ubDom\<cdot>(Lub v0_0) \<noteq> {In} \<or> \<not> chain v0_0) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (v0_0 n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))"
          using f2 f1 by meson
      }
      then have f9: "(UBundle.ubDom\<cdot>(Lub v0_0) \<noteq> {In} \<or> \<not> chain v0_0) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (v0_0 n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0 n)]))"
        by meson
      obtain uu :: "nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>" where
        "(\<exists>v0. (UBundle.ubDom\<cdot>(Lub v0) = {In} \<and> chain v0) \<and> Some (Abs_ubundle [Out \<mapsto> \<Squnion>uua. medH bst In f (v0 uua)]) \<notsqsubseteq> (\<Squnion>uua. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0 uua)]))) = ((UBundle.ubDom\<cdot>(Lub uu) = {In} \<and> chain uu) \<and> Some (Abs_ubundle [Out \<mapsto> \<Squnion>uua. medH bst In f (uu uua)]) \<notsqsubseteq> (\<Squnion>uua. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uu uua)])))"
        by (metis (no_types))
      then show "\<forall>fa. UBundle.ubDom\<cdot>(Lub fa) = {In} \<longrightarrow> chain fa \<longrightarrow> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (fa n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (fa n)]))"
        proof -
          obtain nnb :: "(nat \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option) \<Rightarrow> (nat \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option) \<Rightarrow> nat" where
            f1: "\<forall>f fa. f (nnb fa f) \<noteq> fa (nnb fa f) \<or> Lub f = Lub fa"
            by (meson lub_eq)
          have "Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0a (nnb (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)])) (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0a n)]))))]) = Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (v0_0a (nnb (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)])) (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0a n)]))) . In))\<cdot> bst)])"
            by (simp add: to_medh)
          then have f2: "(\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0_0a n)])) = (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot>bst)]))"
            using f1 by meson
          have f3: "\<forall>c f u ca ua s. (ctype c::'a MABP set) \<noteq> range f \<or> UBundle.ubDom\<cdot>u \<noteq> {ca} \<or> u \<notsqsubseteq> ua \<or> Abs_ubundle [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot> s)] \<sqsubseteq> Abs_ubundle [c \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(ua . ca))\<cdot>s)]"
            using med_tsb_mono by blast
          obtain nnc :: "(nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) \<Rightarrow> nat" where
            f4: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nnc f) \<notsqsubseteq> f (Suc (nnc f)))"
            using po_class.chain_def by moura
          then have f5: "(\<not> chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)]) \<or> (\<forall>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)] \<sqsubseteq> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0a (Suc n) . In))\<cdot> bst)])) \<and> (chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)]) \<or> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (v0_0a (nnc (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)])) . In))\<cdot> bst)] \<notsqsubseteq> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (v0_0a (Suc (nnc (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(v0_0a n . In))\<cdot> bst)]))) . In))\<cdot> bst)])"
            by auto
          obtain uua :: "nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>" where
            "(\<exists>v0. (UBundle.ubDom\<cdot>(Lub v0) = {In} \<and> chain v0) \<and> Some (Abs_ubundle [Out \<mapsto> \<Squnion>uua. medH bst In f (v0 uua)]) \<notsqsubseteq> (\<Squnion>uua. Some (Abs_ubundle [Out \<mapsto> medH bst In f (v0 uua)]))) = ((UBundle.ubDom\<cdot>(Lub uua) = {In} \<and> chain uua) \<and> Some (Abs_ubundle [Out \<mapsto> \<Squnion>uuaa. medH bst In f (uua uuaa)]) \<notsqsubseteq> (\<Squnion>uuaa. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua uuaa)])))"
            by moura
          moreover
          { assume "Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (uua n)]) \<notsqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))"
            { assume "(Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (uua n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))) \<noteq> (Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub uua . In))\<cdot> bst)]) \<sqsubseteq> Some (\<Squnion>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot>bst)]))"
            moreover
              { assume "(\<Squnion>n. medH bst In f (uua n)) \<noteq> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub uua . In))\<cdot>bst)"
              then have "(UBundle.ubDom\<cdot>(Lub uua) \<noteq> {In} \<or> \<not> chain uua) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (uua n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))"
                by (metis (no_types) medh_contlub to_medh)
              }
              ultimately have "(UBundle.ubDom\<cdot>(Lub uua) \<noteq> {In} \<or> \<not> chain uua) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (uua n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))"
                using f5 f4 f3 f2 assms f5 
                proof -
                  have f1: "\<forall>f. \<not> chain f \<or> Some (Lub f::'a MABP tstream\<^sup>\<Omega>) = (\<Squnion>n. Some (f n))"
                    using some_lub_chain_eq by auto
                  have f2: "\<forall>c f u ca ua s. ((ctype c::'a MABP set) \<noteq> range f \<or> UBundle.ubDom\<cdot>u \<noteq> {ca} \<or> u \<notsqsubseteq> ua) \<or> Abs_ubundle [c \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(u . ca)::'b tstream)\<cdot> s)] \<sqsubseteq> Abs_ubundle [c \<mapsto> tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(ua . ca))\<cdot>s)]"
                    by (metis (no_types) med_tsb_mono)
                  obtain nnd :: "(nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) \<Rightarrow> nat" where
                    f3: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nnd f) \<notsqsubseteq> f (Suc (nnd f)))"
                    using po_class.chain_def by moura
                  then have f4: "(\<not> chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot> bst)]) \<or> (\<forall>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot> bst)] \<sqsubseteq> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua (Suc n) . In))\<cdot> bst)])) \<and> (chain (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot>bst)]) \<or> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (uua (nnd (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(uua n . In))\<cdot> bst)])) . In))\<cdot> bst)] \<notsqsubseteq> Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (uua (Suc (nnd (\<lambda>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(uua n . In))\<cdot> bst)]))) . In))\<cdot> bst)])"
                    by meson
                  obtain nne :: "(nat \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option) \<Rightarrow> (nat \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) option) \<Rightarrow> nat" where
                    f5: "\<forall>f fa. f (nne fa f) \<noteq> fa (nne fa f) \<or> Lub f = Lub fa"
                    by (meson lub_eq)
                  have "Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua (nne (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(uua n . In))\<cdot> bst)])) (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))))]) = Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot> (uua (nne (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot> (tsMap (inv f)\<cdot>(uua n . In))\<cdot> bst)])) (\<lambda>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))) . In))\<cdot> bst)])"
                    by (simp add: to_medh)
                  then have f6: "(\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)])) = (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot>bst)]))"
                    using f5 by meson
                  { assume "Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub uua . In))\<cdot> bst)]) \<sqsubseteq> Some (\<Squnion>n. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot>bst)])"
                  then have "UBundle.ubDom\<cdot>(Lub uua) \<noteq> {In} \<or> \<not> chain uua \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (uua n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))"
                    using f6 f4 f3 f2 f1 \<open>(\<Squnion>n::nat. medH (bst::bool stream) (In::channel) (f::'b::countable \<Rightarrow> 'a::countable MABP) ((uua::nat \<Rightarrow> 'a::countable MABP tstream\<^sup>\<Omega>) n)) \<noteq> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub uua . In))\<cdot> bst) \<Longrightarrow> (UBundle.ubDom\<cdot>(Lub uua) \<noteq> {In} \<or> \<not> chain uua) \<or> Some (Abs_ubundle [Out::channel \<mapsto> \<Squnion>n::nat. medH bst In f (uua n)]) \<sqsubseteq> (\<Squnion>n::nat. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))\<close> assms by force
                  }
                  then show ?thesis
                    using \<open>(Some (Abs_ubundle [Out::channel \<mapsto> \<Squnion>n::nat. medH (bst::bool stream) (In::channel) (f::'b::countable \<Rightarrow> 'a::countable MABP) ((uua::nat \<Rightarrow> 'a::countable MABP tstream\<^sup>\<Omega>) n)]) \<sqsubseteq> (\<Squnion>n::nat. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))) \<noteq> (Some (Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(Lub uua . In))\<cdot> bst)]) \<sqsubseteq> Some (\<Squnion>n::nat. Abs_ubundle [Out \<mapsto> tsMap f\<cdot> (tsMed\<cdot>(tsMap (inv f)\<cdot>(uua n . In))\<cdot>bst)]))\<close> by linarith
                qed
            }
            then have "(UBundle.ubDom\<cdot>(Lub uua) \<noteq> {In} \<or> \<not> chain uua) \<or> Some (Abs_ubundle [Out \<mapsto> \<Squnion>n. medH bst In f (uua n)]) \<sqsubseteq> (\<Squnion>n. Some (Abs_ubundle [Out \<mapsto> medH bst In f (uua n)]))"
              using g2 some_below by blast
          }
          ultimately show ?thesis
            by blast
        qed
    qed
qed


  subsubsection \<open>tspf_well\<close>
 (* show that the mediumRSTSPF template  fulfills the tickcount property *)
lemma med_tick: assumes "ubDom\<cdot>b = {In}" and "(ubLen b) = n" and "#bst=\<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "n \<le> (ubclLen (Abs_ubundle([Out \<mapsto> (tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((b . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)])))"
proof -
  have "(ubLen b) = usclLen\<cdot>(b . In)"
    apply (rule uslen_ubLen_ch3)
    by (metis assms(1))
  hence f1: "n = usclLen\<cdot>(b . In)"
    using assms(2) by blast
  hence f2: "n \<le> usclLen\<cdot>(tsMap f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(b  .  In))\<cdot>bst))"
    by (simp add: assms(3) usclLen_tstream_def)
  show ?thesis
    apply (simp add: ubclLen_ubundle_def)
    apply (rule ubLen_geI)
    apply (simp add: assms med_tsb_dom ubgetch_ubrep_eq)
    by (simp add: assms f2 ubdom_ubrep_eq)
qed



  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma med_well [simp]: assumes "#bst=\<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ufWell (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> (tsMap
                                f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)]))"
  apply (rule ufun_wellI)
  apply (simp_all add: domIff2 assms)
  by  (simp_all add: med_tsb_dom assms ubclDom_ubundle_def)


lemma med_revsubst: "Abs_cufun (tsMedAbb bst In Out f) = (med_TSPF bst In Out f)"
  by (simp add: med_TSPF_def)


lemma med_tspfdom: assumes "#bst =\<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ufDom\<cdot>((med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) bst In Out f) = {In}"
  apply (simp add: med_TSPF_def)
  apply (simp add: ufdom_insert)
  apply (simp_all add: assms)
  apply (simp add: domIff)
  by (metis ubclDom_h ubclDom_ubundle_def)


lemma med_tspfran: assumes "#bst =\<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ufRan\<cdot>((med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) bst In Out f) = {Out}"
  apply (simp add: med_TSPF_def)
  apply (simp add: ufran_least med_tspfdom assms)
  apply (simp add: med_revsubst med_tspfdom assms)
  by (metis assms(2) med_tsb_dom ubclDom_ubundle_def ubcldom_least_cs)

  (* now special lemmata for TSPS instantiation *)

lemma med_well2 [simp]: assumes "#({True} \<ominus> bst) = \<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ufWell (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> (tsMap
                                f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>((x . In):: 'a MABP tstream))\<cdot>bst):: 'a MABP tstream)]))"
proof -
   have "#bst = \<infinity>"
     by (simp add: med_ora_length assms(1))
   thus ?thesis
     by (simp add: assms(2))
 qed


lemma med_tspfdom2: assumes "#({True} \<ominus> bst) = \<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ufDom\<cdot>((med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) bst In Out f) = {In}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: assms med_tspfdom)
qed


lemma med_tspfran2: assumes "#({True} \<ominus> bst) = \<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f"
  shows "ufRan\<cdot>((med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) bst In Out f) = {Out}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: assms(2) med_tspfran)
qed


  (* necessary for TSPS instantiation *)
lemma med_tsps_dom1 [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f" shows
  "g = (med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) ora In Out f \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufDom\<cdot>g = {In}"
  by (simp add: assms med_tspfdom2)


lemma med_tsps_dom2 [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f" shows
  "\<exists>ora::bool stream. g = (med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) ora In Out f \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufDom\<cdot>g = {In}"
  using assms med_tsps_dom1 by auto


lemma med_tsps_ran1 [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f" shows
  "g = (med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) ora In Out f \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufRan\<cdot>g = {Out}"
  by (simp add: assms med_tspfran2)


lemma med_tsps_ran2 [simp]: assumes "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f" shows
  "\<exists>ora::bool stream. g = (med_TSPF :: bool stream \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> ('b \<Rightarrow> 'a MABP) \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>)ufun) ora In Out f \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufRan\<cdot>g = {Out}"
  using assms med_tsps_ran1 by auto


lemma med_ufIsWeak: assumes "#bst =\<infinity>" and "(ctype::channel \<Rightarrow> 'a MABP set) Out = range f" shows
  "ufIsWeak (Abs_ufun(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubDom\<cdot>x = {In})
                           \<leadsto> Abs_ubundle([Out \<mapsto> tsMap
                                f\<cdot>(tsMed\<cdot>(tsMap (inv f)\<cdot>(x . In))\<cdot>bst)])))"
  apply (simp add: ufIsWeak_def)
  apply (simp add: assms domIff)
  apply (rule, rule)
  apply (subst med_tick)
  by (simp_all add: assms ubclLen_ubundle_def)

subsection\<open>id\<close>


subsubsection\<open>mono/cont\<close>


lemma idTSPF_mono: "monofun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> x)"
  by (simp add: monofunI some_below ubdom_below)

lemma idTSPF_cont: "cont (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> x)"
  apply(rule contI2)
   apply(simp add: idTSPF_mono)
  using some_lub_chain_eq by fastforce


subsubsection\<open>ufWell/tickCount\<close>


lemma idTSPF_well: "ufWell (\<Lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> x)"
  apply(rule ufun_wellI)
    by (simp_all add: idTSPF_cont domIff2 ubclDom_ubundle_def)

lemma idTSPF_tickCount: "ufIsWeak (Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> x))"
  apply(simp add: ufIsWeak_def)
  by (simp add: idTSPF_cont idTSPF_well domIff rep_abs_cufun) 

lemma idTSPF_dom: "ufDom\<cdot>idTSPF = {c_abpOut}"
  apply(simp add: idTSPF_def)
  apply (fold ubclDom_ubundle_def)
  apply (subst ufun_ufdom_abs)
  by (simp_all add: ubclDom_ubundle_def idTSPF_cont idTSPF_well)

lemma idTSPF_ran: "ufRan\<cdot>idTSPF = {c_abpOut}"
  apply(simp add: idTSPF_def)
proof -
have f1: "\<forall>f. \<not> cont f \<or> \<not> ufWell (Abs_cfun f) \<or> Rep_cufun (Abs_cufun f::('a MABP tstream\<^sup>\<Omega>) ufun) = f"
  by (metis rep_abs_cufun)
  then have f2: "Rep_cufun (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)) = (\<lambda>u. (ubDom\<cdot>u = {c_abpOut})\<leadsto>u)"
    using idTSPF_cont idTSPF_well by blast
  have "ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u))) \<in> dom (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)"
    using f1 by (metis (no_types) idTSPF_cont idTSPF_well ufunLeastIDom)
  then have f3: "(ubDom\<cdot> (ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)))::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot> (u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)))::'a MABP tstream\<^sup>\<Omega> \<noteq> None"
    by blast
  then have "Rep_cufun (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)) (ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)))) = Some (ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u))))"
    using f2 by presburger
  then have "Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u) \<rightleftharpoons> ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u))) = ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)))"
    by (metis option.sel)
  then have f4: "ufRan\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)) = ubclDom\<cdot> (ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)))::'a MABP tstream\<^sup>\<Omega>)"
    by (simp add: UFun_Comp.ufran_least)
  have "Rep_cufun (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)) (ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)))) = Some (ubclLeast (ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u))))"
    using f3 f2 by presburger
  then have "ufRan\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)) = ufDom\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u))"
    using f4 ufdom_2ufundom by blast
  then show "ufRan\<cdot> (Abs_cufun (\<lambda>u. (ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut})\<leadsto>u)) = {c_abpOut}"
    by (metis (no_types) idTSPF_dom idTSPF_def)
qed

subsection\<open>id2\<close>

lemma c_abpOut_idOut_ctype_eq: "\<And> x::('a MABP tstream). usclOkay c_idOut x = usclOkay c_abpOut x"
  by (simp add: usclOkay_tstream_def)

lemma idTSPF2_result_ubwell:  assumes "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}" 
  shows "ubWell [c_idOut \<mapsto> (x::('a MABP tstream\<^sup>\<Omega>)) . c_abpOut]"
  apply (rule ubwellI)
  apply (simp add: domIff)
  by (simp add: assms c_abpOut_idOut_ctype_eq ubgetch_insert)

lemma idTSPF2_result_dom:  assumes "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}" 
  shows "ubDom\<cdot>(Abs_ubundle [c_idOut \<mapsto> (x::('a MABP tstream\<^sup>\<Omega>)) . c_abpOut]) = {c_idOut}"
  by (simp add: assms idTSPF2_result_ubwell ubdom_ubrep_eq)

lemma idTSPF2_io_eq: assumes "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}"
  shows "((\<lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> x . c_abpOut])\<rightharpoonup>x) . c_idOut
    = (x::'a MABP tstream\<^sup>\<Omega>) . c_abpOut"
  apply simp apply rule
  apply (simp add: idTSPF2_result_ubwell ubgetch_ubrep_eq)
  by (simp add: assms)

lemma idTSPF2_result_below: assumes "(x::('a MABP tstream\<^sup>\<Omega>)) \<sqsubseteq> y" 
  and "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}"
  shows "Abs_ubundle [c_idOut \<mapsto> x . c_abpOut] \<sqsubseteq>  Abs_ubundle [c_idOut \<mapsto> y . c_abpOut]"
  apply (rule ub_below)
   apply (subst ubdom_ubrep_eq)
    apply (simp add: assms(2) idTSPF2_result_ubwell)
   apply (subst ubdom_ubrep_eq)
  using assms(1) assms(2) idTSPF2_result_ubwell ubdom_below apply blast
   apply (simp add: domIff)
  apply (simp add: assms idTSPF2_result_dom)
  apply (subst ubgetch_ubrep_eq) 
    apply (simp add: assms(2) idTSPF2_result_ubwell)
  apply (subst ubgetch_ubrep_eq) 
  using assms(1) assms(2) idTSPF2_result_ubwell ubdom_below apply blast
  by (simp add: assms(1) monofun_cfun_arg)

subsubsection\<open>mono/cont\<close>

lemma idTSPF2_mono: "monofun (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> x . c_abpOut])"
  apply (rule monofunI)
  apply (case_tac "(ubDom\<cdot>x \<noteq> {c_abpOut})")
   apply (simp add: ubdom_below)
  apply (simp) apply (rule, rule)
   apply (rule some_below)
   apply (rule ub_below)
    apply (simp add: ubdom_ubrep_eq idTSPF2_result_ubwell)
   apply (simp add: cont2monofunE idTSPF2_result_ubwell ubgetch_ubrep_eq)
  by (simp add: ubdom_below)


lemma idTSPF2_cont: "cont (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> x . c_abpOut])"
  apply(rule contI2)
   apply (simp add: idTSPF2_mono)
proof (rule, rule)
  fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
  assume a1: "chain Y"
  have f1: "\<And> i. ubDom\<cdot>(\<Squnion>i::nat. Y i) = ubDom\<cdot>(Y i)"
    by (simp add: a1)
  have f2: "ubDom\<cdot>(Lub Y) = {c_abpOut} \<Longrightarrow> Some (\<Squnion>i::nat. (Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])) = 
    (\<Squnion>i::nat. Some (Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut]))"
    apply (rule some_lub_chain_eq2)
    apply (rule chainI)
    apply (rule idTSPF2_result_below)
     apply (simp add: a1 po_class.chainE)
    by (simp add: a1)
  have f30: "\<And>c.  ubDom\<cdot>(Lub Y) = {c_abpOut} \<Longrightarrow>  c \<in> ubDom\<cdot>(Abs_ubundle [c_idOut \<mapsto> Lub Y  .  c_abpOut])  
        \<Longrightarrow> (\<Squnion>i::nat. Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])  .  c = 
              (\<Squnion>i::nat. Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut] .  c)"
    apply (rule ubgetch_lub)
    apply (rule chainI)
     apply (rule idTSPF2_result_below)
      apply (simp add: a1 po_class.chainE)
     apply (simp add: a1)
    by (metis (mono_tags, lifting) a1 idTSPF2_result_below idTSPF2_result_dom po_class.chainE po_class.chainI ubdom_chain_eq2)
  have f31: "ubDom\<cdot>(Lub Y) = {c_abpOut} \<Longrightarrow> ubDom\<cdot>(Abs_ubundle [c_idOut \<mapsto> Lub Y  .  c_abpOut]) = {c_idOut}"
    by (simp add: idTSPF2_result_dom)
  have f3: " ubDom\<cdot>(Lub Y) = {c_abpOut} \<Longrightarrow> Some (Abs_ubundle [c_idOut \<mapsto> Lub Y  .  c_abpOut]) \<sqsubseteq> 
         Some (\<Squnion>i::nat. (Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut]))"
    apply (rule some_below)
    apply (rule ub_below)
     apply (metis (mono_tags, lifting) a1 idTSPF2_result_below idTSPF2_result_dom po_class.chainE po_class.chainI ubdom_chain_eq2)
    apply (subst ubgetch_ubrep_eq)
     apply (simp add: idTSPF2_result_ubwell)  
    apply (simp only: f30)    
    apply (subst ubgetch_ubrep_eq)
     apply (simp add: a1 idTSPF2_result_ubwell)
    apply (simp add: f31)
    by (metis a1 below_refl contlub_cfun_arg)
  show "(ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c_abpOut})\<leadsto>Abs_ubundle [c_idOut \<mapsto> (\<Squnion>i::nat. Y i)  .  c_abpOut] 
    \<sqsubseteq> (\<Squnion>i::nat. (ubDom\<cdot>(Y i) = {c_abpOut})\<leadsto>Abs_ubundle [c_idOut \<mapsto> Y i  .  c_abpOut])"
    apply (case_tac "ubDom\<cdot>(\<Squnion>i::nat. Y i) \<noteq> {c_abpOut}")
     apply (simp_all add: a1)
    using f2 f3 by auto
qed

subsubsection\<open>ufWell/tickCount\<close>


lemma idTSPF2_well: "ufWell (\<Lambda> (x::('a MABP tstream\<^sup>\<Omega>)). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> x . c_abpOut])"
  apply(rule ufun_wellI)
    apply(simp_all add: idTSPF2_cont ubclDom_ubundle_def domIff2)
  apply (subst ubdom_ubrep_eq)
  by (simp_all add: idTSPF2_result_ubwell domIff)

lemma idTSPF2_tickCount: "ufIsWeak (Abs_cufun (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> x . c_abpOut]))"
  apply(simp add: ufIsWeak_def)
  apply (rule, rule)
  apply (simp add: idTSPF2_well idTSPF2_cont domIff2)
  apply (simp add: ubclLen_ubundle_def)
  by (simp add: idTSPF2_result_ubwell uslen_ubLen_ch1 uslen_ubLen_ch3)

lemma idTSPF2_dom: "ufDom\<cdot>idTSPF2 = {c_abpOut}"
  apply(simp add: idTSPF2_def)
  apply (fold ubclDom_ubundle_def)
  apply (subst ufun_ufdom_abs)
  by (simp_all add: ubclDom_ubundle_def idTSPF2_cont idTSPF2_well)

lemma idTSPF2_ran: "ufRan\<cdot>idTSPF2 = {c_idOut}"
  apply (simp add: ufran_least)
  apply(simp add: idTSPF2_dom)
  apply(simp add: ubclDom_ubundle_def idTSPF2_def)
  apply (simp add: rep_abs_cufun idTSPF2_cont idTSPF2_well)
  apply (rule, rule)
   apply (simp add: idTSPF2_result_dom)
  by (simp add: ubclLeast_ubundle_def)


(* ----------------------------------------------------------------------- *)
section \<open>Components\<close>
(* ----------------------------------------------------------------------- *)


lemma h1: "inv Rev (Rev S) = S"
  by (meson injI inv_f_eq rev.inject)

lift_definition SND :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {senderTSPF s | s. s \<in> tsSender}"
  apply(subst h1)
  apply(simp add: uspecWell_def)
  apply(simp add: ufclDom_ufun_def ufclRan_ufun_def)
  using sender_tspfdom sender_tspfran
  by metis

lift_definition RCV :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {recvTSPF}"
  apply(subst h1)
  by(simp add: uspecWell_def)

lift_definition MEDSR :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (simp add: inv_def)
  apply (simp add: uspecWell_def)
  apply (subst ufclDom_ufun_def)
  apply (subst  ufclRan_ufun_def)
  using med_tsps_dom2 med_tsps_ran2 by (metis ctype_MABP.simps(4))

lift_definition MEDRS :: "('a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (simp add: inv_def)
  apply (simp add: uspecWell_def)
  apply (subst ufclDom_ufun_def)
  apply (subst  ufclRan_ufun_def)
  using med_tsps_dom2 med_tsps_ran2 by (metis ctype_MABP.simps(5))

lift_definition ID :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {idTSPF2}"
  apply(subst h1)
  by(simp add: uspecWell_def)


abbreviation gencompABP :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"gencompABP \<equiv> ((SND \<Otimes> MEDSR) \<Otimes> RCV) \<Otimes> MEDRS"

abbreviation speccompABP :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"speccompABP \<equiv> uspecFeedbackComp(((SND \<circle> MEDSR) \<circle> RCV) \<circle> (MEDRS \<parallel> ID))"


(* ----------------------------------------------------------------------- *)
section \<open>Composition with special operators\<close>
(* ----------------------------------------------------------------------- *)


abbreviation innerABP where
"innerABP s ora1 ora2 \<equiv> (ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF2))"

abbreviation ABPBundleHelper where
"ABPBundleHelper se ora1 ora2 tb \<equiv> (\<lambda> x. [
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut  \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
    ])"


abbreviation fixABPHelper where
"fixABPHelper se ora1 ora2 tb \<equiv> (\<lambda> x. Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut  \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
    ])"

abbreviation fixABPHelperCont where
"fixABPHelperCont se ora1 ora2 tb \<equiv> (\<Lambda> x. Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
    ])"

abbreviation abpFix where
"abpFix s ora1 ora2 tb \<equiv> ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"

lemma abpHelper_ubWell: "\<And>x. ubWell [
      c_ds     \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
      c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
      c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
      c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
      c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
      c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
      ]"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)


lemma bla2: "tsDom\<cdot>ts \<subseteq> range Data \<longrightarrow> tsMap Data\<cdot>(tsMap (inv Data)\<cdot>ts) = ts"
   apply (rule tstream_induct)
    apply simp_all
   apply (simp add: tsmap_delayfun)
   apply (simp add: tsdom_delayfun)
  by (simp add: f_inv_into_f tsdom_mlscons tsmap_mlscons)

(*
lemma abpHelper_cont: assumes "#({True} \<ominus> ora1) = \<infinity>"
  and "#({True} \<ominus> ora2) = \<infinity>"
  and "se \<in> tsSender"
  and "ubDom\<cdot>tb = {c_abpIn}"
shows "cont (fixABPHelper se ora1 ora2 tb)"
  sorry


(* Lemma from Dennis group  *)
lemma tsaltbitpro_inp2out:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  sorry

*)
(*=================DDD=========================================*)
(* ----------------------------------------------------------------------- *)
section \<open>Component Definitions\<close>
(* ----------------------------------------------------------------------- *)

lemma id_consistent: "uspecIsConsistent ID"
  by (simp add: ID.rep_eq inv_def uspecIsConsistent_def)

lemma id_uspec_ele: "\<forall> ufun \<in> Rep_rev_uspec ID. ufun = idTSPF2"
  by (simp add: ID.rep_eq inv_rev_rev)

lemma id_uspec_dom: "uspecDom (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclDom\<cdot>(idTSPF2::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis id_consistent id_uspec_ele some_in_eq uspecDom_def uspecIsConsistent_def)

lemma id_uspec_ran: "uspecRan (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclRan\<cdot>(idTSPF2::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis id_consistent id_uspec_ele some_in_eq uspecIsConsistent_def uspecRan_def)


lemma rev_uspec_consistent: "uspecIsConsistent RCV"
  by (simp add: RCV.rep_eq inv_def uspecIsConsistent_def)

lemma rcv_uspec_ele: "\<forall> ufun \<in> Rep_rev_uspec RCV. ufun = recvTSPF"
  by (simp add: RCV.rep_eq inv_rev_rev)

lemma rcv_uspec_dom: "uspecDom (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclDom\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis rcv_uspec_ele rev_uspec_consistent some_in_eq uspecDom_def uspecIsConsistent_def)

lemma rcv_uspec_ran: "uspecRan (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclRan\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis rcv_uspec_ele rev_uspec_consistent some_in_eq uspecIsConsistent_def uspecRan_def)


lemma medrs_consist_dom: assumes "uspecIsConsistent (MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec)" 
  and "f \<in> Rep_rev_uspec (MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  shows "uspecDom (MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec) = ufclDom\<cdot>f"
  using uspec_dom_eq2 assms by blast

lemma medrs_rev_insert: "Rep_rev_uspec MEDRS = {medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  by (simp add: MEDRS.rep_eq inv_rev_rev)

lemma medsr_rev_insert: "Rep_rev_uspec MEDSR = {medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  by (simp add: MEDSR.rep_eq inv_rev_rev)
(* ----------------------------------------------------------------------- *)
section \<open>More Lemmas\<close>
(* ----------------------------------------------------------------------- *)

lemma c_as_bool_ctype: "ctype c_as = range Bool"
  by simp

lemma c_dr_boolpair_ctype: "ctype c_dr = range BoolPair"
  by simp

lemma medrs3_id_parcomp_well : "uspec_parcompwell MEDRS ID"
  proof (cases "\<not> uspecIsConsistent (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
    case True
    then show ?thesis 
      apply (simp_all add: uspec_parcompwell_def)
      by (simp add: uspecIsConsistent_def)
  next
    case False
    obtain f where f_def: "f \<in> Rep_rev_uspec (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
      using False uspec_consist_f_ex by auto
    have f1: "\<exists> ora. f = medRS_TSPF ora \<and> #({True} \<ominus> ora)=\<infinity>"
      using f_def medrs_rev_insert by auto
    obtain ora where ora_def: "f = medRS_TSPF ora" and ora_def2: "#({True} \<ominus> ora)=\<infinity>"
      using f1 by blast
    have f1: "uspecDom (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        = ufclDom\<cdot>((medRS_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
      using f_def ora_def uspec_dom_eq by auto
    have f4: "parcomp_well ((medRS_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora) (idTSPF2::('a MABP tstream\<^sup>\<Omega>) ufun)"
      apply rule
       apply (simp add: ufCompL_def)
       apply (simp_all only: idTSPF2_ran idTSPF2_dom)
       apply (simp_all only: ora_def2 c_as_bool_ctype med_tspfdom2)
       apply (simp_all only: ora_def2 c_as_bool_ctype med_tspfran2)
      by blast +
    show ?thesis 
      apply (simp_all add: uspec_parcompwell_def)
      apply (simp_all add: ufunclParCompWell_ufun_def)
      apply (rule, rule)
      by (metis ID.rep_eq f4 f_def insert_iff inv_rev_rev ora_def 
          ufCompL_def ufclDom_ufun_def ufclRan_ufun_def uspec_allDom uspec_ran_eq)
  qed
lemma snd3_medsr3_sercomp_well: "uspec_sercompwell SND (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  proof (cases "\<not> uspecIsConsistent (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
    case True
    then show ?thesis 
      apply (simp_all add: uspec_sercompwell_def)
      by (simp add: uspecIsConsistent_def)
  next
    case False
    have f00: "uspecIsConsistent (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
      using False by auto
    then show ?thesis 
    proof (cases "\<not> uspecIsConsistent (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
      case True
      then show ?thesis 
        apply (simp_all add: uspec_sercompwell_def)
        by (simp add: uspecIsConsistent_def)
    next
      case False
      have f01: "uspecIsConsistent (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using False by auto
      obtain f where f_def: "f \<in> Rep_rev_uspec (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f00 uspec_consist_f_ex by auto
      obtain g where g_def: "g \<in> Rep_rev_uspec (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using False uspec_consist_f_ex by auto
      have f0: "\<exists> ora. f = medSR_TSPF ora \<and> #({True} \<ominus> ora)=\<infinity>"
        using f_def medsr_rev_insert by blast
      obtain ora where ora_def: "f = medSR_TSPF ora" and ora_def2: "#({True} \<ominus> ora)=\<infinity>"
        using f0 by auto
      have f01: "\<exists> s. g = senderTSPF s" 
      proof -
        have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND"
          by (simp add: SND.rep_eq inv_rev_rev)
        then show ?thesis
          using g_def by fastforce
      qed
      obtain snd where snd_def: "g = senderTSPF snd"
        using f01 by auto
      have f1: "uspecDom (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
          = ufclDom\<cdot>((medSR_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
        using f_def ora_def uspec_dom_eq by blast
      have f2: "\<forall> f \<in> Rep_rev_uspec (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
          ufclDom\<cdot>f = ufclDom\<cdot>((medSR_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora)"
        by (simp add: f1 uspec_dom_eq)
      have f3: "uspecDom (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) = ufclDom\<cdot>(senderTSPF snd)"
        using g_def local.snd_def uspec_dom_eq by blast
      have f4: "\<forall> f \<in> Rep_rev_uspec (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
          ufclDom\<cdot>f = ufclDom\<cdot>(senderTSPF snd)"
        using f3 uspec_dom_eq by blast
      have f5: "sercomp_well (senderTSPF snd) (medSR_TSPF ora)"
        apply rule
         apply (simp_all only: sender_tspfran ora_def2 c_dr_boolpair_ctype med_tspfdom2 med_tspfran2)
        apply (simp_all only: sender_tspfdom ora_def2 c_dr_boolpair_ctype med_tspfdom2)
        by simp
      then show ?thesis 
        apply (simp add: uspec_sercompwell_def)
        apply (simp add: ufunclSerCompWell_ufun_def)
        apply (rule, rule)
        by (metis f1 f3 f_def g_def local.snd_def ora_def ufclDom_ufun_def ufclRan_ufun_def 
            uspec_dom_eq uspec_ran_eq)
    qed
  qed

lemma snd3_medsr3_rev3_sercomp_well: "uspec_sercompwell (SND \<circle> MEDSR) (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  proof (cases "\<not> uspecIsConsistent ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
    case True
    then show ?thesis 
      apply (simp_all add: uspec_sercompwell_def)
      by (simp add: uspecIsConsistent_def)
  next
    case False
    have f00: "uspecIsConsistent ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
      using False by auto
    then show ?thesis 
      proof (cases "\<not> uspecIsConsistent (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)")
        case True
        then show ?thesis
          apply (simp_all add: uspec_sercompwell_def)
          by (simp add: RCV.rep_eq inv_rev_rev uspecIsConsistent_def)
      next
        case False
        have f01: "uspecIsConsistent (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using False by auto
        have f02: "uspecIsConsistent (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f00 snd3_medsr3_sercomp_well uspec_sercomp_consistent2 by auto
        have f02: "uspecIsConsistent (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f00 snd3_medsr3_sercomp_well uspec_sercomp_consistent2 by auto
        obtain f1 f2 where f1_f2_def: "f1 \<in> Rep_rev_uspec (SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
              \<and> f2 \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f00 snd3_medsr3_sercomp_well uspec_consist_f_ex uspec_sercomp_consistent2 by blast
        have f03: "ufSerComp f1 f2 \<in> Rep_rev_uspec ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          by (metis f1_f2_def snd3_medsr3_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
        obtain g where g_def: "g \<in> Rep_rev_uspec (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using False uspec_consist_f_ex by auto
        have g_eq_recv: "g = recvTSPF"
          by (simp add: g_def rcv_uspec_ele)
        have f04: "\<exists> ora. f2 = medSR_TSPF ora  \<and> #({True} \<ominus> ora)=\<infinity>"
          using f1_f2_def medsr_rev_insert by auto
        obtain ora where ora_def: "f2 = medSR_TSPF ora" and ora_def2: "#({True} \<ominus> ora)=\<infinity>"
          using f04 by auto
        obtain snd where snd_def: "f1 = senderTSPF snd"
        proof -
          assume a1: "\<And>snd. f1 = senderTSPF snd \<Longrightarrow> thesis"
          have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND"
            by (simp add: SND.rep_eq inv_rev_rev)
          then have "\<exists>c. f1 = senderTSPF c \<and> c \<in> tsSender"
            using f1_f2_def by blast
          then show ?thesis
            using a1 by blast
        qed
        have f05: "uspecDom ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
          = ufclDom\<cdot>(senderTSPF snd)"
          using f00 f1_f2_def local.snd_def snd3_medsr3_sercomp_well uspec_dom_eq uspec_sercomp_consistent2 uspec_sercomp_dom by blast
        have f06: "\<forall> f \<in> Rep_rev_uspec ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
            ufclDom\<cdot>f = ufclDom\<cdot>(senderTSPF snd)"
          by (simp add: f05 uspec_dom_eq)
        have f7: "(senderTSPF snd) \<in> Rep_rev_uspec (SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f1_f2_def local.snd_def by auto
        have f8: "(medSR_TSPF ora) \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f1_f2_def ora_def by auto
        have f09: "sercomp_well (senderTSPF snd) (medSR_TSPF ora)"
          by (meson snd3_medsr3_sercomp_well f7 f8 ufunclSerCompWell_ufun_def uspec_sercomp_h2)
        have f08: "sercomp_well (ufSerComp (senderTSPF snd) (medSR_TSPF ora)) g"
          apply (subst ufSerComp_ran) using f09 apply blast
          apply (subst ufSerComp_ran) using f09 apply blast
          apply (subst ufSerComp_dom) using f09 apply blast
          apply (simp only: g_eq_recv recv_tspfdom recv_tspfran sender_tspfdom sender_tspfran)
          apply (simp_all only:  ora_def2 c_dr_boolpair_ctype med_tspfran2)
          by blast
        then show ?thesis 
          apply (simp add: uspec_sercompwell_def)
          apply (simp add: ufunclSerCompWell_ufun_def)
          by (metis f03 g_def local.snd_def ora_def ufclDom_ufun_def ufclRan_ufun_def 
              uspec_dom_eq uspec_ran_eq)
      qed
    qed

lemma snd3_medsr3_rcv3_medrs3_id_sercomp_well: "uspec_sercompwell ((SND \<circle> MEDSR) \<circle> RCV) (MEDRS \<parallel> (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))"
  proof (cases "\<not> uspecIsConsistent ((SND \<circle> MEDSR) \<circle> (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))")
    case True
    then show ?thesis 
      by (simp add: uspecIsConsistent_def uspec_sercompwell_def)
  next
    case False
    have f00: "uspecIsConsistent ((SND \<circle> MEDSR) \<circle> (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))"
      using False by auto
    then show ?thesis 
    proof (cases "\<not> uspecIsConsistent (MEDRS \<parallel> (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))")
      case True
      then show ?thesis 
        by (simp add: uspecIsConsistent_def uspec_sercompwell_def)
    next
      case False
      have f01: "uspecIsConsistent (MEDRS \<parallel> (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))"
        using False by auto
      have f02: "uspecIsConsistent (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using False medrs3_id_parcomp_well uspec_parcomp_consistent2 by auto
      have f02: "uspecIsConsistent (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f00 snd3_medsr3_rev3_sercomp_well uspec_sercomp_consistent2 by auto
      have f03: "uspecIsConsistent (SND \<circle> (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))"
        using f00 snd3_medsr3_rev3_sercomp_well uspec_sercomp_consistent2 by auto
      have f04: "uspecIsConsistent (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f03 snd3_medsr3_sercomp_well uspec_sercomp_consistent2 by auto
      have f05: "uspecIsConsistent (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f03 snd3_medsr3_sercomp_well uspec_sercomp_consistent2 by blast
      obtain f1 where f1_def: "f1 \<in> Rep_rev_uspec (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f05 uspec_consist_f_ex by blast
      obtain f2 where f2_def: "f2 \<in> Rep_rev_uspec (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f04 uspec_consist_f_ex by auto
      obtain f3 where f3_def: "f3 \<in> Rep_rev_uspec (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f02 uspec_consist_f_ex by auto
      obtain f4 where f4_def: "f4 \<in> Rep_rev_uspec (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using False medrs3_id_parcomp_well uspec_consist_f_ex uspec_parcomp_consistent2 by blast
      obtain f5 where f5_def: "f5 \<in> Rep_rev_uspec (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        by (simp add: ID.rep_eq inv_rev_rev)
      
      obtain ora1 where ora1_def: "f2 = medSR_TSPF ora1" and ora1_def2: "#({True} \<ominus> ora1)=\<infinity>"
        using f2_def medsr_rev_insert by auto
      obtain ora2 where ora2_def: "f4 = medRS_TSPF ora2" and ora2_def2: "#({True} \<ominus> ora2)=\<infinity>"
        using f4_def medrs_rev_insert by auto
      obtain snd where snd_def: "f1 = senderTSPF snd"
      proof -
        assume a1: "\<And>snd. f1 = senderTSPF snd \<Longrightarrow> thesis"
        have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND"
          by (simp add: SND.rep_eq inv_rev_rev)
        then show ?thesis
          using a1 f1_def by moura
      qed
      have f10: "(senderTSPF snd) \<in> Rep_rev_uspec (SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f1_def local.snd_def by auto
      have f11: "(medSR_TSPF ora1) \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        apply (fold ora1_def)
        by (simp add: f2_def)
      have f12: "sercomp_well (senderTSPF snd) (medSR_TSPF ora1)"
        by (meson snd3_medsr3_sercomp_well f10 f11 ufunclSerCompWell_ufun_def uspec_sercomp_h2)
      have f13: "(ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
        by (metis f1_def f2_def local.snd_def ora1_def snd3_medsr3_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_h1)
      have f14: "sercomp_well (ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) f3"
        by (meson snd3_medsr3_rev3_sercomp_well f13 f3_def ufunclSerCompWell_ufun_def uspec_sercomp_h2)
      have f15: "ufSerComp (ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) f3 \<in>  
        Rep_rev_uspec ((SND \<circle> MEDSR) \<circle> RCV)"
        by (metis f13 f3_def snd3_medsr3_rev3_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
      have f16: "parcomp_well f4 f5"
        by (meson medrs3_id_parcomp_well f4_def f5_def ufunclParCompWell_ufun_def uspec_parcomp_h2)
      have f17: "ufParComp f4 f5 \<in> Rep_rev_uspec (MEDRS \<parallel> ID)"
        by (metis f4_def f5_def medrs3_id_parcomp_well ufunclParComp_ufun_def uspec_parcomp_h1)
      have f18: "f5 = idTSPF2"
        by (metis ID.rep_eq f5_def inv_rev_rev singletonD)
      have f19: "f3 = recvTSPF"
        by (simp add: f3_def rcv_uspec_ele)
      have f20: "sercomp_well (ufSerComp (ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) f3) (ufParComp f4 f5)"
        apply (subst ufSerComp_ran) using f14 apply blast
        apply (subst ufSerComp_ran) using f14 apply blast
        apply (subst ufSerComp_dom) using f14 apply blast
        apply (subst ufSerComp_dom) using f12 apply blast
        apply (subst ufParComp_ran) using f16 apply blast
        apply (subst ufParComp_dom) using f16 apply blast
        apply (subst ufParComp_dom) using f16 apply blast
         apply (simp add: f19 ora2_def f18)
        apply (rule)
         apply (metis ora2_def ora2_def2 ctype_MABP.simps(5) idTSPF2_dom insert_is_Un med_tspfdom2 ora2_def recv_tspfran)
        apply (simp only: sender_tspfdom)
        apply (subst med_tspfdom)
          apply (simp add:  med_ora_length ora2_def2, simp)
        apply (subst med_tspfran)
          apply (simp add:  med_ora_length ora2_def2, simp)
        apply (simp only: recv_tspfran idTSPF2_ran idTSPF2_dom)
        by blast
      then show ?thesis 
        apply (simp add: uspec_sercompwell_def)
        apply (simp add: ufunclSerCompWell_ufun_def)
        by (metis f15 f17 ufclDom_ufun_def ufclRan_ufun_def uspec_dom_eq uspec_ran_eq)
    qed
  qed

lemma abpcomp_f_ex: assumes "f \<in> Rep_rev_uspec speccompABP" 
  shows "\<exists> s. \<exists>ora1 ora2. s \<in> tsSender \<and> #({True} \<ominus> ora1)=\<infinity> \<and>  #({True} \<ominus> ora2)=\<infinity> \<and>
    (f =  (ufunclFeedbackComp (ufunclSerComp (ufunclSerComp (ufunclSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
          (ufunclParComp (medRS_TSPF ora2) idTSPF2))))"
proof -
  have f1: "uspec_parcompwell MEDRS (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: medrs3_id_parcomp_well)
  have f2: "uspec_sercompwell SND (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: snd3_medsr3_sercomp_well)
  have f20: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)) \<and> f2\<in>(Rep_rev_uspec MEDSR)}"
    by (simp add: f2)
  have f21: "uspecSerComp SND MEDSR = Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec SND) \<and> f2\<in>(Rep_rev_uspec MEDSR)}"
    by (simp add: uspecSerComp_def)
  have f3: "uspec_sercompwell (SND \<circle> MEDSR) (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: snd3_medsr3_rev3_sercomp_well)
  have f30: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND \<circle> MEDSR)) \<and> f2\<in>(Rep_rev_uspec (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))}"
    by (simp add: f3)
  have f31: "uspecSerComp (SND \<circle> MEDSR) RCV = 
      Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND \<circle> MEDSR)) \<and> f2\<in>(Rep_rev_uspec RCV)}"
    using uspecSerComp_def by blast
  have f40: "uspecWell {ufunclParComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec MEDRS) \<and> f2\<in>(Rep_rev_uspec (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))}"
    by (simp add: f1)
  have f31: "uspecParComp MEDRS ID = 
      Abs_rev_uspec {ufunclParComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec MEDRS) \<and> f2\<in>(Rep_rev_uspec ID)}"
    using uspecParComp_def by blast
  have f51: "uspecSerComp ((SND \<circle> MEDSR) \<circle> RCV) (MEDRS \<parallel> ID) = 
      Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec ((SND \<circle> MEDSR) \<circle> RCV)) 
      \<and> f2\<in>(Rep_rev_uspec (MEDRS \<parallel> ID))}"
    using uspecSerComp_def by blast
  have f60: "uspecWell {(\<mu>) f1 |f1::('a MABP tstream\<^sup>\<Omega>) ufun. f1 \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV \<circle> (MEDRS \<parallel> ABP_TSPS.ID))}"
    by (simp add: uspec_feedbackcomp_well)
  have f61: "uspecFeedbackComp(((SND \<circle> MEDSR) \<circle> RCV) \<circle> (MEDRS \<parallel> ID)) =
    Abs_rev_uspec {(\<mu>) f1 |f1::('a MABP tstream\<^sup>\<Omega>) ufun. f1 \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV \<circle> (MEDRS \<parallel> ABP_TSPS.ID))}"
    by (simp add: uspecFeedbackComp_def)                                                            
  have f70: "f \<in> {(\<mu>) f1 |f1::('a MABP tstream\<^sup>\<Omega>) ufun. f1 \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV \<circle> (MEDRS \<parallel> ABP_TSPS.ID))}"
    by (metis (no_types, lifting) assms f60 f61 rep_abs_rev_simp)
  have f71: "uspecIsConsistent (speccompABP::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    apply (simp add: uspecIsConsistent_def uspecFeedbackComp_def)
    apply (subst rep_abs_rev_simp, simp add: uspec_feedbackcomp_well)
    using f70 by blast
  have f80: "uspecIsConsistent (((SND \<circle> MEDSR \<circle> RCV)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<circle> (MEDRS \<parallel> ABP_TSPS.ID))"
    using f71 uspec_feedbackcomp_consistent_iff by auto
  have f90: "uspecIsConsistent ((SND \<circle> MEDSR \<circle> RCV)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        \<and> uspecIsConsistent ((MEDRS \<parallel> ABP_TSPS.ID)::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    using f51 f80 uspec_sercomp_consistent2 by blast
  have f91: "uspecIsConsistent (MEDRS:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec) 
        \<and> uspecIsConsistent (ID:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f31 f1 uspec_parcomp_consistent2 f90 by blast
  have f92: "uspecIsConsistent ((SND \<circle> MEDSR)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        \<and> uspecIsConsistent (RCV:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f31 f3 uspec_sercomp_consistent2 f90 by blast
  have f93: "uspecIsConsistent (SND:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec) 
        \<and> uspecIsConsistent (MEDSR:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f2 f92 uspec_sercomp_consistent2 by blast
  obtain f1 where f1_def: "f = ufFeedbackComp f1 \<and> f1 \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV \<circle> (MEDRS \<parallel> ABP_TSPS.ID))"
    by (metis assms ufunclFeedbackComp_ufun_def uspec_feedbackcomp_f_ex)
  obtain f2 f3 where f2_f3_def: "f1 = ufSerComp f2 f3 \<and> f2 \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV) 
      \<and> f3 \<in> Rep_rev_uspec (MEDRS \<parallel> ABP_TSPS.ID)"
    by (metis f1_def f80 snd3_medsr3_rcv3_medrs3_id_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_ele_ex)
  obtain f4 f5 where f4_f5_def: "f2 = ufSerComp f4 f5 \<and> f4 \<in> Rep_rev_uspec (SND \<circle> MEDSR) 
      \<and> f5 \<in> Rep_rev_uspec RCV"  
    by (metis f2_f3_def f3 f90 ufunclSerComp_ufun_def uspec_sercomp_ele_ex)
  obtain f6 f7 where f6_f7_def: "f3 = ufParComp f6 f7 \<and> f6 \<in> Rep_rev_uspec MEDRS
      \<and> f7 \<in> Rep_rev_uspec ID"
    by (metis f1 f2_f3_def ufunclParComp_ufun_def uspec_parcomp_ele_ex)
  have f101: " f4 \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
    by (simp add: f4_f5_def)
  have f102: "SND \<circle> (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
    = Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2. f1 \<in> Rep_rev_uspec SND \<and> f2 \<in> Rep_rev_uspec MEDSR}"
    by (simp add: f21)
  obtain f8 f9 where f8_f9_def: "f4 = ufSerComp f8 f9 \<and> f8 \<in> Rep_rev_uspec SND 
      \<and> f9 \<in> Rep_rev_uspec MEDSR"
    by (metis f2 f4_f5_def f92 ufunclSerComp_ufun_def uspec_sercomp_ele_ex)
  obtain snd where snd_def: "f8 = senderTSPF snd \<and> snd \<in> tsSender"
  proof -
    assume a1: "\<And>snd. f8 = senderTSPF snd \<and> snd \<in> tsSender \<Longrightarrow> thesis"
    have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND"
      by (simp add: SND.rep_eq inv_rev_rev)
    then show ?thesis
      using a1 f8_f9_def by blast
  qed
  have f200: "\<exists>ora::bool stream. f9 = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity>"
    using f8_f9_def medsr_rev_insert by blast
  have f201: "\<exists>ora::bool stream. f6 = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity>"
    using f6_f7_def medrs_rev_insert by blast
  obtain ora1 where ora1_def: "f9 = medSR_TSPF ora1 \<and> #({True} \<ominus> ora1) = \<infinity>"
    using f200 by auto
  obtain ora2 where ora2_def: "f6 = medRS_TSPF ora2 \<and> #({True} \<ominus> ora2) = \<infinity>"
    using f201 by auto
  have f202: "f5 = recvTSPF"
    by (metis RCV.rep_eq f4_f5_def inv_rev_rev singletonD)
  have f203: "f7 = idTSPF2"
    by (simp add: f6_f7_def id_uspec_ele)
  have f204: "f9 = medSR_TSPF ora1"
    by (simp add: ora1_def)
  have f205: "f6 = medRS_TSPF ora2"
    by (simp add: ora2_def)
  have f206: "f8 = senderTSPF snd"
    by (simp add: snd_def)
  show ?thesis
    apply (rule_tac x="snd" in exI)
    apply (rule_tac x="ora1" in exI)
    apply (rule_tac x="ora2" in exI)
    apply (rule, simp add: local.snd_def)
    apply (simp add: ora1_def ora2_def)
    apply (fold f202)
    apply (fold f203)
    apply (fold f204)
    apply (fold f205)
    apply (fold f206)
    by (simp add: f1_def f2_f3_def f4_f5_def f6_f7_def f8_f9_def ufunclFeedbackComp_ufun_def ufunclParComp_ufun_def ufunclSerComp_ufun_def)
qed

(*=========================================================================================================================================================*)


lemma abp_speccomp_final: assumes "f \<in> Rep_rev_uspec speccompABP"
                            and "ubDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
proof - 
  have f1: "\<exists> s. \<exists>ora1 ora2. s \<in> tsSender  \<and> (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
          (ufParComp (medRS_TSPF ora2) idTSPF2))))"
    by (metis abpcomp_f_ex ufunclFeedbackComp_ufun_def ufunclSerComp_ufun_def ufunclParComp_ufun_def assms(1)) 
  then obtain s where f12: "(s \<in> tsSender) \<and> (\<exists> ora1 ora2. (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF2)))))"
    using f1 by blast
  then obtain ora1  where f13: "(#({True} \<ominus> ora1) = \<infinity>) \<and> (\<exists> ora2. (#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF2)))))"
    using f1 by blast
  then obtain ora2  where f14: "(#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF2))))"
    using f1 by blast
  then have f15: "(f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF2))))"
    using f1 by blast

(*===============================================================================================*)
  have f100: "medRS_TSPF ora2 \<in> Rep_rev_uspec (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    using f14 medrs_rev_insert by blast
  have f101: "idTSPF2 \<in> Rep_rev_uspec (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: ID.rep_eq inv_rev_rev)
  have f102: "recvTSPF \<in> Rep_rev_uspec (RCV::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: RCV.rep_eq inv_rev_rev)
  have f103: "(medSR_TSPF ora1) \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    using f13 medsr_rev_insert by blast
  have f104: "(senderTSPF s) \<in> Rep_rev_uspec (SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  proof -
    have "\<exists>c. senderTSPF s = senderTSPF c \<and> c \<in> tsSender"
      using f12 by blast
    then show ?thesis
      by (simp add: SND.rep_eq inv_rev_rev)
  qed

  have f110: "sercomp_well (senderTSPF s) (medSR_TSPF ora1)"
    by (simp add: f13 med_tspfdom2 med_tspfran2 sender_tspfdom sender_tspfran)

  have f20: "ufDom\<cdot>(innerABP s ora1 ora2) = {c_abpIn, c_as}"
    apply (subst ufSerComp_dom) defer
     apply (subst ufSerComp_dom) defer
      apply (subst ufSerComp_dom) defer
       apply (simp add: insert_commute sender_tspfdom) defer defer
    using f110 apply blast
     apply (subst ufSerComp_dom)
     apply (subst ufSerComp_dom)
    using f110 apply blast
     apply (simp add: ufSerComp_ran f13 med_tspfdom2 med_tspfran2 sender_tspfdom sender_tspfran) +
    apply (simp add: recv_tspfdom recv_tspfran)
    apply (subst ufSerComp_ran)
     apply (subst ufSerComp_ran)
    using f110 apply blast
     apply (subst ufSerComp_dom)
    using f110 apply blast
     apply (subst ufSerComp_ran)
    using f110 apply blast
     apply (simp add: ufSerComp_ran f13 med_tspfdom2 med_tspfran2 sender_tspfdom sender_tspfran) +
     apply (simp add: recv_tspfdom recv_tspfran)
     apply (subst ufParComp_dom)
     apply (simp_all add: ufCompL_def f14 med_tspfdom2 med_tspfran2 idTSPF2_ran idTSPF2_dom)
    apply (simp add: recv_tspfdom recv_tspfran)
     apply (subst ufSerComp_dom)
    using f110 apply blast
     apply (subst ufSerComp_ran)
     apply (subst ufSerComp_ran)
    using f110 apply blast
     apply (subst ufSerComp_ran)
    using f110 apply blast
     apply (subst ufSerComp_dom)
    using f110 apply blast
     apply (simp add: ufSerComp_ran f13 med_tspfdom2 med_tspfran2 sender_tspfdom sender_tspfran) +
    apply (simp add: recv_tspfdom recv_tspfran)
     apply (subst ufParComp_dom)
     apply (simp_all add: ufCompL_def f14 med_tspfdom2 med_tspfran2 idTSPF2_ran idTSPF2_dom)
     apply (subst ufParComp_ran)
     apply (simp_all add: ufCompL_def f14 med_tspfdom2 med_tspfran2 idTSPF2_ran idTSPF2_dom)
     apply (subst ufParComp_ran)
     apply (simp_all add: ufCompL_def f14 med_tspfdom2 med_tspfran2 idTSPF2_ran idTSPF2_dom)
    apply (simp add: sender_tspfdom)
    apply (simp add: recv_tspfdom recv_tspfran)
    by blast
  have f21: "ufRan\<cdot>(innerABP s ora1 ora2) = {c_idOut, c_as}"
    apply (simp add: ufran_least)
    apply (simp add: f20)
    apply (simp add: ubclDom_ubundle_def)
    sorry
                                      
  have f2: "(f \<rightleftharpoons> tb) . c_idOut =  (ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_ar})  .  c_idOut"
    apply(subst f15)
    apply(simp add: ufFeedbackComp_def)
    apply(simp add: ufFeedbackComp_cont ufFeedbackComp_well)
    apply(simp add: f20 f21 assms ubclDom_ubundle_def)
    sorry (* smt found *)

  have f105: "(ufSerComp (senderTSPF s) (medSR_TSPF ora1)) 
    \<in> Rep_rev_uspec ((SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<circle> MEDSR)"
    by (metis f103 f104 snd3_medsr3_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_h1)
  have f106: "(ufParComp (medRS_TSPF ora2) idTSPF2) \<in>
                         Rep_rev_uspec ((MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<parallel> ID)"
    apply (simp add: uspecParComp_def)
    apply (subst rep_abs_uspec)
     apply (simp add: medrs3_id_parcomp_well)
    apply (simp add: inv_rev_rev)
    by (metis f100 f101 ufunclParComp_ufun_def)
  have f107: "(ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) \<in>
    Rep_rev_uspec (((SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<circle> MEDSR) \<circle> RCV)"
    by (metis f102 f105 snd3_medsr3_rev3_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
  have f110: "parcomp_well (medRS_TSPF ora2) (idTSPF2::('a MABP tstream\<^sup>\<Omega>) ufun)"
    apply (fold ufunclParCompWell_ufun_eq)
    using f100 f101 medrs3_id_parcomp_well uspec_parcomp_h2 by blast
  have f111: "sercomp_well (senderTSPF s) (medSR_TSPF ora1)"
    apply (fold ufunclSerCompWell_ufun_eq)
    using f103 f104 snd3_medsr3_sercomp_well uspec_sercompwell_def by blast
  have f112: "sercomp_well (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF"
    apply (fold ufunclSerCompWell_ufun_eq)
    using f102 f105 snd3_medsr3_rev3_sercomp_well uspec_sercompwell_def by blast
  have f113: "sercomp_well (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF2)"
    apply (fold ufunclSerCompWell_ufun_eq)
    using f106 f107 snd3_medsr3_rcv3_medrs3_id_sercomp_well uspec_sercompwell_def by blast
  have f98: "ufDom\<cdot>(innerABP s ora1 ora2) = ufDom\<cdot>(senderTSPF s)"
    by (metis f111 f112 f113 ufSerComp_dom)

  have f99: "\<And>x. dom (ABPBundleHelper s ora1 ora2 tb x)  = {c_ds, c_dr, c_ar, c_idOut, c_as, c_abpOut}"
    by auto
  have f100: "\<And>x. ubWell (ABPBundleHelper s ora1 ora2 tb x)"
    apply(simp add: ubWell_def)
    apply(simp add: usclOkay_tstream_def)
    by (simp_all add: tsmap_tsdom_range)
  have f101: "ubWell (ABPBundleHelper s ora1 ora2 tb x)"
    apply (simp add: ubWell_def)
    apply(simp add: usclOkay_tstream_def)
    by (simp_all add: tsmap_tsdom_range)
  have f199: "\<And> Y. chain Y \<Longrightarrow> chain (\<lambda> i. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))"
    apply (rule chainI)
    apply (rule ub_below)
     apply (simp add: f100 ubdom_ubrep_eq)
    apply (simp add: ubdom_insert f100)
    apply (simp add: ubgetch_ubrep_eq f100)
    apply (rule) + apply (simp)
     apply (simp add: monofun_cfun_arg po_class.chainE)
    apply (rule) + apply (simp)
     apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE)
    apply (rule) + apply (simp)
     apply (simp add: cont_pref_eq1I fst_monofun po_class.chainE)
    apply (rule) + apply (simp)
     apply (simp add: monofun_cfun_arg po_class.chainE snd_monofun)
    apply (rule) + apply (simp)
     apply (simp add: cont_pref_eq1I monofun_cfun_fun po_class.chainE)
    apply (rule) + apply (simp)
    by (simp add: monofun_cfun_arg po_class.chainE)

  have f2001: "ubDom\<cdot>(fixABPHelper s ora1 ora2 tb x) = {c_ds, c_dr, c_ar, c_idOut, c_abpOut, c_as}"
    apply (subst ubdom_ubrep_eq)
    using abpHelper_ubWell apply blast
    apply (simp add: domIff)
    by blast

  have f200: "cont (fixABPHelper s ora1 ora2 tb)"
    apply (rule contI2)
     apply (rule monofunI)
     apply (rule ub_below)
      apply (subst ubdom_ubrep_eq)
    using abpHelper_ubWell apply blast
      apply (subst ubdom_ubrep_eq)
    using abpHelper_ubWell apply blast
      apply simp 
    apply (subst ubgetch_ubrep_eq)
    using abpHelper_ubWell apply blast
    apply (subst ubgetch_ubrep_eq)
    using abpHelper_ubWell apply blast
     apply (simp add: ubgetch_ubrep_eq)
     apply (rule) + apply (simp)
      apply (simp add: monofun_cfun_arg)
     apply (rule) + apply (simp)
      apply (simp add: monofun_cfun_arg monofun_cfun_fun)
     apply (rule) + apply (simp)
      apply (simp add: cont_pref_eq1I fst_monofun)
     apply (rule) + apply (simp)
      apply (simp add: cont_pref_eq1I snd_monofun)
     apply (rule) + apply (simp)
     apply (simp add: monofun_cfun_arg monofun_cfun_fun)
     apply (rule) + apply (simp)
    apply (simp add: monofun_cfun_arg po_class.chainE)
    apply (rule, rule)
  proof -
    fix Y :: "nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
    assume a1: "chain Y"
    have f0:  "(\<Squnion>n. tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y n . c_dr))) = tsRec\<cdot>(tsMap invBoolPair\<cdot>(Lub Y . c_dr))"
      by (simp add: a1 contlub_cfun_arg)
    have f1: "ubDom\<cdot>(Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (\<Squnion>i::nat. Y i))) = ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))"
    proof -
      have "\<And>f n. ubDom\<cdot>(Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (f (n::nat)))) = {c_ds, c_dr, c_ar, c_idOut, c_abpOut, c_as}"
        by (metis f100 f2001 f99 ubdom_ubrep_eq)
      then have "\<And>f. \<not> chain (\<lambda>n. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (f n))) \<or> ubDom\<cdot> (\<Squnion>n. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (f n))) = {c_ds, c_dr, c_ar, c_idOut, c_abpOut, c_as}"
        using ubdom_chain_eq2 by blast
      then have "ubWell (ABPBundleHelper s ora1 ora2 tb (Lub Y)) \<and> ubDom\<cdot> (\<Squnion>n. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y n))) = {c_ds, c_dr, c_ar, c_idOut, c_abpOut, c_as}"
        using a1 f100 f199 by presburger
      then show ?thesis
        using f99 ubdom_ubrep_eq by fastforce
    qed
    have f2: "\<And> c. (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))  .  c = 
          (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)) .  c)"
      using a1 contlub_cfun_arg f199 by auto
    have f3: "chain (\<lambda> i. tsMap invBool\<cdot>((Y i)  .  c_as))"
      by (simp add: a1)
    have f4: "chain (\<lambda> i. s\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((Y i) .  c_as)))"
      using f3 by auto
    have f5: "chain (\<lambda> i. tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((Y i) .  c_as))))"
      apply (rule chainI)
      using f4 monofun_cfun_arg po_class.chainE by blast
    have f7: "tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_as))) = 
        (\<Squnion>i::nat. tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((Y i) .  c_as))))"
      by (simp add: a1 contlub_cfun_arg)
    show "Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))"
      apply (rule ub_below)
      using f1 apply blast
      apply (unfold f2)
      apply (simp add: ubgetch_ubrep_eq f100)
      apply (simp add: f100 ubdom_ubrep_eq)
      apply (rule) + apply (simp)
       apply (simp add: a1 contlub_cfun_arg)
      apply (rule) + apply (simp)
       apply (simp add: a1 contlub_cfun_arg)
       apply (subst contlub_cfun_fun)
        apply (rule chainI)
        apply (simp add: a1 monofun_cfun_arg po_class.chainE)
       apply (subst contlub_cfun_arg)
      apply (rule chainI)
        apply (simp add: a1 monofun_cfun_arg monofun_cfun_fun po_class.chainE, simp)
      apply (rule) + apply (simp)
      apply (simp add: a1 f0 recvCH1_contlub to_recvch1)
      apply (rule) + apply (simp)
       apply (simp add: a1 f0 recvCH2_contlub to_recvch2)
      apply (rule) + apply (simp)
       apply (simp add: a1 medh_contlub to_medh)
      apply (rule) + apply (simp)
      by (simp add: a1 contlub_cfun_arg)
  qed
 
  have f300: "(\<Squnion>i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_ar} tb)  .  c_abpOut =
    (\<Squnion>i::nat. iterate i\<cdot>((ufFeedH (innerABP s ora1 ora2)) tb)\<cdot>(ubclLeast {c_idOut, c_ar}))  .  c_abpOut "
    by simp

  have f400: "ufRan\<cdot>(innerABP s ora1 ora2) = {c_as, c_idOut}"
    by (simp add: f21 insert_commute)

  have f310: "iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) 0 {c_idOut, c_ar} tb =
             (ubclLeast {c_idOut, c_ar})"
    by simp

  have f500: "ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut} =
           (\<Squnion>i. iterate i\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) "
    using ubFix_def by force

  have f501: "iterate 0\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) = 
    (ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
    by simp
  have f502: "iterate (Suc 0)\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) = 
    Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>((ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>((ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_dr)))),
    c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>((ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>((ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_abpOut))
    ]"
    apply (simp add: f200 f100)
    apply (rule ub_eq)
     apply (simp add: f100 ubdom_ubrep_eq)
     apply (subst ubdom_ubrep_eq)
      apply(simp add: ubWell_def)
      apply(simp add: usclOkay_tstream_def)
      apply (simp_all add: tsmap_tsdom_range)
    apply (simp add: f99 f100 ubdom_ubrep_eq)
    apply auto
         apply (simp add: f100 ubgetch_ubrep_eq)
    apply (subst ubgetch_ubrep_eq)
      apply(simp add: ubWell_def)
      apply(simp add: usclOkay_tstream_def)
      apply (simp_all add: tsmap_tsdom_range)
         apply (simp add: f100 ubgetch_ubrep_eq)
    apply (subst ubgetch_ubrep_eq)
      apply(simp add: ubWell_def)
      apply(simp add: usclOkay_tstream_def)
         apply (simp_all add: tsmap_tsdom_range)
    apply (simp add: ubclLeast_ubundle_def)
         apply (simp add: f100 ubgetch_ubrep_eq)
    apply (subst ubgetch_ubrep_eq)
      apply(simp add: ubWell_def)
      apply(simp add: usclOkay_tstream_def)
         apply (simp_all add: tsmap_tsdom_range)
    apply (simp add: ubclLeast_ubundle_def)
         apply (simp add: f100 ubgetch_ubrep_eq)
    apply (subst ubgetch_ubrep_eq)
      apply(simp add: ubWell_def)
      apply(simp add: usclOkay_tstream_def)
         apply (simp_all add: tsmap_tsdom_range)
    by (simp add: ubclLeast_ubundle_def)
  
(*===============================================================================================*)


  have f3: "(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_abpOut, c_ar})  .  c_abpOut = 
            (ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})  .  c_abpOut"
    sorry

  have f40: "ubfun_io_eq (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds}"
    sorry
  then have f41: "ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds} =  (fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})"
    using ubfix_eq by blast

  have f42: "\<And>x. ubWell [
      c_ds     \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
      c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
      c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
      c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
      c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2)
      ]"
    using abpHelper_ubWell by blast
  (* After proving the fixed points propties we can now show the assumptions of the tsaltbitpro_inp2out lemma
  
    i = (tsMap invData\<cdot>(tb . c_abpIn))
    ds_stream = (tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))
    as_stream = (tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))

  *)

  (* Result *)
  have f8: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_dr)))) = tsAbs\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))"
    
    sorry
  have f9: "tsAbs\<cdot>(tsMap Data\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_dr))))) = tsAbs\<cdot>(tb . c_abpIn)"
  proof - 
    have f90: "\<And>s. invData (Data s) = s"
      by simp
    have f91: "tsDom\<cdot>(tb . c_abpIn) \<subseteq> range Data"
      by (metis assms(2) ctype_MABP.simps(1) insert_iff ubdom_channel_usokay ubgetch_insert usclOkay_tstream_def)
    then have f92: "\<exists>s. tb . c_abpIn = tsMap Data\<cdot>s"
      sorry
    show ?thesis
      using f8 
      sorry
  qed
  show ?thesis
  proof - 
    have f90: "cont ( fixABPHelper s ora1 ora2 tb)"
      apply(subst abpHelper_cont, simp_all add: assms)
      by(simp_all add: f12 f13 f14)
    have f91: "(abpFix s ora1 ora2 tb) . c_abpOut =
                tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(abpFix s ora1 ora2 tb . c_dr))))"
      apply(subst f41)
      apply(simp add: f90)
      apply(simp add: ubGetCh_def)
      apply(subst ubrep_ubabs)
      apply (metis (no_types, lifting) f42 ubgetch_insert)   
       by simp   
    have f92: "\<And>x. (snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>x))) = (tsProjFst\<cdot>(tsRemDups\<cdot>(tsMap invBoolPair\<cdot>x)))"
      by(simp add: tsRec_def tsRecSnd_def)
    show ?thesis
      apply(subst f2)
      apply(subst f3)
      apply(subst f91)
      apply(subst f92)
      apply(subst f9)
      by simp
  qed
qed



(*
(* ----------------------------------------------------------------------- *)
section \<open>Testing of Composition without Medium\<close>
(* ----------------------------------------------------------------------- *)

definition senderTSPF2 :: "'a sender \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun" where
"senderTSPF2 se \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"

lemma sender_mono: assumes "se \<in> tsSender" shows "monofun (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"
  sorry

lemma sender_cont: assumes "se \<in> tsSender" shows "cont (\<lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"
  sorry

lemma sender_well: assumes "se \<in> tsSender" shows "ufWell (\<Lambda> x. (ubDom\<cdot>x = {c_ar, c_abpIn})
                \<leadsto> Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(x . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar)))])"
  sorry

lift_definition SND2 :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {senderTSPF2 s | s. s \<in> tsSender}"
  sorry

definition recvTSPF2 :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"recvTSPF2 \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"

lemma recv_mono: "monofun (\<lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"
  sorry

lemma recv_cont: "cont (\<lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"
  sorry

lemma recv_well: "ufWell (\<Lambda> x. (ubDom\<cdot>x = {c_dr}) \<leadsto> Abs_ubundle [c_ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                        c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))])"
  sorry

lift_definition RCV2 :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" is
"Rev {recvTSPF2}"
  sorry

abbreviation speccompABP_nmed :: "(('a MABP tstream\<^sup>\<Omega>) ufun) uspec" where
"speccompABP_nmed \<equiv> uspecFeedbackComp(SND \<circle> RCV)"


lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "ds_stream = send\<cdot>i\<cdot>as_stream"
    and as_def: "as_stream = tsProjSnd\<cdot>ds_stream"
    and i_inf: "#\<surd>i = \<infinity>"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds_stream) = tsAbs\<cdot>i"
  using as_def ds_def send_def tsaltbitpro_inp2out_nmed by auto

lemma h1: assumes "s \<in> tsSender" shows "UFun.ufDom\<cdot>(ufunclSerComp (senderTSPF2 s) recvTSPF2) = {c_abpIn, c_ar}"
  apply (simp add: ufdom_insert ubclDom_ubundle_def)
  sorry                                                              

lemma h2: assumes "s \<in> tsSender" shows "UFun.ufRan\<cdot>(ufunclSerComp (senderTSPF2 s) recvTSPF2) = {c_abpOut, c_ar}"
  sorry

abbreviation abpFixH :: "('a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream) \<Rightarrow>  'a MABP tstream ubundle \<Rightarrow> 'a MABP tstream ubundle \<rightarrow> 'a MABP tstream ubundle" where
"abpFixH s tb \<equiv> (\<Lambda> x. Abs_ubundle[c_dr \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar))),
                                    c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                    c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))
                                   ])"

lemma abp_speccomp: assumes "f \<in> Rep_rev_uspec speccompABP_nmed"
                            and "ubDom\<cdot>tb = {c_abpIn}"
                          shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
proof - 
  have f1: "\<exists> s \<in> tsSender. (f = (\<mu>(ufunclSerComp (senderTSPF2 s) recvTSPF2)))"
    apply (simp add: ufunclSerComp_ufun_def)
    (* Cannot be proven until Instatiation *)
    sorry
  then obtain s where f12: "s \<in> tsSender \<and> (f = (\<mu>(ufunclSerComp (senderTSPF2 s) recvTSPF2)))"
    by blast
  then have f13: "f = (\<mu>(ufunclSerComp (senderTSPF2 s) recvTSPF2))"
    by blast
  have f14: "s \<in> tsSender"
    using f12 by blast


  have f20: "ubclDom\<cdot>tb = {c_abpIn, c_ar} - {c_ar}"
    apply(simp add: ubclDom_ubundle_def)
    using assms by blast                    
  have f2: "(f \<rightleftharpoons> tb) . c_abpOut =  ubFix (ufFeedH (ufunclSerComp (senderTSPF2 s) recvTSPF2) tb) {c_abpOut, c_ar}  .  c_abpOut"
    apply(subst f13)
    apply(simp add: ufFeedbackComp_def)
    apply(simp add: ufFeedbackComp_cont ufFeedbackComp_well)
    apply(simp add: f12 h1 h2)
    by(simp add: f20)


  have f3: "cont (\<lambda> x. Abs_ubundle[c_dr \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_ar))),
                                    c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
                                    c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))
                                   ])"
    sorry
  have f4: "ubFix (ufFeedH (ufunclSerComp (senderTSPF2 s) recvTSPF2) tb) {c_abpOut, c_ar}  .  c_abpOut
          = ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr} . c_abpOut"
    (* Should be possible to prove with equality of lubs *)
    sorry
  have f5: "ubfun_io_eq (abpFixH s tb) {c_abpOut, c_ar, c_dr}"
    sorry
  then have f6: "ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr} =  (abpFixH s tb)\<cdot>(ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr})"
    using ubfix_eq by blast


  (* After proving the fixed points propties we can now show the assumptions of the tsaltbitpro_inp2out_nmed lemma *)
  (*
    i = (tsMap invData\<cdot>(tb . c_abpIn))
    ds_stream = (tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))
    as_stream = (tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))

  *)
  have f7: "(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr)) = s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))"
    sorry

  have f8: "(tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar)) = tsProjSnd\<cdot>(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))"
    sorry

  (* More assms are necessary for this subgoal*)
  have f9: "#\<surd>(tsMap invData\<cdot>(tb . c_abpIn)) = \<infinity>"
    sorry

  (* Result of tsaltbitpro_inp2out_nmed lemma *)
  have f10: "tsAbs\<cdot>(tsRecSnd\<cdot>(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))) = tsAbs\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))"
    using f7 f8 f9 f14 by(simp add: tsaltbitpro_inp2out_nmed)
  
  

  
  show ?thesis
      sorry  
qed




*)
(*
(* ----------------------------------------------------------------------- *)
section \<open>More Lemmas\<close>
(* ----------------------------------------------------------------------- *)
*)
(*
lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and ds_def: "c_ds = send\<cdot>i\<cdot>c_as"
    and as_def: "c_as = tsProjSnd\<cdot>c_ds"
    and i_inf: "#\<surd>i = \<infinity>"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>c_ds) = tsAbs\<cdot>i"
  sorry    

lemma tsaltbitpro_inp2out:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "c_ds = send\<cdot>i\<cdot>c_as"
    and dr_def: "c_dr = tsMed\<cdot>c_ds\<cdot>p1"
    and ar_def: "c_ar = tsProjSnd\<cdot>c_dr"
    (* definition 5 *)
    and as_def: "c_as = tsMed\<cdot>c_ar\<cdot>p2"
    and i_ninf: "#(tsAbs\<cdot>i) \<noteq> \<infinity>"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>c_dr)) = tsAbs\<cdot>i"
  sorry



lemma abp_gencomp_final: assumes "f \<in> Rep_rev_uspec gencompABP"
                            and "ubDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
  oops  

*)

(*
  subsection \<open>medium_rs\<close>

(*

definition tsMedRSTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedRSTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {c_ar})
                           \<leadsto> [c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]\<Omega>)"

abbreviation tsMedRSAbb  :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP TSB option" where
"tsMedRSAbb bst x \<equiv> ((tsbDom\<cdot>x = {c_ar})
                           \<leadsto> [c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]\<Omega>)"

*)
subsubsection \<open>defs\<close>

definition medRSH :: "bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream"  where
"medRSH bst \<equiv> (\<lambda> x. (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst))"

lemma medrsh_cont [simp]: "cont (medRSH bst)"
  by (simp add: medRSH_def)

lemma medrsh_contlub: assumes "chain Y"
  shows "(medRSH bst) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medRSH bst) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medrsh: "tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst)
                  = ((medRSH :: bool stream \<Rightarrow> 'a MABP tstream\<^sup>\<Omega> \<Rightarrow> 'a MABP tstream) bst) x"
  by (simp add: medRSH_def)

subsubsection \<open>pre\<close>

lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast


lemma medrs_tsb_well [simp]: "ubWell  [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]"
  apply (rule ubwellI)
  apply (simp add: usclOkay_tstream_def)
  by (simp add: tsmap_tsdom_range)

lemma medrs_tsb_dom: "ubclDom\<cdot>(Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)])) = {c_as}"
  apply (simp add: ubclDom_ubundle_def)
  by (simp add: ubdom_ubrep_eq)


subsubsection \<open>cont\<close>

  (* prerequirement for the mono proofs of the tspf *)
lemma medrs_tsb_mono: "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubclDom\<cdot>x = {c_ar} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst)]) \<sqsubseteq> Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(y  .  c_ar))\<cdot>bst)])"
  apply (simp_all add: ubclDom_ubundle_def)
  apply (rule ub_below)
  apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq)
  apply (simp add: to_medrsh)
  using cont2mono medrsh_cont monofun_def by blast


lemma medrs_mono [simp]: "monofun (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
  apply (rule ufun_monoI2)
  by (simp add: medrs_tsb_mono)

lemma medrs_tsb_getc: assumes "chain (Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>)" and "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar}"
                      and "c = c_as"
  shows "(\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))  .  c_as
          =  (\<Squnion>i::nat. (Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)])) . c_as)"
proof (rule lubgetCh)
  have f2: "\<And> i. ubclDom\<cdot>(Y i) =  ubclDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1) ubclDom_ubundle_def)
  show tb_chain: "chain (\<lambda>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
    by (simp add: assms(1) assms(2) f2 medrs_tsb_mono po_class.chainE po_class.chainI)
  show "c_as \<in> ubclDom\<cdot>(\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
    by (metis (mono_tags, lifting) insert_iff medrs_tsb_dom tb_chain ubclDom_ubundle_def ubdom_chain_eq2)
qed



lemma medrs_cont [simp]: "cont (\<lambda> x::'a MABP tstream\<^sup>\<Omega>. (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
proof (rule ufun_contI)
  show medrs_mo : "\<And>(x::'a MABP tstream\<^sup>\<Omega>) y::'a MABP tstream\<^sup>\<Omega>.
       ubclDom\<cdot>x = {c_ar} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  c_ar))\<cdot>bst)] 
          \<sqsubseteq> Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(y  .  c_ar))\<cdot>bst)]"
    by (simp add: medrs_tsb_well monofun_cfun_arg monofun_cfun_fun option.distinct(1) option.sel ub_below ubdom_ubrep_eq ubgetch_ubrep_eq)

  have f1: " \<And>Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar} \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)])) = {c_as}"
    by (metis (mono_tags, lifting) medrs_tsb_dom medrs_tsb_mono po_class.chain_def ubcldom_lub_eq2I)
  show "\<And>Y::nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar} \<Longrightarrow>
       Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_ar))\<cdot>bst)]) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
  proof -
    fix Y::"nat \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>"
    assume chain_Y: "chain Y" and chain_Y_dom: "ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c_ar}"
    have f10: "(\<Squnion>i::nat. Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)])  .  c_as =
                    (\<Squnion>i::nat. Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]  .  c_as)"
      apply (rule cont2contlubE, simp)
      apply (rule chainI)
      by (simp add: chain_Y monofun_cfun_arg monofun_cfun_fun po_class.chainE ub_below ubdom_ubrep_eq ubgetch_ubrep_eq)
    show "Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  c_ar))\<cdot>bst)]) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle([c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  c_ar))\<cdot>bst)]))"
      apply (rule ub_below)
       apply (simp_all add: ubdom_below ubdom_ubrep_eq ubgetch_ubrep_eq f1) 
       apply (metis (mono_tags, lifting) chain_Y chain_Y_dom f1 ubclDom_ubundle_def)
      apply (subst f10)
      by (metis (mono_tags, lifting) chain_Y fun_upd_same lub_eq medrs_tsb_well medrsh_contlub not_below2not_eq option.sel to_medrsh ubgetch_ubrep_eq)
  qed
qed


  subsubsection \<open>tspf_well\<close>
  
 (* show that the mediumRSTSPF template  fulfills the tickcount property *)
lemma medrs_tick: assumes "ubclDom\<cdot>b = {c_ar}" and "(ubLen b) = n" and "#bst=\<infinity>"
  shows "n \<le> (ubclLen (Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(b  .  c_ar))\<cdot>bst)])))"
proof -
  have "(ubLen b) = usclLen\<cdot>(b . c_ar)"
    apply (rule uslen_ubLen_ch3)
    by (metis assms(1) ubclDom_ubundle_def)
  hence f1: "n = usclLen\<cdot>(b . c_ar)"
    using assms(2) by blast
  hence f2: "n \<le> usclLen\<cdot>((tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(b  .  c_ar))\<cdot>bst))"
    by (simp add: assms(3) usclLen_tstream_def)
  show ?thesis
    apply (simp add: ubclLen_ubundle_def)
    apply (rule ubLen_geI)
    apply (simp add: medrs_tsb_dom ubgetch_ubrep_eq)
    by (simp add: f2 ubdom_ubrep_eq)
qed
  
      
    
  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma medrs_well [simp]: assumes "#bst=\<infinity>"
  shows "ufWell (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
  apply (rule ufun_wellI)
    apply (simp_all add: domIff2)
  by (simp add:  ubclDom_ubundle_def ubDom_def)

      
lemma medrs_revsubst: "Abs_cufun (tsMedRSAbb bst) = (medRS_TSPF bst)"
  by (simp add: medRS_TSPF_def)
    
lemma medrs_tspfdom: assumes "#bst =\<infinity>"
  shows "ufDom\<cdot>(medRS_TSPF bst) = {c_ar}"
    apply (simp add: medRS_TSPF_def)
    apply (simp add: ufdom_insert assms)
    apply (simp add: domIff2)
  by (simp add: ubclDom_h)
   
lemma medrs_tspfran: assumes "#bst =\<infinity>"
  shows "ufRan\<cdot>(medRS_TSPF bst) = {c_as}"   
    apply (simp add: medRS_TSPF_def)
    apply (simp add: ufran_least medrs_tspfdom assms)
    apply (simp add: medrs_revsubst medrs_tspfdom assms)
  by (simp add: medrs_tsb_dom ubcldom_least_cs)


  (* now special lemmata for TSPS instantiation *)

lemma medrs_well2 [simp]: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufWell (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubclDom\<cdot>x = {c_ar})
                           \<leadsto> Abs_ubundle([c_as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>bst)]))"
proof -
   have "#bst = \<infinity>"
     by (simp add: med_ora_length assms(1))
   thus ?thesis  
     by (simp add: medrs_tspfdom)
qed
  

lemma medrs_tspfdom2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufclDom\<cdot>(medRS_TSPF bst) = {c_ar}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medrs_tspfdom ufclDom_ufun_def)
qed
  
lemma medrs_tspfran2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "ufRan\<cdot>(medRS_TSPF bst) = {c_as}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medrs_tspfran)
qed

  (* necessary for TSPS instantiation *)
lemma medrs_tsps_dom1 [simp]: "f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufDom\<cdot>f = {c_ar}"
  by (metis medrs_tspfdom2 ufclDom_ufun_def)

lemma medrs_tsps_dom2 [simp]: "\<exists>ora::bool stream. f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufDom\<cdot>f = {c_ar}"
  using medrs_tsps_dom1  by auto
 
lemma medrs_tsps_ran1 [simp]: "f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> ufRan\<cdot>f = {c_as}"
  by (simp add: medrs_tspfran2)

lemma medrs_tsps_ran2 [simp]: "\<exists>ora::bool stream. f = medRS_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> ufRan\<cdot>f = {c_as}"
  using medrs_tsps_ran1 by auto


      
  subsection \<open>medium_sr\<close>     

subsubsection \<open>defs\<close>

definition medSRH :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP tstream"  where
"medSRH bst \<equiv> (\<lambda> x. (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst))"

lemma medsrh_cont [simp]: "cont (medSRH bst)"
  by (simp add: medSRH_def)

lemma medsrh_contlub: assumes "chain Y"
  shows "(medSRH bst) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medSRH bst) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medsrh: "tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x  .  c_ds))\<cdot>bst)
                  = ((medSRH :: bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP tstream) bst) x"
  by (simp add: medSRH_def)

subsubsection \<open>pre\<close>
(*
lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast
*)

lemma medsr_tsb_well[simp]: "tsb_well [c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]"
  apply (rule tsb_wellI)
  by (simp add: tsmap_tsdom_range)

lemma medsr_tsb_dom: "tsbDom\<cdot>([c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>) = {c_dr}"
  by (simp add: tsbdom_rep_eq)
    
  subsubsection \<open>cont\<close>
    
(* definition tsMedSRTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedSRTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)" *)

(* this can be shown analogue to before *)
lemma medsr_cont [simp]: "cont (\<lambda> x::'a MABP TSB. (tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)"
  sorry
    
 
  subsubsection \<open>tspf_well\<close>

lemma medsr_tick: assumes "tsbDom\<cdot>b = {c_ds}" and "(#\<surd>tsb b) = n" and "#bst=\<infinity>"
  shows "n \<le> (#\<surd>tsb [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(b . c_ds))\<cdot>bst)]\<Omega>)"
proof -
  have "(#\<surd>tsb b) = #\<surd>(b . c_ds)"
    apply (rule tsbtick_single_ch2)
    by (simp add: assms(1))
  hence f1: "n = #\<surd>(b . c_ds)"
    using assms(2) by blast
  hence f2: "n \<le> #\<surd>((tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(b . c_ds))\<cdot>bst))"
    by (simp add: assms(3))
  show ?thesis
    apply (rule tsbtick_geI)
    apply (simp add: medsr_tsb_dom tsbgetch_rep_eq)
    using f2 by force
qed    
    
  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma medsr_well [simp]: assumes "#bst=\<infinity>"
  shows "tspf_well (\<Lambda> x.(tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)"
  apply (rule tspf_wellI)
    apply (simp_all add: domIff2 medsr_tsb_dom)
    apply (subst tsbtick_single_ch1, simp)
    by (simp add: assms tsbtick_single_ch2)    
 
lemma medsr_revsubst: "Abs_CTSPF (medSR_TSPFAbb bst) = (medSR_TSPF bst)"
  by (simp add: medSR_TSPF_def)
    
lemma medsr_tspfdom: assumes "#bst =\<infinity>"
  shows "tspfDom\<cdot>(medSR_TSPF bst) = {c_ds}"
    apply (simp add: medSR_TSPF_def)
    apply (simp add: tspf_dom_insert assms)
    apply (simp add: domIff2)
    by (meson tsbleast_tsdom someI)
   
lemma medsr_tspfran: assumes "#bst =\<infinity>"
  shows "tspfRan\<cdot>(medSR_TSPF bst) = {c_dr}"   
    apply (simp add: medSR_TSPF_def)
    apply (simp add: tspfran_least medsr_tspfdom assms)
    apply (simp add: medsr_revsubst medsr_tspfdom assms)
    by (metis singletonI tsb_newMap_id tsbleast_getch tsbleast_tsdom)

  (* now special lemmata for TSPS instantiation *)

lemma medsr_well2 [simp]: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "tspf_well (\<Lambda> x.(tsbDom\<cdot>x = {c_ds})
  \<leadsto> [c_dr \<mapsto> (tsMap:: ('a \<times> bool \<Rightarrow> 'a MABP) \<Rightarrow> ('a \<times> bool) tstream \<rightarrow> 'a MABP tstream) 
            BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>bst)]\<Omega>)"
proof -
   have "#bst = \<infinity>"
     by (simp add: med_ora_length assms(1))
   thus ?thesis
     by (simp add: medsr_tspfdom)
qed
  

lemma medsr_tspfdom2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "tspfDom\<cdot>(medSR_TSPF bst) = {c_ds}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medsr_tspfdom)
qed
  
lemma medsr_tspfran2: assumes "#({True} \<ominus> bst) = \<infinity>"
  shows "tspfRan\<cdot>(medSR_TSPF bst) = {c_dr}"
proof -
  have "#bst = \<infinity>"
    by (simp add: med_ora_length assms(1))
  thus ?thesis
    by (simp add: medsr_tspfran)
qed

  (* necessary for TSPS instantiation *)
lemma medsr_tsps_dom1 [simp]: "f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> tspfDom\<cdot>f = {c_ds}"
  by (simp add: medsr_tspfdom2)

lemma medsr_tsps_dom2 [simp]: "\<exists>ora::bool stream. f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> tspfDom\<cdot>f = {c_ds}"
  using medsr_tsps_dom1  by auto
 
lemma medsr_tsps_ran1 [simp]: "f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> \<Longrightarrow> tspfRan\<cdot>f = {c_dr}"
  by (simp add: medsr_tspfran2)

lemma medsr_tsps_ran2 [simp]: "\<exists>ora::bool stream. f = medSR_TSPF ora \<and> #({True} \<ominus> ora) = \<infinity> 
                               \<Longrightarrow> tspfRan\<cdot>f = {c_dr}"
  using medsr_tsps_ran1 by auto
      
(* ----------------------------------------------------------------------- *)
section \<open>Component Definitions\<close>
(* ----------------------------------------------------------------------- *)
  
lift_definition RCV :: "('a MABP tstream\<^sup>\<Omega> , 'a MABP tstream\<^sup>\<Omega>) ufun uspec" is "Rev {recvTSPF}"
  apply (simp add: inv_def)
  by (simp add: uspecWell_def)
    
lift_definition MEDSR :: "'a MABP TSPS" is "{medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (rule tsps_wellI)
   by (simp_all)
    
lift_definition MEDRS :: "'a MABP TSPS" is "{medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  apply (rule tsps_wellI)
   by (simp_all) (* proof uses the special medrs_tsps lemmata *)
    
lift_definition SND  :: "'a MABP TSPS" is "{senderTSPF s | s. s \<in> tsSender}"
  apply (rule tsps_wellI)
   apply (simp_all)
    (* instantiation analogue to MEDRS *)
    sorry

abbreviation sendCompRecv :: "'a MABP TSPS" where 
"sendCompRecv \<equiv> (SND::'a MABP TSPS) \<Otimes> (RCV::'a MABP TSPS)"
  
      
abbreviation gencompABP :: "'a MABP TSPS" where
"gencompABP \<equiv> ((SND \<Otimes> MEDSR) \<Otimes> RCV) \<Otimes> MEDRS"
  
  

(* ----------------------------------------------------------------------- *)
section \<open>More Lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
  (* Final lemma for general composition operator*)
lemma abp_gencomp_final: assumes "f \<in> Rep_TSPS gencompABP"
                            and "tsbDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
  oops                          
      

*)