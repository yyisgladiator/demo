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

definition idTSPF3 :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"idTSPF3 \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> 
                                            tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))])"


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

lemma recvTSPF_apply: assumes "ubclDom\<cdot>ub = {c_dr}"
  shows "recvTSPF\<rightleftharpoons>ub = Abs_ubundle([c_ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(ub . c_dr)))),
                       c_abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(ub . c_dr))))])"
  by (simp add: recvTSPF_def assms)

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


lemma senderTSPF_apply : assumes "s \<in> tsSender" and "ubDom\<cdot>ub = {c_abpIn, c_as}"
  shows "(senderTSPF s)\<rightleftharpoons>ub = Abs_ubundle([c_ds \<mapsto> tsMap BoolPair\<cdot>((s::('a::countable tstream \<rightarrow> bool tstream \<rightarrow> ('a::countable \<times> bool) tstream))\<cdot>(tsMap invData\<cdot>(ub . c_abpIn))\<cdot>(tsMap invBool\<cdot>(ub . c_as)))])"
  apply (simp add: senderTSPF_def assms)
  apply (simp add: ubclDom_ubundle_def)
  by (simp add: assms(2) doubleton_eq_iff)

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

lemma medsr_tspf_apply: assumes "ubDom\<cdot>ub = {c_ds}" and "#ora = \<infinity>"
  shows "(medSR_TSPF ora)\<rightleftharpoons>ub = Abs_ubundle [c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(ub  .  c_ds))\<cdot>ora)] "
  apply (simp add: med_TSPF_def)
  apply (subst rep_abs_cufun)
  by (simp add: assms) +

lemma medrs_tspf_apply: assumes "ubDom\<cdot>ub = {c_ar}" and "#ora = \<infinity>"
  shows "(medRS_TSPF ora)\<rightleftharpoons>ub = Abs_ubundle [c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(ub  .  c_ar))\<cdot>ora)] "
  apply (simp add: med_TSPF_def)
  apply (subst rep_abs_cufun)
  by (simp add: assms) +

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


subsection\<open>id3\<close>
(*
definition idTSPF3 :: "('a MABP tstream\<^sup>\<Omega>) ufun" where
"idTSPF3 \<equiv> Abs_cufun (\<lambda> x. (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> 
                                            tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))])"
*)


lemma tsmap_idI: "tsDom\<cdot>ts \<subseteq> range f \<longrightarrow> tsMap f\<cdot>(tsMap (inv f)\<cdot>ts) = ts"
   apply (rule tstream_induct)
    apply simp_all
   apply (simp add: tsmap_delayfun)
   apply (simp add: tsdom_delayfun)
  by (simp add: f_inv_into_f tsdom_mlscons tsmap_mlscons)


lemma ubgetch_tsmap_idI: "ubDom\<cdot>x = cs \<Longrightarrow> c \<in> cs \<Longrightarrow> ctype c = range f \<Longrightarrow> tsMap f\<cdot>(tsMap (inv f)\<cdot>(x  .  c)) = x  .  c"
proof -
  assume a1: "ubDom\<cdot>x = cs" and a2: "c \<in> cs" and a3: "ctype c = range f"
  have f1: "usclOkay c (x . c)"
    by (simp add: a1 a2 ubgetch_insert)
  have f2: "tsDom\<cdot>(x . c) \<subseteq> ctype c"
    using f1 usclOkay_tstream_def by auto
  have f3: "tsDom\<cdot>(x . c) \<subseteq> range f"
    using a3 f2 by auto
  show "tsMap f\<cdot>(tsMap (inv f)\<cdot>(x  .  c)) = x  .  c"
    by (simp add: tsmap_idI f3)
qed

lemma c_idOut_tsmap_id: assumes "c_abpOut \<in> ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>)" 
  shows "[c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))] = [c_idOut \<mapsto> x . c_abpOut]"
  by (simp add: assms ubgetch_tsmap_idI)

lemma c_idOut_tsmap_id2: "(\<lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))]) = 
  (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle[c_idOut \<mapsto> x . c_abpOut])"
  using c_idOut_tsmap_id by fastforce

lemma idtspf2_3_eq: "idTSPF2 = idTSPF3"
  apply (simp add: idTSPF2_def idTSPF3_def)
proof -
  have "\<forall>u ua. ubDom\<cdot>(u::'a MABP tstream\<^sup>\<Omega>) \<noteq> {c_abpOut} \<or> ubDom\<cdot>ua \<noteq> {c_abpOut} \<or> ubDom\<cdot>u = {c_abpOut} \<and> ubDom\<cdot>ua = {c_abpOut} \<and> Some (Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot> (tsMap invData\<cdot>(ua . c_abpOut)::'a tstream)]) = Some (Abs_ubundle [c_idOut \<mapsto> ua . c_abpOut])"
    by (simp add: c_idOut_tsmap_id)
  then show "Abs_cufun (\<lambda>u. (ubDom\<cdot>u = {c_abpOut})\<leadsto>Abs_ubundle [c_idOut \<mapsto> u . c_abpOut]) = Abs_cufun (\<lambda>u. (ubDom\<cdot>u = {c_abpOut})\<leadsto>Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot> (tsMap invData\<cdot> (u . c_abpOut)::'a tstream)])"
    by (metis (lifting))
qed

lemma idTSPF3_result_ubwell:  assumes "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}" 
  shows "ubWell [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))]"
  by (simp add: assms c_idOut_tsmap_id idTSPF2_result_ubwell)

lemma idTSPF3_result_dom:  assumes "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}" 
  shows "ubDom\<cdot>(Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))]) = {c_idOut}"
  by (simp add: assms c_idOut_tsmap_id idTSPF2_result_dom)

lemma idTSPF3_io_eq: assumes "ubDom\<cdot>(x::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut}"
  shows "((\<lambda> (x::'a MABP tstream\<^sup>\<Omega>). (ubDom\<cdot>x = {c_abpOut}) 
    \<leadsto> Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))])\<rightharpoonup>x) . c_idOut
    = (x::'a MABP tstream\<^sup>\<Omega>) . c_abpOut"
  by (metis assms c_idOut_tsmap_id2 idTSPF2_io_eq)

subsubsection\<open>mono/cont\<close>

lemma idTSPF3_mono: "monofun (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). 
    (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))])"
  by (simp add: below_option_def c_idOut_tsmap_id idTSPF2_result_below monofunI ubdom_below)

lemma idTSPF3_cont: "cont (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). 
      (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))])"
  by (simp add: c_idOut_tsmap_id2 idTSPF2_cont)

subsubsection\<open>ufWell/tickCount\<close>
lemma idTSPF3_well: "ufWell (\<Lambda> (x::('a MABP tstream\<^sup>\<Omega>)). 
      (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))])"
  by (simp add: c_idOut_tsmap_id2 idTSPF2_well)

lemma idTSPF3_tickCount: "ufIsWeak (Abs_cufun (\<lambda> (x::('a MABP tstream\<^sup>\<Omega>)). 
      (ubDom\<cdot>x = {c_abpOut}) \<leadsto> Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))]))"
  by (simp add: c_idOut_tsmap_id2 idTSPF2_tickCount)


lemma idTSPF3_dom: "ufDom\<cdot>idTSPF3 = {c_abpOut}"
  by (metis idtspf2_3_eq idTSPF2_dom)

lemma idTSPF3_ran: "ufRan\<cdot>idTSPF3 = {c_idOut}"
  by (metis idtspf2_3_eq idTSPF2_ran)

lemma idTSPF3_apply : assumes "ubDom\<cdot>ub = {c_abpOut}"
  shows "idTSPF3 \<rightleftharpoons> ub = Abs_ubundle [c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(ub . c_abpOut))]"
  apply (simp add: idTSPF3_def)
  by (simp add: idTSPF3_cont idTSPF3_well assms)

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
"Rev {idTSPF3}"
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
"innerABP s ora1 ora2 \<equiv> (ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3))"

abbreviation ABPBundleHelper where
"ABPBundleHelper se ora1 ora2 tb \<equiv> (\<lambda> x. [
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut  \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2)
    ])"


abbreviation fixABPHelper where
"fixABPHelper se ora1 ora2 tb \<equiv> (\<lambda> x. Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut  \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2)
    ])"

abbreviation fixABPHelperCont where
"fixABPHelperCont se ora1 ora2 tb \<equiv> (\<Lambda> x. Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2)
    ])"

abbreviation abpFix where
"abpFix s ora1 ora2 tb \<equiv> ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds}"

abbreviation ABPBundleHelper_ext where
"ABPBundleHelper_ext se ora1 ora2 tb \<equiv> (\<lambda> x. [
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut  \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
    ])"


abbreviation fixABPHelper_ext where
"fixABPHelper_ext se ora1 ora2 tb \<equiv> (\<lambda> x. Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut  \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
    ])"

abbreviation fixABPHelperCont_ext where
"fixABPHelperCont_ext se ora1 ora2 tb \<equiv> (\<Lambda> x. Abs_ubundle[
    c_ds     \<mapsto> tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
    c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
    c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
    c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2),
    c_idOut  \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x . c_abpOut))
    ])"

abbreviation abpFix_ext where
"abpFix_ext s ora1 ora2 tb \<equiv> ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"


(*
lemma ABPBundleHelper_ext_cont: assumes "#({True} \<ominus> ora1) = \<infinity>"
  and "#({True} \<ominus> ora2) = \<infinity>"
  and "se \<in> tsSender"
  and "ubDom\<cdot>tb = {c_abpIn}"
shows "cont (fixABPHelpert ora1 ora2 tb)"
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
subsection \<open>Component Definitions\<close>
(* ----------------------------------------------------------------------- *)

lemma id_consistent: "uspecIsConsistent ID"
  by (simp add: ID.rep_eq inv_def uspecIsConsistent_def)

lemma id_uspec_ele: "\<forall> ufun \<in> Rep_rev_uspec ID. ufun = idTSPF3"
  by (simp add: ID.rep_eq inv_rev_rev)

lemma id_uspec_ele2: " idTSPF3 \<in> Rep_rev_uspec ID"
  by (simp add: ID.rep_eq inv_rev_rev)

lemma id_uspec_dom: "uspecDom (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclDom\<cdot>(idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis id_consistent id_uspec_ele some_in_eq uspecDom_def uspecIsConsistent_def)

lemma id_uspec_ran: "uspecRan (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclRan\<cdot>(idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis id_consistent id_uspec_ele some_in_eq uspecIsConsistent_def uspecRan_def)


lemma rev_uspec_consistent: "uspecIsConsistent RCV"
  by (simp add: RCV.rep_eq inv_def uspecIsConsistent_def)

lemma rcv_uspec_ele: "\<forall> ufun \<in> Rep_rev_uspec RCV. ufun = recvTSPF"
  by (simp add: RCV.rep_eq inv_rev_rev)

lemma rcv_uspec_ele2: "recvTSPF \<in> Rep_rev_uspec RCV"
  by (simp add: RCV.rep_eq inv_rev_rev)

lemma rcv_uspec_dom: "uspecDom (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclDom\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis rcv_uspec_ele rev_uspec_consistent some_in_eq uspecDom_def uspecIsConsistent_def)

lemma rcv_uspec_ran: "uspecRan (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
  = ufclRan\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
  by (metis rcv_uspec_ele rev_uspec_consistent some_in_eq uspecIsConsistent_def uspecRan_def)


lemma medrs_consist_dom: assumes "f \<in> Rep_rev_uspec (MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
  shows "uspecDom (MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec) = ufclDom\<cdot>f"
  using assms uspec_dom_eq by auto

lemma medrs_rev_insert: "Rep_rev_uspec MEDRS = {medRS_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  by (simp add: MEDRS.rep_eq inv_rev_rev)

lemma medsr_rev_insert: "Rep_rev_uspec MEDSR = {medSR_TSPF ora | ora. #({True} \<ominus> ora)=\<infinity>}"
  by (simp add: MEDSR.rep_eq inv_rev_rev)

lemma medsr_eleI: assumes " #({True} \<ominus> ora)=\<infinity>"
  shows "medSR_TSPF ora \<in> Rep_rev_uspec MEDSR"
  using assms medsr_rev_insert by blast

lemma medrs_eleI: assumes " #({True} \<ominus> ora)=\<infinity>"
  shows "medRS_TSPF ora \<in> Rep_rev_uspec MEDRS"
  using assms medrs_rev_insert by blast

subsection \<open>More Lemmas\<close>

subsubsection \<open>Parcomp Sercomp Well\<close>
lemma c_as_bool_ctype: "ctype c_as = range Bool"
  by simp

lemma c_dr_boolpair_ctype: "ctype c_dr = range BoolPair"
  by simp

paragraph  \<open>medrs id parcomp_well\<close>
lemma medrs_id_parcomp_well : "uspec_parcompwell MEDRS ID"
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
    have f4: "parcomp_well ((medRS_TSPF::bool stream \<Rightarrow> ('a MABP tstream\<^sup>\<Omega>) ufun) ora) (idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun)"
      apply rule
       apply (simp add: ufCompL_def)
       apply (simp_all only: idTSPF3_ran idTSPF3_dom)
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


lemma medrs_id_parcomp_dom: assumes "medrs_f \<in> Rep_rev_uspec MEDRS" and "id_f \<in> Rep_rev_uspec ID"
  shows "ufDom\<cdot>(ufParComp medrs_f id_f) = {c_ar, c_abpOut}"
proof -
  have f1: "parcomp_well medrs_f id_f"
    using uspec_parcomp_h2 ufunclParCompWell_ufun_def 
    by (metis assms(1) assms(2) medrs_id_parcomp_well)
  have f2: "id_f = idTSPF3"
    by (simp add: assms(2) id_uspec_ele)
  obtain ora where ora_def: "medrs_f = medRS_TSPF ora" and ora_def2: "#({True} \<ominus> ora) = \<infinity>"
    using assms(1) medrs_rev_insert by auto
  show ?thesis
    apply (simp add: f1 ufParComp_dom)
    apply (simp add: f2 idTSPF3_dom)
    apply (simp add: ora_def)
    apply (simp add: ora_def2 med_tspfdom2)
    by blast
qed

lemma medrs_id_parcomp_ran: assumes "medrs_f \<in> Rep_rev_uspec MEDRS" and "id_f \<in> Rep_rev_uspec ID"
  shows "ufRan\<cdot>(ufParComp medrs_f id_f) = {c_as, c_idOut}"
proof -
  have f1: "parcomp_well medrs_f id_f"
    using uspec_parcomp_h2 ufunclParCompWell_ufun_def 
    by (metis assms(1) assms(2) medrs_id_parcomp_well)
  have f2: "id_f = idTSPF3"
    by (simp add: assms(2) id_uspec_ele)
  obtain ora where ora_def: "medrs_f = medRS_TSPF ora" and ora_def2: "#({True} \<ominus> ora) = \<infinity>"
    using assms(1) medrs_rev_insert by auto
  show ?thesis
    apply (simp add: f1 ufParComp_ran)
    apply (simp add: f2 idTSPF3_ran)
    apply (simp add: ora_def)
    apply (simp add: ora_def2 med_tspfran2)
    by blast
qed

paragraph \<open>snd medsr sercomp_well\<close>
lemma snd_medsr_sercomp_well: "uspec_sercompwell SND (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
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

lemma snd_medsr_sercomp_dom: assumes "snd_f \<in> Rep_rev_uspec SND" and "medsr_f \<in> Rep_rev_uspec MEDSR"
  shows "ufDom\<cdot>(ufSerComp snd_f medsr_f) = {c_as, c_abpIn}"
proof -
  have f1: "sercomp_well snd_f medsr_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(1) assms(2) snd_medsr_sercomp_well ufunclSerCompWell_ufun_eq by blast
  obtain s where s_def1: "snd_f = senderTSPF s" and s_def2: "s \<in> tsSender"
  proof -
    assume a1: "\<And>s. \<lbrakk>snd_f = senderTSPF s; s \<in> tsSender\<rbrakk> \<Longrightarrow> thesis"
    have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND"
      by (simp add: SND.rep_eq inv_rev_rev)
    then show ?thesis
      using a1 assms(1) by auto
  qed
  show ?thesis
    apply (subst ufSerComp_dom)
    using f1 apply blast
    apply (simp add: s_def1)
    by (simp add: sender_tspfdom)
qed

lemma snd_medsr_sercomp_ran: assumes "snd_f \<in> Rep_rev_uspec SND" and "medsr_f \<in> Rep_rev_uspec MEDSR"
  shows "ufRan\<cdot>(ufSerComp snd_f medsr_f) = {c_dr}"
proof -
  have f1: "sercomp_well snd_f medsr_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(1) assms(2) snd_medsr_sercomp_well ufunclSerCompWell_ufun_eq by blast
  obtain ora where ora_def: "medsr_f = medSR_TSPF ora" and ora_def2: "#({True} \<ominus> ora) = \<infinity>"
    using assms(2) medsr_rev_insert by auto
  show ?thesis
    apply (subst ufSerComp_ran)
    using f1 apply blast
    apply (simp add: ora_def)
    by (simp add: ora_def2 med_tspfran2)
qed


paragraph \<open>snd medsr rcv sercomp_well\<close>
lemma snd_medsr_rcv_sercomp_well: "uspec_sercompwell (SND \<circle> MEDSR) (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
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
          using f00 snd_medsr_sercomp_well uspec_sercomp_consistent2 by auto
        have f02: "uspecIsConsistent (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f00 snd_medsr_sercomp_well uspec_sercomp_consistent2 by auto
        obtain f1 f2 where f1_f2_def: "f1 \<in> Rep_rev_uspec (SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
              \<and> f2 \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f00 snd_medsr_sercomp_well uspec_consist_f_ex uspec_sercomp_consistent2 by blast
        have f03: "ufSerComp f1 f2 \<in> Rep_rev_uspec ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          by (metis f1_f2_def snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
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
          using f00 f1_f2_def local.snd_def snd_medsr_sercomp_well uspec_dom_eq uspec_sercomp_consistent2 uspec_sercomp_dom by blast
        have f06: "\<forall> f \<in> Rep_rev_uspec ((SND \<circle> MEDSR):: ('a MABP tstream\<^sup>\<Omega>) ufun uspec).
            ufclDom\<cdot>f = ufclDom\<cdot>(senderTSPF snd)"
          by (simp add: f05 uspec_dom_eq)
        have f7: "(senderTSPF snd) \<in> Rep_rev_uspec (SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f1_f2_def local.snd_def by auto
        have f8: "(medSR_TSPF ora) \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
          using f1_f2_def ora_def by auto
        have f09: "sercomp_well (senderTSPF snd) (medSR_TSPF ora)"
          by (meson snd_medsr_sercomp_well f7 f8 ufunclSerCompWell_ufun_def uspec_sercomp_h2)
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

lemma snd_medsr_rcv_sercomp_dom: assumes "snd_f \<in> Rep_rev_uspec SND" 
  and "medsr_f \<in> Rep_rev_uspec MEDSR"
  and "rcv_f \<in> Rep_rev_uspec RCV"
  shows "ufDom\<cdot>(ufSerComp (ufSerComp snd_f medsr_f) rcv_f)= {c_as, c_abpIn}"
proof -
  have f1: "sercomp_well snd_f medsr_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(1) assms(2) snd_medsr_sercomp_well ufunclSerCompWell_ufun_eq by blast
  have f2: "ufSerComp snd_f medsr_f \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
    by (metis (mono_tags, lifting) assms(1)  assms(2) snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
  have f3: "sercomp_well (ufSerComp snd_f medsr_f) rcv_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(3) f2 snd_medsr_rcv_sercomp_well ufunclSerCompWell_ufun_eq by blast
  obtain s where s_def1: "snd_f = senderTSPF s" and s_def2: "s \<in> tsSender"
  proof -
    assume a1: "\<And>s. \<lbrakk>snd_f = senderTSPF s; s \<in> tsSender\<rbrakk> \<Longrightarrow> thesis"
    have "{u. \<exists>c. (u::('a MABP tstream\<^sup>\<Omega>) ufun) = senderTSPF c \<and> c \<in> tsSender} = Rep_rev_uspec SND"
      by (simp add: SND.rep_eq inv_rev_rev)
    then show ?thesis
      using a1 assms(1) by auto
  qed
  show ?thesis
    apply (subst ufSerComp_dom)
    using f3 apply blast
    by (metis f1 s_def1 sender_tspfdom ufSerComp_dom)
qed

lemma snd_medsr_rcv_sercomp_ran: assumes "snd_f \<in> Rep_rev_uspec SND" 
  and "medsr_f \<in> Rep_rev_uspec MEDSR"
  and "rcv_f \<in> Rep_rev_uspec RCV"
  shows "ufRan\<cdot>(ufSerComp (ufSerComp snd_f medsr_f) rcv_f)= {c_ar, c_abpOut}"
proof -
  have f1: "sercomp_well snd_f medsr_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(1) assms(2) snd_medsr_sercomp_well ufunclSerCompWell_ufun_eq by blast
  have f2: "ufSerComp snd_f medsr_f \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
    by (metis (mono_tags, lifting) assms(1)  assms(2) snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
  have f3: "sercomp_well (ufSerComp snd_f medsr_f) rcv_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(3) f2 snd_medsr_rcv_sercomp_well ufunclSerCompWell_ufun_eq by blast
  show ?thesis
    apply (subst ufSerComp_ran)
    using f3 apply blast
    using rcv_uspec_ele recv_tspfran 
    using assms(3) by fastforce
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
        using False medrs_id_parcomp_well uspec_parcomp_consistent2 by auto
      have f02: "uspecIsConsistent (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f00 snd_medsr_rcv_sercomp_well uspec_sercomp_consistent2 by auto
      have f03: "uspecIsConsistent (SND \<circle> (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))"
        using f00 snd_medsr_rcv_sercomp_well uspec_sercomp_consistent2 by auto
      have f04: "uspecIsConsistent (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f03 snd_medsr_sercomp_well uspec_sercomp_consistent2 by auto
      have f05: "uspecIsConsistent (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f03 snd_medsr_sercomp_well uspec_sercomp_consistent2 by blast
      obtain f1 where f1_def: "f1 \<in> Rep_rev_uspec (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f05 uspec_consist_f_ex by blast
      obtain f2 where f2_def: "f2 \<in> Rep_rev_uspec (MEDSR:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f04 uspec_consist_f_ex by auto
      obtain f3 where f3_def: "f3 \<in> Rep_rev_uspec (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using f02 uspec_consist_f_ex by auto
      obtain f4 where f4_def: "f4 \<in> Rep_rev_uspec (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
        using False medrs_id_parcomp_well uspec_consist_f_ex uspec_parcomp_consistent2 by blast
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
        by (meson snd_medsr_sercomp_well f10 f11 ufunclSerCompWell_ufun_def uspec_sercomp_h2)
      have f13: "(ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
        by (metis f1_def f2_def local.snd_def ora1_def snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_h1)
      have f14: "sercomp_well (ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) f3"
        by (meson snd_medsr_rcv_sercomp_well f13 f3_def ufunclSerCompWell_ufun_def uspec_sercomp_h2)
      have f15: "ufSerComp (ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) f3 \<in>  
        Rep_rev_uspec ((SND \<circle> MEDSR) \<circle> RCV)"
        by (metis f13 f3_def snd_medsr_rcv_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
      have f16: "parcomp_well f4 f5"
        by (meson medrs_id_parcomp_well f4_def f5_def ufunclParCompWell_ufun_def uspec_parcomp_h2)
      have f17: "ufParComp f4 f5 \<in> Rep_rev_uspec (MEDRS \<parallel> ID)"
        by (metis f4_def f5_def medrs_id_parcomp_well ufunclParComp_ufun_def uspec_parcomp_h1)
      have f18: "f5 = idTSPF3"
        by (metis ID.rep_eq f5_def inv_rev_rev singletonD)
      have f19: "f3 = recvTSPF"
        by (simp add: f3_def rcv_uspec_ele)
      have f20: "sercomp_well (ufSerComp (ufSerComp (senderTSPF snd) (medSR_TSPF ora1)) f3) (ufParComp f4 f5)"
        apply (simp add: f18 f19)
        apply (simp add: snd_medsr_rcv_sercomp_ran snd_medsr_rcv_sercomp_dom f10 f11 rcv_uspec_ele2)
        by (simp add: medrs_id_parcomp_dom medrs_id_parcomp_ran f4_def id_uspec_ele2)
      then show ?thesis 
        apply (simp add: uspec_sercompwell_def)
        apply (simp add: ufunclSerCompWell_ufun_def)
        by (metis f15 f17 ufclDom_ufun_def ufclRan_ufun_def uspec_dom_eq uspec_ran_eq)
    qed
  qed

lemma snd_medsr_rcv_medrs_id_dom: assumes "snd_f \<in> Rep_rev_uspec SND" 
  and "medsr_f \<in> Rep_rev_uspec MEDSR"
  and "rcv_f \<in> Rep_rev_uspec RCV"
  and "medrs_f \<in> Rep_rev_uspec MEDRS" 
  and "id_f \<in> Rep_rev_uspec ID"
shows "ufDom\<cdot>(ufSerComp (ufSerComp (ufSerComp snd_f medsr_f) rcv_f) (ufParComp medrs_f id_f)) 
                            = {c_as, c_abpIn}"
proof -
  have f1: "sercomp_well snd_f medsr_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(1) assms(2) snd_medsr_sercomp_well ufunclSerCompWell_ufun_eq by blast
  have f2: "ufSerComp snd_f medsr_f \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
    by (metis (mono_tags, lifting) assms(1)  assms(2) snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
  have f3: "sercomp_well (ufSerComp snd_f medsr_f) rcv_f"
    using uspec_sercomp_h2 assms(3) f2 snd_medsr_rcv_sercomp_well ufunclSerCompWell_ufun_eq by blast
  have f4: "ufSerComp (ufSerComp snd_f medsr_f) rcv_f \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV)"
    by (metis assms(3) f2 snd_medsr_rcv_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_h1)
  have f5: "parcomp_well medrs_f id_f"
    using uspec_parcomp_h2 ufunclParCompWell_ufun_def 
    by (metis assms(4) assms(5) medrs_id_parcomp_well)
  have f6: "id_f = idTSPF3"                  
    by (simp add: assms(5) id_uspec_ele)
  have f7: "ufParComp medrs_f id_f \<in> Rep_rev_uspec (MEDRS \<parallel> ID)"
    by (metis assms(4) assms(5) ufunclParComp_ufun_def  medrs_id_parcomp_well uspec_parcomp_h1)
  have f8: "sercomp_well (ufSerComp (ufSerComp snd_f medsr_f) rcv_f) (ufParComp medrs_f id_f)"
    by (simp add: medrs_id_parcomp_ran medrs_id_parcomp_dom snd_medsr_rcv_sercomp_ran snd_medsr_rcv_sercomp_dom assms)
  show ?thesis
    apply (subst ufSerComp_dom)
    using f8 apply blast
    by (simp add: assms(1) assms(2) assms(3) snd_medsr_rcv_sercomp_dom)
qed

lemma snd_medsr_rcv_medrs_id_ran: assumes "snd_f \<in> Rep_rev_uspec SND" 
  and "medsr_f \<in> Rep_rev_uspec MEDSR"
  and "rcv_f \<in> Rep_rev_uspec RCV"
  and "medrs_f \<in> Rep_rev_uspec MEDRS" 
  and "id_f \<in> Rep_rev_uspec ID"
shows "ufRan\<cdot>(ufSerComp (ufSerComp (ufSerComp snd_f medsr_f) rcv_f) (ufParComp medrs_f id_f)) 
                            = {c_as, c_idOut}"
proof -
  have f1: "sercomp_well snd_f medsr_f"
    using uspec_sercomp_h2 ufunclParCompWell_ufun_def 
    using assms(1) assms(2) snd_medsr_sercomp_well ufunclSerCompWell_ufun_eq by blast
  have f2: "ufSerComp snd_f medsr_f \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
    by (metis (mono_tags, lifting) assms(1)  assms(2) snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)
  have f3: "sercomp_well (ufSerComp snd_f medsr_f) rcv_f"
    using uspec_sercomp_h2 assms(3) f2 snd_medsr_rcv_sercomp_well ufunclSerCompWell_ufun_eq by blast
  have f4: "ufSerComp (ufSerComp snd_f medsr_f) rcv_f \<in> Rep_rev_uspec (SND \<circle> MEDSR \<circle> RCV)"
    by (metis assms(3) f2 snd_medsr_rcv_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_h1)
  have f5: "parcomp_well medrs_f id_f"
    using uspec_parcomp_h2 ufunclParCompWell_ufun_def 
    by (metis assms(4) assms(5) medrs_id_parcomp_well)
  have f6: "id_f = idTSPF3"                  
    by (simp add: assms(5) id_uspec_ele)
  have f7: "ufParComp medrs_f id_f \<in> Rep_rev_uspec (MEDRS \<parallel> ID)"
    by (metis assms(4) assms(5) ufunclParComp_ufun_def  medrs_id_parcomp_well uspec_parcomp_h1)
  have f8: "sercomp_well (ufSerComp (ufSerComp snd_f medsr_f) rcv_f) (ufParComp medrs_f id_f)"
    by (simp add: medrs_id_parcomp_ran medrs_id_parcomp_dom snd_medsr_rcv_sercomp_ran snd_medsr_rcv_sercomp_dom assms)
  show ?thesis
    apply (subst ufSerComp_ran)
    using f8 apply blast
    by (simp add: assms(4) assms(5) medrs_id_parcomp_ran)
qed

lemma innerABP_applyI: assumes "ubDom\<cdot>ub = {c_abpIn, c_as}"
  and "se \<in> tsSender" and "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>"
shows "(innerABP se ora1 ora2)\<rightleftharpoons>ub = 
(ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF se \<rightleftharpoons> ub)))))\<cdot>
           ((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF se \<rightleftharpoons> ub))))))"
proof -
  have f0: "senderTSPF se \<in> Rep_rev_uspec SND"
    by (metis (mono_tags, lifting) SND.rep_eq assms(2) inv_rev_rev mem_Collect_eq)
  have f1: "medSR_TSPF ora1 \<in> Rep_rev_uspec (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: medsr_eleI assms(3))
  have f2: "((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun) \<in> Rep_rev_uspec (MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: medrs_eleI assms(4))
  have f1: "(innerABP se ora1 ora2)\<rightleftharpoons>ub = 
   (ufParComp (medRS_TSPF ora2) idTSPF3)\<rightleftharpoons>((ufSerComp (ufSerComp (senderTSPF se) (medSR_TSPF ora1)) recvTSPF)\<rightleftharpoons>ub)"
    apply (rule ufSerComp_apply)
     apply (simp add: snd_medsr_rcv_sercomp_dom snd_medsr_rcv_sercomp_ran f0 f1 rcv_uspec_ele2)
     apply (simp add: medrs_id_parcomp_dom medrs_id_parcomp_ran f2 id_uspec_ele2)
    apply (simp add: ubclDom_ubundle_def)
    apply (simp add: snd_medsr_rcv_medrs_id_dom f0 f1 f2 id_uspec_ele2 rcv_uspec_ele2)
    using assms(1) by blast
  have f2: "((ufSerComp (ufSerComp (senderTSPF se) (medSR_TSPF ora1)) recvTSPF)\<rightleftharpoons>ub) = 
              recvTSPF\<rightleftharpoons>((ufSerComp (senderTSPF se) (medSR_TSPF ora1))\<rightleftharpoons>ub)"
    apply (rule ufSerComp_apply)
     apply (subst snd_medsr_sercomp_dom)
       apply (simp add: f0)
    using assms(3) medsr_rev_insert apply blast
     apply (subst snd_medsr_sercomp_ran)
       apply (simp add: f0)
    using assms(3) medsr_rev_insert apply blast
     apply (subst snd_medsr_sercomp_ran)
       apply (simp add: f0)
    using assms(3) medsr_rev_insert apply blast
    apply (simp add: recv_tspfdom recv_tspfran)
    apply (simp add: ubclDom_ubundle_def)
    apply (subst snd_medsr_rcv_sercomp_dom)
       apply (simp_all add: f0 f1 rcv_uspec_ele2 assms(1))
    using assms(3) medsr_rev_insert apply blast
    by blast
  have f3: "(ufSerComp (senderTSPF se) (medSR_TSPF ora1))\<rightleftharpoons>ub = 
       (medSR_TSPF ora1)\<rightleftharpoons>((senderTSPF se)\<rightleftharpoons>ub)"
    apply (rule ufSerComp_apply)
     apply (simp add: assms(3) med_tspfdom2 med_tspfran2 sender_tspfdom sender_tspfran)
    apply (simp add: ubclDom_ubundle_def assms(1)) 
    using assms(3) f0 medsr_rev_insert snd_medsr_sercomp_dom by fastforce
  have f4: "\<And> ub:: ('a MABP tstream\<^sup>\<Omega>). ubclDom\<cdot>ub = ufDom\<cdot>(ufParComp ((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) (idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun)) 
      \<longrightarrow> (ufParComp ((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) (idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<rightleftharpoons>ub = (ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub))\<cdot>((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub)))"
  proof rule
    fix ub::"'a MABP tstream\<^sup>\<Omega>"
    assume a1: "ubclDom\<cdot>ub = ufDom\<cdot>(ufParComp ((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) (idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))"
    show "(ufParComp ((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) (idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<rightleftharpoons>ub = (ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub))\<cdot>((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub)))"
      apply (subst ufParComp_apply)
        apply (simp only: idTSPF3_dom idTSPF3_ran ufCompL_def)
        apply (simp add:  med_tspfdom med_tspfran assms(4) med_ora_length)
      by (simp_all add: a1)
  qed
  have f4: "recvTSPF\<rightleftharpoons>((ufSerComp (senderTSPF se) (medSR_TSPF ora1))\<rightleftharpoons>ub) = 
            recvTSPF\<rightleftharpoons>((medSR_TSPF ora1)\<rightleftharpoons>((senderTSPF se)\<rightleftharpoons>ub))"
    by (simp add: f3)
  have f5: "ufRan\<cdot>recvTSPF = ufDom\<cdot>(ufParComp ((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) (idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))"
  proof -
    have "(medRS_TSPF ora2::('a MABP tstream\<^sup>\<Omega>) ufun) \<in> Rep_rev_uspec MEDRS"
      using assms(4) medrs_rev_insert by blast
    then show ?thesis
      by (simp add: id_uspec_ele2 medrs_id_parcomp_dom recv_tspfran)
  qed
  have f6: "ufRan\<cdot>(senderTSPF se) = ufDom\<cdot>(medSR_TSPF ora1)"
    by (simp add: assms(3) med_tspfdom2 sender_tspfran)
  have f7: "ufRan\<cdot>(medSR_TSPF ora1) = ufDom\<cdot>recvTSPF"
    by (simp add: assms(3) med_tspfran2 recv_tspfdom)
  have f9: "ubDom\<cdot>ub = ufDom\<cdot>(senderTSPF se)"
    by (simp add: assms(1) insert_commute sender_tspfdom)
  have f18: "ufRan\<cdot>(ufSerComp (ufSerComp (senderTSPF se) (medSR_TSPF ora1)) recvTSPF) = {c_abpOut, c_ar}"
    by (simp add: assms(3) f0 insert_commute medsr_eleI rcv_uspec_ele2 snd_medsr_rcv_sercomp_ran)
  have f19: "ufDom\<cdot>(ufSerComp (ufSerComp (senderTSPF se) (medSR_TSPF ora1)) recvTSPF) = {c_abpIn, c_as}"
    by (simp add: assms(3) f0 insert_commute medsr_eleI rcv_uspec_ele2 snd_medsr_rcv_sercomp_dom)
  have f20: "sercomp_well (ufSerComp (ufSerComp (senderTSPF se) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3)"
    apply (simp only: f19 f18)
    apply (simp add: medrs_id_parcomp_dom medrs_id_parcomp_ran id_uspec_ele2 assms(4) medrs_eleI)
    by blast
  have f30: "ubDom\<cdot>((senderTSPF se)\<rightleftharpoons>ub) = ufRan\<cdot>(senderTSPF se)"
    by (metis f9 ubclDom_ubundle_def ufran_2_ubcldom2)
  have f31: "ubDom\<cdot>((medSR_TSPF ora1)\<rightleftharpoons>((senderTSPF se)\<rightleftharpoons>ub)) = ufRan\<cdot>(medSR_TSPF ora1::('a MABP tstream\<^sup>\<Omega>) ufun)"
    apply (fold ubclDom_ubundle_def)
    apply (subst ufran_2_ubcldom2)
    by (simp_all add: f30 f6 ubclDom_ubundle_def)
  have f32: "ubDom\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF se \<rightleftharpoons> ub))) = ufRan\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun)"
    apply (fold ubclDom_ubundle_def)
    apply (subst ufran_2_ubcldom2)
    by (simp_all add: f31 f7 ubclDom_ubundle_def)
  show ?thesis
    apply (simp add: f1)
    apply (simp add: f2)
    apply (simp add: f3)
    apply (subst ufParComp_apply)
      apply (simp add: ufCompL_def assms(4) med_tspfran2 med_tspfdom2 idTSPF3_dom idTSPF3_ran)
     apply (simp add: ubclDom_ubundle_def)
     apply (simp add: f32 f5)
    by simp
qed

lemma innerABP_ubgetchR: assumes "ubDom\<cdot>(ub::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut, c_ar}"
  shows "(ubclUnion\<cdot>(((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun)\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub))\<cdot>
                ((idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun)\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>(idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub))) . c_idOut =
                ((idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun)\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>(idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub)) . c_idOut"
    apply (simp add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
    apply (subst ubunion_getchR)
     apply (metis (no_types, hide_lams) assms Int_commute Int_empty_left Int_insert_left_if1 idTSPF3_dom idTSPF3_ran insertI1 ubclDom_ubundle_def ubrestrict_ubdom2 ufran_2_ubcldom2)
  by simp

lemma innerABP_ubgetchL: assumes "ubDom\<cdot>(ub::'a MABP tstream\<^sup>\<Omega>) = {c_abpOut, c_ar}"
  shows "(ubclUnion\<cdot>(((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun)\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub))\<cdot>
                ((idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun)\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>(idTSPF3::('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub))) . c_as =
                (((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun)\<rightleftharpoons>(ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2)::('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>ub)) . c_as"
    apply (simp add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
  apply (subst ubunion_getchL)
   apply (simp add: idTSPF3_dom)
  apply (fold ubclDom_ubundle_def)
   apply (subst ufran_2_ubcldom2)
    apply (simp_all add: assms idTSPF3_dom ubclDom_ubundle_def)
  by (simp add: idTSPF3_ran)


subsubsection \<open>Helper Lemmas\<close>

  paragraph \<open>innerABP\<close>
lemma innerABP_dom:  assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ufDom\<cdot>(innerABP s ora1 ora2) = {c_abpIn, c_as}"
  apply (subst snd_medsr_rcv_medrs_id_dom)
       apply (metis (mono_tags, lifting) CollectI SND.rep_eq assms(1) inv_rev_rev)
      apply (simp add: assms(2) medsr_eleI)
     apply (simp add: rcv_uspec_ele2)
    apply (simp add: assms(3) medrs_eleI)
   apply (simp add: id_uspec_ele2)
  by blast

lemma innerABP_ran:  assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ufRan\<cdot>(innerABP s ora1 ora2) =  {c_idOut, c_as}"
  apply (subst snd_medsr_rcv_medrs_id_ran)
       apply (metis (mono_tags, lifting) CollectI SND.rep_eq assms(1) inv_rev_rev)
      apply (simp add: assms(2) medsr_eleI)
     apply (simp add: rcv_uspec_ele2)
    apply (simp add: assms(3) medrs_eleI)
   apply (simp add: id_uspec_ele2)
  by blast

paragraph \<open>innerABP Feedback\<close>


paragraph \<open>ABPBundleHelper_ext\<close>

lemma ABPBundleHelper_ext_ubWell: "ubWell (ABPBundleHelper_ext se ora1 ora2 tb x)"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)

lemma ABPBundleHelper_ext_ubWell2: "\<And> x. ubWell (ABPBundleHelper_ext se ora1 ora2 tb x)"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)


lemma ABPBundleHelper_ext_ubWellI: assumes "ubWell x"
  shows "ubWell (ABPBundleHelper_ext se ora1 ora2 tb (Abs_ubundle x))"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)

lemma ABPBundleHelper_ext_dom: "dom (ABPBundleHelper_ext s ora1 ora2 tb x)  = {c_ds, c_dr, c_ar, c_idOut, c_as, c_abpOut}"
  by auto

lemma ABPBundleHelper_ext_chain: assumes "chain Y"
  shows "chain (\<lambda> i. Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb (Y i)))"
  apply (rule chainI)
  apply (rule ub_below)
   apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
  apply (simp add: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
  apply (simp add: assms monofun_cfun_arg po_class.chainE) 
  apply (simp add: assms monofun_cfun_arg monofun_cfun_fun po_class.chainE)
  apply rule + apply simp
  apply (meson assms fst_monofun monofun_cfun_arg po_class.chainE)
  apply rule + apply simp
  by (simp add: assms monofun_cfun_arg po_class.chainE snd_monofun)

paragraph \<open>fixABPHelper_ext\<close>
lemma fixABPHelper_ext_dom:  assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ubDom\<cdot>(fixABPHelper_ext s ora1 ora2 tb x) = {c_ds, c_dr, c_ar, c_idOut, c_abpOut, c_as}"
    apply (subst ubdom_ubrep_eq)
    using ABPBundleHelper_ext_ubWell apply blast
    apply (simp add: domIff)
    by blast

lemma fixABPHelper_ext_cont_h: assumes "chain Y"
  shows "Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb (Y i)))"
proof -
  have f1: "\<And>c::channel. c \<in> ubDom\<cdot>(Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb (\<Squnion>i::nat. Y i))) \<Longrightarrow> 
  (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb (Y i)))  .  c = 
  (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb (Y i))  .  c)"
    apply (subst ubgetch_lub)
      apply (simp add: ABPBundleHelper_ext_chain assms)
     apply (subst ubdom_lub2)
      apply (simp add: ABPBundleHelper_ext_chain assms)
     apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
    by (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
  show ?thesis
    apply (rule ub_below)
     apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
    apply (subst ubdom_lub2)
      apply (simp add: ABPBundleHelper_ext_chain assms)
     apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
    apply (subst f1)
    apply (simp add: assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
    using assms apply (simp add: ABPBundleHelper_ext_dom)
    apply rule + apply simp          
     apply (simp add: contlub_cfun_arg)
    apply (rule) + apply (simp)
     apply (simp add: contlub_cfun_arg)
     apply (subst contlub_cfun_fun)
      apply (rule chainI)
      apply (simp add:  monofun_cfun_arg po_class.chainE)
     apply (subst contlub_cfun_arg)
      apply (rule chainI)
      apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE, simp)
    apply (rule) + apply (simp)
     apply (simp add:  ABPBundleHelper_ext_dom recvCH1_contlub to_recvch1)
    apply (rule) + apply (simp)
     apply (simp add:  ABPBundleHelper_ext_dom recvCH2_contlub to_recvch2)
    apply (rule) + apply (simp)
    apply (simp add: medh_contlub to_medh)
    apply (rule) + apply (simp)
    by (simp add: contlub_cfun_arg)
qed

lemma fixABPHelper_ext_cont:  assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "cont (fixABPHelper_ext s ora1 ora2 tb)"
  apply (rule contI2)
   apply (rule monofunI)
   apply (rule ub_below)
    apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
  apply (simp add: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
   apply (simp add: monofun_cfun_arg monofun_cfun_fun cont_pref_eq1I fst_monofun snd_monofun)
  by (simp add: fixABPHelper_ext_cont_h)



lemma ABPBundleHelper_ext_ubwell1: "ubWell (ABPBundleHelper_ext s ora1 ora2 tb
                                       (Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)))"
    by (simp add: ABPBundleHelper_ext_ubWell)

lemma ABPBundleHelper_ext_ubwell2: "ubWell (ABPBundleHelper_ext s ora1 ora2 tb 
        (Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb 
        (Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)))))"
    by (simp add: ABPBundleHelper_ext_ubWell)

lemma fixABPHelperCont_ext_apply_0: "iterate 0\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>x = x"
  by simp

lemma fixABPHelperCont_ext_apply: "iterate (Suc n)\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>x = 
  (fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(iterate n\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>x)"
  by simp

lemma fixABPHelper_ext_chain:   assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "chain (\<lambda> i. iterate i\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
  apply (rule ub_iterate_chain)
  apply(simp add: ubclDom_ubundle_def ubclLeast_ubundle_def)
  apply (simp add: fixABPHelper_ext_cont assms)
  apply (subst ubdom_ubrep_eq)
   apply (simp add: ubWell_def)
   apply (simp add: usclOkay_tstream_def)
   apply (simp add: tsmap_tsdom_range)
  by (simp add: insert_commute)

lemma fixABPHelperCont_ext_iter_dom:assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ubDom\<cdot>(iterate i\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) = {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"
proof -
  have f1: "(iterate 0\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) = ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"
    by (simp add: fixABPHelperCont_ext_apply_0)
  have f2: "ubDom\<cdot>(iterate i\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) = 
ubDom\<cdot>(iterate 0\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
    apply (rule ubdom_chain_eq3)
    apply (rule fixABPHelper_ext_chain)
    by (simp_all add: assms)
  show ?thesis
    apply (simp add: f2)
    apply (fold ubclDom_ubundle_def)
    by (simp add: ubcldom_least_cs)
qed

lemma fixABPHelperCont_ext_ubFix_dom: assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ubDom\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})
=  {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"
  apply (simp add: ubFix_def)
  apply (subst ubdom_lub2)
   apply (simp add: fixABPHelper_ext_chain assms)
  by (simp add: fixABPHelperCont_ext_iter_dom assms)
                          
paragraph \<open>fixABPHlperCont iter step\<close>
lemma fixABPHelperCont_ext_iter_1:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc n)\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_ds = 
tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((iterate n\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_as)))"
  apply (simp add: fixABPHelperCont_ext_apply)
  apply (simp add: fixABPHelper_ext_cont assms)
  apply (subst ubgetch_ubrep_eq)
   apply (simp add: ABPBundleHelper_ext_ubWell)
  by simp

lemma fixABPHelperCont_ext_iter_2:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc n))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_dr = 
(\<lambda> x. tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1)) (iterate (Suc n)\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc n)\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc n))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (simp only: fixABPHelperCont_ext_iter_1 assms)
    apply (simp add: fixABPHelper_ext_cont assms)
    apply (subst ubgetch_ubrep_eq)
     apply (simp add: ABPBundleHelper_ext_ubWell)
    apply simp
    apply (simp only: iterate2_def)
    by (simp only: fixABPHelperCont_ext_iter_1 assms)
qed

lemma fixABPHelperCont_ext_iter_3_c_ar:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_ar = 
    (\<lambda> x. tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))) 
      (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (fold iterate2_def)
    apply (simp add: fixABPHelper_ext_cont assms)
    by (simp add: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
qed


lemma fixABPHelperCont_ext_iter_3_c_abpOut:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_abpOut = 
    (\<lambda> x. tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))) 
      (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (fold iterate2_def)
    apply (simp add: fixABPHelper_ext_cont assms)
    by (simp add: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
qed

lemma fixABPHelperCont_ext_iter_4_c_idOut:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_idOut = 
tsMap Data\<cdot>(tsMap invData\<cdot>(tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((iterate n\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_as)))))\<cdot>ora1)))))))"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (simp add: fixABPHelper_ext_cont assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
    apply simp
    apply (simp only: iterate2_def)
    apply (simp only: fixABPHelperCont_ext_iter_3_c_abpOut assms)
    apply (simp only: fixABPHelperCont_ext_iter_2 assms)
    by (simp only: fixABPHelperCont_ext_iter_1 assms)
qed

lemma fixABPHelperCont_ext_iter_4_c_idOut2:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_idOut = 
tsMap Data\<cdot>(tsMap invData\<cdot>((iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_abpOut))"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (fold iterate2_def)
    apply (simp add: fixABPHelper_ext_cont assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
    by simp
qed

lemma fixABPHelperCont_ext_iter_4_c_as2:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_as = 
          tsMap (Bool::bool \<Rightarrow> 'a MABP)\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_ar))\<cdot>ora2)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (fold iterate2_def)
    apply (simp add: fixABPHelper_ext_cont assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
    by simp
qed

lemma fixABPHelperCont_ext_iter_4_c_as:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) . c_as = 
 tsMap (Bool::bool \<Rightarrow> 'a MABP)\<cdot>
             (tsMed\<cdot>(tsMap invBool\<cdot>
                     (tsMap (Bool::bool \<Rightarrow> 'a MABP)\<cdot>
                      (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>
                                   (tsMap BoolPair\<cdot>
                                    (tsMed\<cdot>(tsMap invBoolPair\<cdot>
                                            (tsMap BoolPair\<cdot>
                                             (se\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>
                                              (tsMap invBool\<cdot>((iterate n\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)  .  c_as)))))\<cdot>
                                     ora1)))))))\<cdot>
              ora2)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont_ext se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_ext_apply)
  show ?thesis
    apply (subst f1)
    apply (simp add: fixABPHelper_ext_cont assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ext_ubWell)
    apply simp
    apply (simp only: iterate2_def)
    apply (simp only: fixABPHelperCont_ext_iter_3_c_ar assms)
    apply (simp only: fixABPHelperCont_ext_iter_2 assms)
    by (simp only: fixABPHelperCont_ext_iter_1 assms)
qed

paragraph \<open>ABPBundleHelper\<close>

lemma ABPBundleHelper_ubWell: "ubWell (ABPBundleHelper se ora1 ora2 tb x)"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)

lemma ABPBundleHelper_ubWell2: "\<And> x. ubWell (ABPBundleHelper se ora1 ora2 tb x)"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)


lemma ABPBundleHelper_ubWellI: assumes "ubWell x"
  shows "ubWell (ABPBundleHelper se ora1 ora2 tb (Abs_ubundle x))"
  apply(simp add: ubWell_def)
  apply(simp add: usclOkay_tstream_def)
  by (simp_all add: tsmap_tsdom_range)

lemma ABPBundleHelper_dom: "dom (ABPBundleHelper s ora1 ora2 tb x)  = {c_ds, c_dr, c_ar, c_as, c_abpOut}"
  by auto

lemma ABPBundleHelper_chain: assumes "chain Y"
  shows "chain (\<lambda> i. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))"
  apply (rule chainI)
  apply (rule ub_below)
   apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
  apply (simp add: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
  apply (simp add: assms monofun_cfun_arg po_class.chainE) 
  apply (simp add: assms monofun_cfun_arg monofun_cfun_fun po_class.chainE)
  apply rule + apply simp
  apply (meson assms fst_monofun monofun_cfun_arg po_class.chainE)
  apply rule + apply simp
  by (simp add: assms monofun_cfun_arg po_class.chainE snd_monofun)

lemma ABPBundleHelper_getch: "Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x)  .  c = 
(ABPBundleHelper s ora1 ora2 tb x)\<rightharpoonup>c"
proof -
  obtain helper where helper_def: "helper = (ABPBundleHelper s ora1 ora2 tb x)"
    by simp
  have f1: "ubWell helper"
    apply (simp add: helper_def)
    by (simp only: ABPBundleHelper_ubWell)
  show ?thesis
    apply (fold helper_def)
    apply (simp add: ubgetch_insert)
    by (simp add: f1)
qed

paragraph \<open>fixABPHelper\<close>
lemma fixABPHelper_dom:  assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ubDom\<cdot>(fixABPHelper s ora1 ora2 tb x) = {c_ds, c_dr, c_ar, c_abpOut, c_as}"
    apply (subst ubdom_ubrep_eq)
    using ABPBundleHelper_ubWell apply blast
    apply (simp add: domIff)
    by blast

lemma fixABPHelper_cont_h: assumes "chain Y"
  shows "Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))"
proof -
  have f1: "\<And>c::channel. c \<in> ubDom\<cdot>(Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (\<Squnion>i::nat. Y i))) \<Longrightarrow> 
  (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i)))  .  c = 
  (\<Squnion>i::nat. Abs_ubundle (ABPBundleHelper s ora1 ora2 tb (Y i))  .  c)"
    apply (subst ubgetch_lub)
      apply (simp add: ABPBundleHelper_chain assms)
     apply (subst ubdom_lub2)
      apply (simp add: ABPBundleHelper_chain assms)
     apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
    by (simp only: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
  show ?thesis
    apply (rule ub_below)
     apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
    apply (subst ubdom_lub2)
      apply (simp add: ABPBundleHelper_chain assms)
     apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
    apply (subst f1)
    apply (simp add: assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
    using assms apply (simp add: ABPBundleHelper_dom)
    apply rule + apply simp          
     apply (simp add: contlub_cfun_arg)
    apply (rule) + apply (simp)
     apply (simp add: contlub_cfun_arg)
     apply (subst contlub_cfun_fun)
      apply (rule chainI)
      apply (simp add:  monofun_cfun_arg po_class.chainE)
     apply (subst contlub_cfun_arg)
      apply (rule chainI)
      apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE, simp)
    apply (rule) + apply (simp)
     apply (simp add:  ABPBundleHelper_dom recvCH1_contlub to_recvch1)
    apply (rule) + apply (simp)
     apply (simp add:  ABPBundleHelper_dom recvCH2_contlub to_recvch2)
    apply (rule) + apply (simp)
    by (simp add: medh_contlub to_medh)
qed

lemma fixABPHelper_cont:  assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "cont (fixABPHelper s ora1 ora2 tb)"
  apply (rule contI2)
   apply (rule monofunI)
   apply (rule ub_below)
    apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
  apply (simp add: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
   apply (simp add: monofun_cfun_arg monofun_cfun_fun cont_pref_eq1I fst_monofun snd_monofun)
  by (simp add: fixABPHelper_cont_h)


lemma fixABPHelperCont_apply_0: "iterate 0\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>x = x"
  by simp

lemma fixABPHelperCont_apply: "iterate (Suc n)\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>x = 
  (fixABPHelperCont s ora1 ora2 tb)\<cdot>(iterate n\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>x)"
  by simp

lemma fixABPHelper_chain:   assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "chain (\<lambda> i. iterate i\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}))"
  apply (rule ub_iterate_chain)
  apply(simp add: ubclDom_ubundle_def ubclLeast_ubundle_def)
  apply (simp add: fixABPHelper_cont assms)
  apply (subst ubdom_ubrep_eq)
   apply (simp add: ubWell_def)
   apply (simp add: usclOkay_tstream_def)
   apply (simp add: tsmap_tsdom_range)
  by (simp add: insert_commute)

lemma fixABPHelperCont_iter_dom:assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ubDom\<cdot>(iterate i\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})) = {c_abpOut, c_ar, c_as, c_dr, c_ds}"
proof -
  have f1: "(iterate 0\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})) = ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}"
    by (simp add: fixABPHelperCont_apply_0)
  have f2: "ubDom\<cdot>(iterate i\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})) = 
ubDom\<cdot>(iterate 0\<cdot>(fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}))"
    apply (rule ubdom_chain_eq3)
    apply (rule fixABPHelper_chain)
    by (simp_all add: assms)
  show ?thesis
    apply (simp add: f2)
    apply (fold ubclDom_ubundle_def)
    by (simp add: ubcldom_least_cs)
qed

lemma fixABPHelperCont_ubFix_dom: assumes "s \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "ubDom\<cdot>(ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})
=  {c_abpOut, c_ar, c_as, c_dr, c_ds}"
  apply (simp add: ubFix_def)
  apply (subst ubdom_lub2)
   apply (simp add: fixABPHelper_chain assms)
  by (simp add: fixABPHelperCont_iter_dom assms)

paragraph \<open>fixABPHlperCont iter step\<close>
lemma fixABPHelperCont_iter_1:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc n)\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) . c_ds = 
tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((iterate n\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) . c_as)))"
  apply (simp add: fixABPHelperCont_apply)
  apply (simp add: fixABPHelper_cont assms)
  apply (subst ubgetch_ubrep_eq)
   apply (simp add: ABPBundleHelper_ubWell)
  by simp

lemma fixABPHelperCont_iter_2:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc n))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) . c_dr = 
(\<lambda> x. tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1)) (iterate (Suc n)\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc n)\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc n))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_apply)
  show ?thesis
    apply (subst f1)
    apply (simp only: fixABPHelperCont_iter_1 assms)
    apply (simp add: fixABPHelper_cont assms)
    apply (subst ubgetch_ubrep_eq)
     apply (simp add: ABPBundleHelper_ubWell)
    apply simp
    apply (simp only: iterate2_def)
    by (simp only: fixABPHelperCont_iter_1 assms)
qed

lemma fixABPHelperCont_iter_3_c_ar:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) . c_ar = 
    (\<lambda> x. tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))) 
      (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_apply)
  show ?thesis
    apply (subst f1)
    apply (fold iterate2_def)
    apply (simp add: fixABPHelper_cont assms)
    by (simp add: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
qed


lemma fixABPHelperCont_iter_3_c_abpOut:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) . c_abpOut = 
    (\<lambda> x. tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr))))) 
      (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc n))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_apply)
  show ?thesis
    apply (subst f1)
    apply (fold iterate2_def)
    apply (simp add: fixABPHelper_cont assms)
    by (simp add: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
qed


lemma fixABPHelperCont_iter_4_c_as:   assumes "se \<in> tsSender" and "(#({True} \<ominus> ora1) = \<infinity>)"
  and "(#({True} \<ominus> ora2) = \<infinity>)"
shows"(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) . c_as = 
 tsMap (Bool::  bool \<Rightarrow> 'a MABP)\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>
                      (tsMap (Bool::  bool \<Rightarrow> 'a MABP)\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>
                                              (tsMap BoolPair\<cdot>
                                               (tsMed\<cdot>(tsMap invBoolPair\<cdot>
                                                       (tsMap BoolPair\<cdot>(se\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper se ora1 ora2 tb x))\<cdot>x  .  c_as)))))\<cdot>
                                                ora1)))))))\<cdot>
                ora2)"
proof -
  obtain iterate2 where iterate2_def: "iterate2 =  (iterate (Suc (Suc (Suc n)))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x)"
    by simp
  have f1: "(iterate (Suc (Suc (Suc (Suc n))))\<cdot>(fixABPHelperCont se ora1 ora2 tb)\<cdot>x) =
(fixABPHelperCont se ora1 ora2 tb)\<cdot>iterate2"
    apply (simp only: iterate2_def)
    by (simp only:fixABPHelperCont_apply)
  show ?thesis
    apply (subst f1)
    apply (simp add: fixABPHelper_cont assms)
    apply (simp only: ubgetch_ubrep_eq ABPBundleHelper_ubWell)
    apply simp
    apply (simp only: iterate2_def)
    apply (simp only: fixABPHelperCont_iter_3_c_ar assms)
    apply (simp only: fixABPHelperCont_iter_2 assms)
    by (simp only: fixABPHelperCont_iter_1 assms)
qed
(* ----------------------------------------------------------------------- *)
section \<open>Result\<close>
(* ----------------------------------------------------------------------- *)
lemma abpcomp_f_ex: assumes "f \<in> Rep_rev_uspec speccompABP" 
  shows "\<exists> s. \<exists>ora1 ora2. s \<in> tsSender \<and> #({True} \<ominus> ora1)=\<infinity> \<and>  #({True} \<ominus> ora2)=\<infinity> \<and>
    (f =  (ufunclFeedbackComp (ufunclSerComp (ufunclSerComp (ufunclSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
          (ufunclParComp (medRS_TSPF ora2) idTSPF3))))"
proof -
  have f20: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)) \<and> f2\<in>(Rep_rev_uspec MEDSR)}"
    by (simp add: snd_medsr_sercomp_well)
  have f21: "uspecSerComp SND MEDSR = Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec SND) \<and> f2\<in>(Rep_rev_uspec MEDSR)}"
    by (simp add: uspecSerComp_def)
  have f3: "uspec_sercompwell (SND \<circle> MEDSR) (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    by (simp add: snd_medsr_rcv_sercomp_well)
  have f30: "uspecWell {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND \<circle> MEDSR)) \<and> f2\<in>(Rep_rev_uspec (RCV:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))}"
    by (simp add: f3)
  have f31: "uspecSerComp (SND \<circle> MEDSR) RCV = 
      Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec (SND \<circle> MEDSR)) \<and> f2\<in>(Rep_rev_uspec RCV)}"
    using uspecSerComp_def by blast
  have f40: "uspecWell {ufunclParComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec MEDRS) \<and> f2\<in>(Rep_rev_uspec (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec))}"
    by (simp add: medrs_id_parcomp_well)
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
    using f90 medrs_id_parcomp_well uspec_parcomp_consistent2 by auto
  have f92: "uspecIsConsistent ((SND \<circle> MEDSR)::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
        \<and> uspecIsConsistent (RCV:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f31 f3 uspec_sercomp_consistent2 f90 by blast
  have f93: "uspecIsConsistent (SND:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec) 
        \<and> uspecIsConsistent (MEDSR:: (('a MABP tstream\<^sup>\<Omega>) ufun) uspec)"
    using f92 uspec_sercomp_consistent2 by blast
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
    by (metis medrs_id_parcomp_well f2_f3_def ufunclParComp_ufun_def uspec_parcomp_ele_ex)
  have f101: " f4 \<in> Rep_rev_uspec (SND \<circle> MEDSR)"
    by (simp add: f4_f5_def)
  have f102: "SND \<circle> (MEDSR::('a MABP tstream\<^sup>\<Omega>) ufun uspec) 
    = Abs_rev_uspec {ufunclSerComp f1 f2 | f1 f2. f1 \<in> Rep_rev_uspec SND \<and> f2 \<in> Rep_rev_uspec MEDSR}"
    by (simp add: f21)
  obtain f8 f9 where f8_f9_def: "f4 = ufSerComp f8 f9 \<and> f8 \<in> Rep_rev_uspec SND 
      \<and> f9 \<in> Rep_rev_uspec MEDSR"
    by (metis snd_medsr_sercomp_well f4_f5_def f92 ufunclSerComp_ufun_def uspec_sercomp_ele_ex)
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
  have f203: "f7 = idTSPF3"
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

lemma tsabs_map_snth: assumes "Fin n < #(tsAbs\<cdot>s)" shows "snth n (tsAbs\<cdot>(tsMap f\<cdot>s)) = f (snth n (tsAbs\<cdot>(s)))"
proof - 
  have "(tsAbs\<cdot>(tsMap f\<cdot>s)) = smap f\<cdot>(tsAbs\<cdot>(s))"
    apply(simp add: tsabs_insert tsmap_insert)
    by (simp add: tsmap_h_well tsproj_tsabs_h)
  thus ?thesis
    by (simp add: smap_snth_lemma assms)
qed

lemma tsAbs_data_eq: assumes "tsAbs\<cdot>(s) = tsAbs\<cdot>(tsMap invData\<cdot>(s2))" and "tsDom\<cdot>s2 \<subseteq> range Data" shows "tsAbs\<cdot>(tsMap Data\<cdot>s) = tsAbs\<cdot>s2"
proof - 
  have f0: "\<And>s. invData(Data s) = s"
    by simp
  have f1: " #(tsAbs\<cdot>s) = #(tsAbs\<cdot>s2)"
    using assms(1) by simp
  show ?thesis
    apply(subst snths_eq, simp_all)
    apply(simp add: f1)
    apply rule+
  proof - 
    fix n
    assume fin: "Fin n < #(tsAbs\<cdot>s)"

    obtain a where f2: "snth n (tsAbs\<cdot>s2) = Data a"
      using assms(2) f1 fin
      by (metis (mono_tags, lifting) f_inv_into_f snth2sdom subset_iff tsabs_tsdom)
    hence f21: "snth n (tsAbs\<cdot>(tsMap invData\<cdot>(s2))) = a"
      using fin by (simp add: tsabs_map_snth f1)
    
    have f3: "snth n (tsAbs\<cdot>s) = a"
      using f2 assms by (simp add: f21)
    hence f4: "snth n (tsAbs\<cdot>(tsMap Data\<cdot>s)) = Data a"
      using tsabs_map_snth fin by blast

    show "snth n (tsAbs\<cdot>(tsMap Data\<cdot>s)) = snth n (tsAbs\<cdot>s2)"
      using f2 f4 by auto
  qed
qed

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

lemma abp_speccomp_final: assumes "f \<in> Rep_rev_uspec speccompABP"
                            and "ubDom\<cdot>tb = {c_abpIn}"
  shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_idOut) = tsAbs\<cdot>(tb . c_abpIn)"
proof - 
  have f1: "\<exists> s. \<exists>ora1 ora2. s \<in> tsSender  \<and> (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
          (ufParComp (medRS_TSPF ora2) idTSPF3))))"
    by (metis abpcomp_f_ex ufunclFeedbackComp_ufun_def ufunclSerComp_ufun_def ufunclParComp_ufun_def assms(1)) 
  then obtain s where f12: "(s \<in> tsSender) \<and> (\<exists> ora1 ora2. (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3)))))"
    using f1 by blast
  then obtain ora1  where f13: "(#({True} \<ominus> ora1) = \<infinity>) \<and> (\<exists> ora2. (#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3)))))"
    using f1 by blast
  then obtain ora2  where f14: "(#({True} \<ominus> ora2) = \<infinity>) \<and>
     (f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3))))"
    using f1 by blast
  then have f15: "(f =  (\<mu>(ufSerComp (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3))))"
    using f1 by blast

(*===============================================================================================*)
  have f100: "medRS_TSPF ora2 \<in> Rep_rev_uspec (MEDRS:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
    using f14 medrs_rev_insert by blast
  have f101: "idTSPF3 \<in> Rep_rev_uspec (ID:: ('a MABP tstream\<^sup>\<Omega>) ufun uspec)"
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

  have f20: "ufDom\<cdot>(innerABP s ora1 ora2) = {c_abpIn, c_as}"
    by (simp add: f12 f13 f14 innerABP_dom)
  have f21: "ufRan\<cdot>(innerABP s ora1 ora2) = {c_idOut, c_as}"
    by (simp add: f12 f13 f14 innerABP_ran)

  have f2: "(f \<rightleftharpoons> tb) . c_idOut =  (ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as})  .  c_idOut"
    apply(subst f15)
    apply(simp add: ufFeedbackComp_def)
    apply(simp add: ufFeedbackComp_cont ufFeedbackComp_well)
    apply(simp add: f20 f21 assms ubclDom_ubundle_def)
    by (simp add: insert_Diff_if)

  have f105: "(ufSerComp (senderTSPF s) (medSR_TSPF ora1)) 
    \<in> Rep_rev_uspec ((SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<circle> MEDSR)"
    by (metis f103 f104 snd_medsr_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_h1)
  have f106: "(ufParComp (medRS_TSPF ora2) idTSPF3) \<in>
                         Rep_rev_uspec ((MEDRS::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<parallel> ID)"
    apply (simp add: uspecParComp_def)
    apply (subst rep_abs_uspec)
     apply (simp add: medrs_id_parcomp_well)
    apply (simp add: inv_rev_rev)
    by (metis f100 f101 ufunclParComp_ufun_def)
  have f107: "(ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) \<in>
    Rep_rev_uspec (((SND::('a MABP tstream\<^sup>\<Omega>) ufun uspec) \<circle> MEDSR) \<circle> RCV)"
    by (metis f102 f105 snd_medsr_rcv_sercomp_well ufunclSerComp_ufun_def uspec_sercomp_not_empty)

  have f111: "sercomp_well (senderTSPF s) (medSR_TSPF ora1)"
    apply (fold ufunclSerCompWell_ufun_eq)
    using f103 f104 snd_medsr_sercomp_well uspec_sercompwell_def by blast
  have f112: "sercomp_well (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF"
    apply (fold ufunclSerCompWell_ufun_eq)
    using f102 f105 snd_medsr_rcv_sercomp_well uspec_sercompwell_def by blast
  have f113: "sercomp_well (ufSerComp (ufSerComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (ufParComp (medRS_TSPF ora2) idTSPF3)"
    apply (fold ufunclSerCompWell_ufun_eq)
    using f106 f107 snd3_medsr3_rcv3_medrs3_id_sercomp_well uspec_sercompwell_def by blast

  have f98: "ufDom\<cdot>(innerABP s ora1 ora2) = ufDom\<cdot>(senderTSPF s)"
    by (simp add: f20 insert_commute sender_tspfdom)
  have f400: "ufRan\<cdot>(innerABP s ora1 ora2) = {c_as, c_idOut}"
    by (simp add: f21 insert_commute)


  have f690: "ubWell [c_abpIn \<mapsto> tb  .  c_abpIn, c_as \<mapsto> \<bottom>]"
    apply (simp add: ubWell_def)
    apply (simp add: usclOkay_tstream_def)
    by (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
  have f691: "ubDom\<cdot>(Abs_ubundle [c_abpIn \<mapsto> tb  .  c_abpIn, c_as \<mapsto> \<bottom>]) = {c_as, c_abpIn}"
    by (simp add: f690 ubdom_ubrep_eq)
  have f6980: "ubclRestrict {c_as, c_abpIn}\<cdot>(ubclUnion\<cdot>tb\<cdot>(ubclLeast {c_idOut, c_as})) = Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> \<bottom>]"
    apply (simp add: ubclRestrict_ubundle_def ubclUnion_ubundle_def ubclLeast_ubundle_def)
    apply (simp add: ubunion_ubrestrict3)
     apply (simp add: ubrestrict_ubdom_sub assms(2))
    apply (simp add: ubrestrict_ubleast_inter)
    apply (rule ub_eq)
     apply (simp add: assms(2))
     apply (simp add: f690 ubdom_ubrep_eq)
    apply (simp add: assms(2))
    apply auto
    by (simp add: f690 ubgetch_ubrep_eq) +

  have f701: "(iterate (Suc 0)\<cdot>(ufFeedH (innerABP s ora1 ora2) tb)\<cdot>(ubclLeast {c_idOut, c_as})) = 
(ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> \<bottom>])))))\<cdot>
           ((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> \<bottom>]))))))"
    apply (simp add: ufFeedH_def)
    apply (subst Abs_cfun_inverse2)
    using ufFeedH_cont1 apply blast
    apply (simp add: innerABP_dom f12 f13 f14)
    apply (fold f6980)
    apply (subst innerABP_applyI)
    apply (metis bot_set_def f691 f6980 insert_commute)
       apply (simp add: f12)
      apply (simp add: f13)
     apply (simp add: f14)
    by (simp add: insert_commute)


  have f704: "\<And> ub. ubDom\<cdot>ub = {c_as, c_abpIn} \<Longrightarrow> ((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ub ))))) . c_idOut
 = tsMap Data\<cdot>(tsMap invData\<cdot>(tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(ub  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>(ub  .  c_as)))))\<cdot>ora1)))))))"
    apply (simp add: senderTSPF_def)
    apply (simp add: ubclDom_ubundle_def)
    apply (simp add: med_TSPF_def)
    apply (subst rep_abs_cufun)
      apply simp
     apply (simp add: f13 med_ora_length)
    apply (simp add:  ubdom_ubrep_eq ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
    apply (simp add: recvTSPF_def)
    apply (simp add: ubclDom_ubundle_def)
    apply (simp add:  ubdom_ubrep_eq ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
    apply (simp add:  ubgetch_ubrep_eq ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
    apply (simp add: idTSPF3_dom ubclRestrict_ubundle_def)
    apply (simp add: ubrestrict_insert)
    apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
    apply (simp add: idTSPF3_def)
    apply (simp add: idTSPF3_well idTSPF3_cont)
    apply (simp add: ubdom_ubrep_eq ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
    by (simp add: ubgetch_ubrep_eq ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
(*===============================================================================================*)
  paragraph \<open>lub eq proof\<close>
  have fixABPHelperCont_simp: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) =
(\<Squnion>i::nat. iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
    by (simp add: ubFix_def)

  have fixABPHelperCont_simp_dom: "ubDom\<cdot>(\<Squnion>i::nat. iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) = 
              {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"
    apply (fold fixABPHelperCont_simp)
    by (simp add: fixABPHelperCont_ext_ubFix_dom f12 f13 f14)


  have innerABP_fb_simp: "(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as}) = 
  (\<Squnion>i. iterate i\<cdot>(ufFeedH (innerABP s ora1 ora2) tb)\<cdot>(ubclLeast {c_idOut, c_as}))"
    by (simp add: ubFix_def)

  have innerAbp_fb_chain: "chain (\<lambda>i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)"
    apply (rule ub_iterate_chain)
    apply (simp add: ufFeedH_def)
    apply (simp add: ufFeedH_cont1)
    apply (simp add: snd_medsr_rcv_medrs_id_dom f104 f103 rcv_uspec_ele2 f14 medrs_eleI id_uspec_ele2)
    apply (unfold f6980)
    apply (subst ufran_2_ubcldom2) 
     apply (simp add: ubclDom_ubundle_def)
     apply (simp add: f691 f98 sender_tspfdom)
    by (simp add: f21)

  have innerAbp_fb_dom: "ubDom\<cdot>(\<Squnion>i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = {c_idOut, c_as}"
    apply (subst ubdom_lub2)
     apply (simp add: innerAbp_fb_chain)
    apply (fold ubclDom_ubundle_def)
    apply (subst iter_ubfix2_dom)
    apply (subst ufFeedH_dom)
       apply (simp_all add: ubclDom_ubundle_def)
      apply (simp add: innerABP_dom innerABP_ran f12 f13 f14 assms(2))
    apply blast
     apply (fold ubclDom_ubundle_def)
     apply (simp add: ubcldom_least_cs)
    by (simp add: f12 f13 f14 innerABP_ran) +
  have innerAbp_fb_i_dom: "\<And> i. ubDom\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = {c_idOut, c_as}"
    using innerAbp_fb_chain innerAbp_fb_dom ubdom_chain_eq2 by blast
  have innerAbp_fb_i_dom2: "\<And> i. ubDom\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = {c_idOut, c_as}"
    using innerAbp_fb_i_dom ufFeedH_def 
    by (simp add: ufFeedH_def)

  have f7013: "\<And>i . ubWell [
  c_abpIn \<mapsto> tb . c_abpIn,
  c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)) . c_as
]"
    apply (simp add: ubWell_def)
    apply (simp add: usclOkay_tstream_def)
    apply rule
     apply (simp only: ubclUnion_ubundle_def)
     apply (subst ubunion_getchR)
      apply (simp add: innerAbp_fb_i_dom2)
     apply (metis ubgetch_tsmap_idI c_as_bool_ctype f21 f400 innerAbp_fb_i_dom2 insertI1 tsmap_tsdom_range)
    by (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
  have f7014: "\<And>i. ubDom\<cdot>(Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)) . c_as]) = {c_abpIn, c_as}"
    apply (simp add: ubdom_ubrep_eq f7013)
    by blast
  have f7015: "\<And>i .ubDom\<cdot>(ubclRestrict (ufDom\<cdot>(innerABP s ora1 ora2))\<cdot>(ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb))) = {c_abpIn, c_as}"
    apply (simp add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
    apply (simp add: innerAbp_fb_i_dom2 assms)
    by (simp add: innerABP_dom f12 f13 f14)

  have f7012: "\<And> i. ubclRestrict (ufDom\<cdot>(innerABP s ora1 ora2))\<cdot>(ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)) =
Abs_ubundle [
  c_abpIn \<mapsto> tb . c_abpIn,
  c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)) . c_as
]"
    apply (rule ub_eq)
    apply (simp_all add: f7015 f7014)
    apply auto
     apply (simp_all add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
     apply (simp_all add: ubunion_ubrestrict3)
     apply (subst ubunion_getchL)
      apply (simp add: innerAbp_fb_i_dom2)
    apply (simp add: f20)
    apply (subst ubgetch_ubrep_eq)
    apply (fold ubclRestrict_ubundle_def ubclUnion_ubundle_def)
      apply (simp_all add: f7013)
     apply (simp_all add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
    apply (subst ubunion_getchR)
    apply (simp add: innerAbp_fb_i_dom2 f20)
    apply (subst ubgetch_ubrep_eq)
    apply (fold ubclRestrict_ubundle_def ubclUnion_ubundle_def)
     apply (simp_all add: f7013)
     apply (simp_all add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
     by (simp add: innerAbp_fb_i_dom2 f20)

  have f7011: "\<And> i. ufFeedH (innerABP s ora1 ora2) tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = 
(\<Lambda> (z::'a MABP tstream\<^sup>\<Omega>). innerABP s ora1 ora2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>(innerABP s ora1 ora2))\<cdot>(ubclUnion\<cdot>tb\<cdot>z))\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)"
    by (simp add: ufFeedH_def)
  have f7010: "\<And> i. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc i) {c_idOut, c_as} tb = 
(ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)) . c_as]))))))\<cdot>
           ((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)) . c_as])))))))"
    apply (simp)[1]
    apply (simp add: f7011)
    apply (subst Abs_cfun_inverse2)
    using ufFeedH_cont1 apply blast
    apply (simp only: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
    apply (subst innerABP_applyI)
        apply (simp only: ubrestrict_ubdom2 ubunionDom assms)
        apply (fold ubclRestrict_ubundle_def ubclUnion_ubundle_def)
    using innerAbp_fb_i_dom2 innerABP_dom f12 f13 f14 apply blast
       apply (simp_all only: f12 f13 f14)
    by (simp add: f7012)


  obtain abphelper_chain where abphelper_chain_def: "abphelper_chain = (\<lambda> i. (iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})))"
    by simp
  have abphelper_chain_ischain: "chain abphelper_chain"
    apply (simp add:  abphelper_chain_def)
    by (simp add: fixABPHelper_chain f12 f13 f14)
(*
  have abphelper_chain_c_abpOut_eq: "Lub abphelper_chain . c_abpOut = Lub (\<lambda> i. iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})) . c_abpOut"
    apply (simp add: abphelper_chain_def)
    apply (subst ubgetch_lub)
    apply (simp add: ubclRestrict_ubundle_def)
    apply (rule chainI)
    apply (rule ubrestrict_belowI1)
      apply (rule chainE)
    apply (simp_all only: fixABPHelper_chain f12 f13 f14)
     apply (simp add: ubclRestrict_ubundle_def)
    apply (subst ubdom_lub2)
      apply (rule chainI)
      apply (rule ubrestrict_belowI1)
      apply (rule chainE)
      apply (simp only: fixABPHelper_chain f12 f13 f14)
     apply (simp add: fixABPHelperCont_iter_dom f12 f13 f14)
    apply (simp add: ubclRestrict_ubundle_def)
    apply (subst ubgetch_lub)
      apply (simp_all add: fixABPHelper_chain f12 f13 f14)
    by (simp add: ubdom_lub2 fixABPHelper_chain fixABPHelperCont_iter_dom f12 f13 f14)
*)
  obtain abphelper_ext_chain where abphelper_ext_chain_def: "abphelper_ext_chain = (\<lambda> i. ubclRestrict {c_idOut, c_as}\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))"
    by simp
  obtain abphelper_ext_chain_shift where abphelper_ext_chain_shift_def: "abphelper_ext_chain_shift = (\<lambda> i. abphelper_ext_chain (4 * (Suc i)))"
    by simp
  obtain innerABP_chain where innerABP_chain_def: "innerABP_chain = (\<lambda> i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb)"
    by simp
  obtain innerABP_chain_shift where innerABP_chain_shift_def: "innerABP_chain_shift = (\<lambda> i. innerABP_chain (Suc i))"
    by simp 
  have abphelper_ext_chain_ischain: "chain abphelper_ext_chain"
    apply (simp add: abphelper_ext_chain_def)
    apply (simp add: ubclRestrict_ubundle_def)
    apply (rule chainI)
    apply (rule ubrestrict_belowI1)
    apply (rule chainE)
    apply (subst fixABPHelper_ext_chain)
    by (simp_all add: f12 f13 f14)
  have abphelper_ext_chain_shift_ischain: "chain abphelper_ext_chain_shift"
    apply (rule chainI)
    apply (simp add: abphelper_ext_chain_shift_def)
    apply (rule chain_mono_less)
     apply (simp add: abphelper_ext_chain_ischain)
    apply (induct_tac i)
     apply simp
    by simp

  have abphelper_ext_chain_shift_in_range : "\<And> i . abphelper_ext_chain_shift i \<in> range abphelper_ext_chain"
    by (simp add: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
  have abphelper_ext_chain_shift_lub_eq: "Lub abphelper_ext_chain = Lub abphelper_ext_chain_shift"
    apply (subst po_eq_conv) apply rule
     apply (rule lub_mono)
       apply (simp_all add: abphelper_ext_chain_shift_ischain abphelper_ext_chain_ischain)
     apply (simp add: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
     apply (rule chain_mono)
      apply (fold abphelper_ext_chain_def)
      apply (simp add: abphelper_ext_chain_ischain)
     apply (induct_tac i)
    by (simp add: abphelper_ext_chain_ischain abphelper_ext_chain_shift_ischain cpo is_ub_thelub_ex abphelper_ext_chain_shift_in_range lub_below) +

  have innerABP_chain_ischain: "chain innerABP_chain"
    apply (simp add: innerABP_chain_def)
    by (simp add: innerAbp_fb_chain)
  have innerABP_chain_shift_ischain: "chain innerABP_chain_shift"
    using innerABP_chain_ischain innerABP_chain_shift_def po_class.chain_def by auto

  have innerABP_chain_eq: "Lub innerABP_chain = Lub innerABP_chain_shift"
    apply (subst po_eq_conv) apply rule
    using innerABP_chain_ischain innerABP_chain_shift_def innerABP_chain_shift_ischain lub_mono po_class.chain_def apply auto[1]
    by (metis cpo innerABP_chain_ischain innerABP_chain_shift_def innerABP_chain_shift_ischain is_lub_rangeD1 lub_below lub_eqI)

  have four_times_simp_suc: "\<And> i. 4 * (Suc i) = (Suc (Suc (Suc (Suc (4 * i)))))"
    by simp
  have four_times_zero: "4 * (0::nat) = 0"
    by simp
  have chain_eq_proof: "Lub abphelper_ext_chain_shift = Lub innerABP_chain_shift"
    apply (rule lub_eq)
  proof (induct_tac i)
    fix i::nat 
    have f1: "ubDom\<cdot>(ubclRestrict {c_idOut, c_as}\<cdot>(iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))) = {c_idOut, c_as}"
      apply (simp only: ubclRestrict_ubundle_def)
      apply (simp only: ubrestrict_ubdom2)
      apply (subst fixABPHelperCont_ext_iter_dom)
      by (simp_all add: f12 f13 f14)

      have f1200: "(iterate (Suc 0)\<cdot>(ufFeedH (innerABP s ora1 ora2) tb)\<cdot>(ubclLeast {c_idOut, c_as})) = ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ubclLeast {c_idOut, c_as})"
        by simp
      have f1300: "(iterate (Suc 0)\<cdot>(ufFeedH (innerABP s ora1 ora2) tb)\<cdot>(ubclLeast {c_idOut, c_as})) = ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ubclLeast {c_idOut, c_as})"
        by simp
    have f1401: "iterate 0\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) = (ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
      by simp
    have f1402: "iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) =
(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>
    ((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>
     ((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))))"
      by simp
    have f1403: "iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc (0::nat)) {c_idOut, c_as} tb = 
(ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) 0 {c_idOut, c_as} tb)) . c_as]))))))\<cdot>
           ((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) 0 {c_idOut, c_as} tb)) . c_as])))))))"
      by (simp only: f7010)
    have f14000: "ubWell [c_abpIn \<mapsto> tb  .  c_abpIn, c_as \<mapsto> ubclUnion\<cdot>tb\<cdot>(ubclLeast {c_idOut, c_as})  .  c_as]"
      apply (simp add: ubWell_def)
      apply (simp add: usclOkay_tstream_def)
      apply (simp add: ubclUnion_ubundle_def)
      by (metis assms(2) ubgetch_tsmap_idI c_as_bool_ctype ctype_MABP.simps(1) innerAbp_fb_i_dom2 insert_iff insert_is_Un iterate_0 tsmap_tsdom_range ubunionDom)
    have f14001: "ubclDom\<cdot>(Abs_ubundle [c_abpIn \<mapsto> tb  .  c_abpIn, c_as \<mapsto> ubclUnion\<cdot>tb\<cdot>(ubclLeast {c_idOut, c_as})  .  c_as]) = {c_as, c_abpIn}"
      apply (simp add: ubclDom_ubundle_def)
      by (simp add: f14000 ubdom_ubrep_eq)
    have f1404: "ubclRestrict {c_idOut, c_as}\<cdot>(((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>
              ((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>
            ((\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))))) .  c_idOut =
    ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ubclLeast {c_idOut, c_as})  .  c_idOut"
       apply (fold f1402) 
       apply (fold f1200)
      apply (simp only: f701)
      apply (subst innerABP_ubgetchR)
       apply (fold ubclDom_ubundle_def)
       apply (subst ufran_2_ubcldom2) +
          apply (simp add: ubclDom_ubundle_def)
          apply (simp add: ubdom_ubrep_eq f690)
          apply (simp add: sender_tspfdom)
         apply (simp add: f111)
        apply (subst med_tspfran)
          apply (simp add: f13 med_ora_length)
         apply simp
      apply (simp add: recv_tspfdom)
       apply (simp add: recv_tspfran)
      apply blast
      apply (subst f704)
       apply (subst ubdom_ubrep_eq)
        apply (simp add: ubWell_def)
        apply (simp add: usclOkay_tstream_def)
        apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      apply (simp add: domIff)
       apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubgetch_ubrestrict)
      apply blast
       apply (subst fixABPHelperCont_ext_iter_4_c_idOut)
         apply (simp_all add: f12 f13 f14 ubclLeast_ubundle_def)
      apply (subst ubgetch_ubrep_eq)
        apply (simp add: ubWell_def)
        apply (simp add: usclOkay_tstream_def)
        apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      apply (simp add: domIff)
      apply (subst ubgetch_ubrep_eq)
        apply (simp add: ubWell_def)
        apply (simp add: usclOkay_tstream_def)
        apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      by (simp add: domIff)
    have f14050: "ubclUnion\<cdot>tb\<cdot>(ubclLeast {c_idOut, c_as})  .  c_as = \<bottom>"
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
       apply (fold ubclDom_ubundle_def)
       apply (simp add: ubcldom_least_cs)
      by (simp add: ubclLeast_ubundle_def)
    have f1405: "ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ubclLeast {c_idOut, c_as})  .  c_as =
tsMap (Bool::bool \<Rightarrow> 'a MABP)\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>
                      (tsMap (Bool::bool \<Rightarrow> 'a MABP)\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>
                                              (tsMap BoolPair\<cdot>
                                               (tsMed\<cdot>(tsMap invBoolPair\<cdot>(tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>(tsMap invBool\<cdot>((ubclLeast:: channel set \<Rightarrow> 'a MABP tstream\<^sup>\<Omega>) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}  .  c_as)))))\<cdot>
                                                ora1)))))))\<cdot>
                ora2)"
      apply (fold f1300)
      apply (simp only: f7010)
      apply (subst innerABP_ubgetchL)
       apply (fold ubclDom_ubundle_def)
       apply (subst ufran_2_ubcldom2) +
          apply (metis f20 f7014 f98 ubclDom_ubundle_def)
         apply (simp add: f111)
        apply (simp add: f13 med_tspfran2 recv_tspfdom)
       apply (simp add: insert_commute recv_tspfran)
      apply (simp add: med_tspfdom2 f14 senderTSPF_def)
      apply (simp add: f14001)
      apply (simp add: f14050)
      apply (simp add: ubclLeast_ubundle_def)
      apply (subst medsr_tspf_apply)
        apply (simp add: ubdom_ubrep_eq) defer
       apply (simp add: ubgetch_ubrep_eq)
       apply (subst recvTSPF_apply) defer
        apply (simp add: ubclRestrict_ubundle_def)
        apply (subst ubrestrict_ubrep_eq) defer
         apply (subst medrs_tspf_apply)
           apply (subst ubdom_ubrep_eq) defer defer defer
            apply (subst ubgetch_ubrep_eq) defer
             apply (subst ubgetch_ubrep_eq) defer
             apply (subst ubgetch_ubrep_eq) defer
              apply (subst ubgetch_ubrep_eq) defer
               apply (subst ubgetch_ubrep_eq) defer
               apply simp
              apply (simp add: f13 med_ora_length)
      apply (simp_all add: ubclDom_ubundle_def)
          apply (subst ubdom_ubrep_eq)
          apply (simp_all add: ubWell_def)
         apply (simp_all add: usclOkay_tstream_def)
         apply (simp_all add: tsmap_tsdom_range)
       apply (simp add: f14 med_ora_length)
      by (metis assms(2) ctype_MABP.simps(1) singletonI ubdom_channel_usokay ubgetch_insert usclOkay_tstream_def)
    show "abphelper_ext_chain_shift (0::nat) = innerABP_chain_shift (0::nat)"
      apply (simp only: abphelper_ext_chain_shift_def innerABP_chain_shift_def
                abphelper_ext_chain_def innerABP_chain_def)
      apply (simp only: f1403)
      apply (rule ub_eq)
       apply (simp_all only: f1 four_times_simp_suc four_times_zero)
      apply (fold f1403)
      using innerAbp_fb_chain innerAbp_fb_dom ubdom_chain_eq2 apply blast
       apply (simp del: iterate_Suc) 
      apply auto
      apply (simp add: f1404)
       apply (fold f1402 f1200) 
      apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubgetch_ubrestrict)
      apply blast
      apply (simp only: fixABPHelperCont_ext_iter_4_c_as f12 f13 f14) +
      by (simp add: f1405)
  next
    fix i::nat and n::nat
    assume a1: "abphelper_ext_chain_shift n = innerABP_chain_shift n"
    have f1: "ubDom\<cdot>(ubclRestrict {c_idOut, c_as}\<cdot>(iterate ((4::nat) * Suc (Suc n))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))) = {c_idOut, c_as}"
      apply (simp only: ubclRestrict_ubundle_def)
      apply (simp only: ubrestrict_ubdom2)
      apply (subst fixABPHelperCont_ext_iter_dom)
      by (simp_all add: f12 f13 f14)
    have f2: "ubDom\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc (Suc n)) {c_idOut, c_as} tb) = {c_idOut, c_as}"
      apply (fold ubclDom_ubundle_def)
      apply (simp add: ubclDom_ubundle_def)
      by (metis innerAbp_fb_i_dom2 iterate_Suc)
    have f5: "iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc (Suc n)) {c_idOut, c_as} tb = 
ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ufFeedH (innerABP s ora1 ora2) tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) n {c_idOut, c_as} tb))"
      by simp
    have f6: "iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc n) {c_idOut, c_as} tb = 
(ubclUnion\<cdot>(((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>((medRS_TSPF ora2):: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) n {c_idOut, c_as} tb)) . c_as]))))))\<cdot>
           ((idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(idTSPF3:: ('a MABP tstream\<^sup>\<Omega>) ufun))\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (Abs_ubundle [c_abpIn \<mapsto> tb . c_abpIn, c_as \<mapsto> (ubclUnion\<cdot>tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) n {c_idOut, c_as} tb)) . c_as])))))))"
      using f7010 by blast
    have f7: "(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc n) {c_idOut, c_as} tb) =(ufFeedH (innerABP s ora1 ora2) tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) n {c_idOut, c_as} tb))"
      by simp
    have f8: "innerABP_chain_shift n  = iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) (Suc n) {c_idOut, c_as} tb"
      by (simp add: innerABP_chain_shift_def innerABP_chain_def)
    have f9: "abphelper_ext_chain_shift n = ubclRestrict {c_idOut, c_as}\<cdot>(iterate (4 + (4 * n))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
      apply  (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
      by simp
    have f90: "ubclRestrict {c_idOut, c_as}\<cdot>(iterate (4 + (4 * n))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) . c_as = 
(iterate (4 + (4 * n))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) . c_as"
      apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubgetch_ubrestrict)
      by simp +
    have f91: "4 * (Suc (Suc n)) = (8::nat) + (4::nat) * n"
      by simp
    have f92: "4 * (Suc (Suc n)) = Suc (Suc (Suc (Suc ((4::nat) * (Suc n)))))"
      by simp
    have f10: "(ubclRestrict {c_idOut, c_as}\<cdot>(iterate ((8::nat) + (4::nat) * n)\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))  . 
    c_idOut =
    ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ufFeedH (innerABP s ora1 ora2) tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) n {c_idOut, c_as} tb))  .  c_idOut"
      apply (fold f91)
      apply (simp only: f92)
      apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubgetch_ubrestrict)
       apply blast
      apply (subst fixABPHelperCont_ext_iter_4_c_idOut)
          apply (simp add: f12)
         apply (simp add: f13)
        apply (simp add: f14)
      apply (fold f5)
      apply (simp only: f7010)
      apply (subst innerABP_ubgetchR)
      apply (fold f6)
       apply (fold ubclDom_ubundle_def)
       apply (subst ufran_2_ubcldom2) +
          apply (simp only:  ubclDom_ubundle_def)
      using f20 f7014 f98 apply presburger
         apply (simp add: f111)
        apply (simp add: f13 med_tspfran2 recv_tspfdom)
       apply (simp add: insert_commute recv_tspfran)
      apply (subst senderTSPF_apply)
        apply (simp add: f12)
       apply (simp only: f7014)
      apply (subst medsr_tspf_apply)
        apply (subst ubdom_ubrep_eq)
         apply (simp add: ubWell_def)
         apply (simp add: usclOkay_tstream_def)
         apply (simp add: tsmap_tsdom_range)
        apply simp
       apply (simp add: f13 med_ora_length)
      apply (subst recvTSPF_apply)
       apply (simp add: ubclDom_ubundle_def)
       apply (subst ubdom_ubrep_eq)
        apply (simp add: ubWell_def)
      apply (simp add: usclOkay_tstream_def)
        apply (simp add: tsmap_tsdom_range)
       apply simp
      apply (simp only: idTSPF3_dom)
      apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubrestrict_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply (simp add: tsmap_tsdom_range)
      apply simp
      apply (subst idTSPF3_apply)
      apply (subst ubdom_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
        apply (simp add: tsmap_tsdom_range)
      apply simp
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply (simp add: tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply (simp add: tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply (simp add: tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply (simp add: tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply rule 
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
         apply (fold f7)
         apply (subst innerAbp_fb_i_dom)
         apply blast
        apply (metis ubgetch_tsmap_idI c_as_bool_ctype innerAbp_fb_i_dom2 insert_subset subset_insertI tsmap_tsdom_range)
      apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def)
       apply (simp add: usclOkay_tstream_def)
       apply rule 
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
         apply (fold f7)
         apply (subst innerAbp_fb_i_dom)
         apply blast
        apply (metis ubgetch_tsmap_idI c_as_bool_ctype innerAbp_fb_i_dom2 insert_subset subset_insertI tsmap_tsdom_range)
       apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      apply simp
         apply (fold f7)
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
         apply (fold f7)
       apply (subst innerAbp_fb_i_dom)
       apply simp
      apply (fold f8)
      apply (fold a1)
      apply (simp only: f9)
      by (simp only: f90)
    have f11: "(ubclRestrict {c_idOut, c_as}\<cdot>(iterate ((8::nat) + (4::nat) * n)\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))  . 
    c_as =
    ufFeedH (innerABP s ora1 ora2) tb\<cdot>(ufFeedH (innerABP s ora1 ora2) tb\<cdot>(iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) n {c_idOut, c_as} tb))  .  c_as"
      apply (fold f91)
      apply (simp only: f92)
      apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubgetch_ubrestrict)
       apply blast
      apply (subst fixABPHelperCont_ext_iter_4_c_as)
         apply (simp add: f12) apply (simp add: f13) apply (simp add: f14)
      apply (fold f5)
      apply (simp only: f7010)
      apply (subst innerABP_ubgetchL)
       apply (fold f6)
       apply (fold ubclDom_ubundle_def)
       apply (subst ufran_2_ubcldom2) +
          apply (simp only:  ubclDom_ubundle_def)
      using f20 f7014 f98 apply presburger
         apply (simp add: f111)
        apply (simp add: f13 med_tspfran2 recv_tspfdom)
       apply (simp add: insert_commute recv_tspfran)
      apply (subst senderTSPF_apply)
        apply (simp add: f12)
       apply (simp only: f7014)
      apply (subst medsr_tspf_apply)
        apply (simp add: ubdom_ubrep_eq)
       apply (simp add: f13 med_ora_length)
      apply (subst recvTSPF_apply)
       apply (simp add: ubclDom_ubundle_def)
       apply (simp add: ubdom_ubrep_eq)
      apply (subst med_tspfdom)
        apply (simp add: f14 med_ora_length)
       apply simp
      apply (simp only: ubclRestrict_ubundle_def)
      apply (subst ubrestrict_ubrep_eq)
       apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
      apply (subst medrs_tspf_apply)
        apply (subst ubdom_ubrep_eq)
         apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
        apply simp
       apply (simp add: f14 med_ora_length)
      apply (subst ubgetch_ubrep_eq)
       apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
       apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
       apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
       apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
      apply (simp add: ubWell_def)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
       apply rule 
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
         apply (fold f7) apply (subst innerAbp_fb_i_dom) apply blast
        apply (metis ubgetch_tsmap_idI c_as_bool_ctype innerAbp_fb_i_dom2 insert_subset subset_insertI tsmap_tsdom_range)
      apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      apply (subst ubgetch_ubrep_eq)
      apply (simp add: ubWell_def usclOkay_tstream_def tsmap_tsdom_range)
       apply rule 
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
         apply (fold f7) apply (subst innerAbp_fb_i_dom) apply blast
        apply (metis ubgetch_tsmap_idI c_as_bool_ctype innerAbp_fb_i_dom2 insert_subset subset_insertI tsmap_tsdom_range)
       apply (metis assms(2) ubgetch_tsmap_idI ctype_MABP.simps(1) insertI1 tsmap_tsdom_range)
      apply simp
      apply (fold f7)
      apply (simp add: ubclUnion_ubundle_def)
      apply (subst ubunion_getchR)
       apply (fold f7)
       apply (subst innerAbp_fb_i_dom) apply simp
      apply (fold f8)
      apply (fold a1)
      apply (simp only: f9)
      by (simp only: f90)
    show "abphelper_ext_chain_shift (Suc n) = innerABP_chain_shift (Suc n)"
      apply (simp only: abphelper_ext_chain_shift_def innerABP_chain_shift_def
                abphelper_ext_chain_def innerABP_chain_def)
      apply (rule ub_eq)
       apply (simp_all only: f1 f2)
      apply auto[1]
      apply (simp add: f10)
      by (simp add: f11)
  qed
  
(* is_lub_range_shift *)
  have f10000: "ubclRestrict {c_idOut, c_as}\<cdot>(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as}) =
(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as})"
    apply (simp add: ubclRestrict_ubundle_def)
    apply (rule ubrestrict_id)
    apply (fold ubclDom_ubundle_def)
    apply (subst ubfix_dom)
     apply (subst ufFeedH_dom)
       apply (simp_all add: f400 f98 sender_tspfdom assms ubclDom_ubundle_def)
    apply (fold ubclDom_ubundle_def)
     apply (simp add: ubcldom_least_cs)
    by blast +
  have f10001: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut = 
(ubclRestrict {c_idOut, c_as}\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))  .  c_idOut "
    by (simp add: ubclRestrict_ubundle_def)

  have f10002: "(ubclRestrict {c_idOut, c_as}\<cdot>(\<Squnion>i::nat. iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))) = 
(\<Squnion>i::nat. ubclRestrict {c_idOut, c_as}\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))"
    apply (simp add: ubclRestrict_ubundle_def)
    apply (subst ubrestrict_lub)
     apply (subst iter_ubfix2_chain)
      apply (simp add: ubclDom_ubundle_def)
       apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
      apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
    by blast

  have f10004: "(\<Squnion>i::nat. ubclRestrict {c_idOut, c_as}\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))) = 
    Lub abphelper_ext_chain"
    by (simp add: abphelper_ext_chain_def)
  have f10005: "(\<Squnion>i::nat. ubclRestrict {c_idOut, c_as}\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))) = 
    Lub abphelper_ext_chain_shift"
    apply (subst f10004)
    by (simp add: abphelper_ext_chain_shift_lub_eq)
  have f10006: "(\<Squnion>i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = Lub innerABP_chain "
    by (simp add: innerABP_chain_def)
  have f10007: "(\<Squnion>i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = Lub innerABP_chain_shift "
    by (simp add: f10006 innerABP_chain_eq)

  have f10003: " (\<Squnion>i::nat. iter_ubfix2 (ufFeedH (innerABP s ora1 ora2)) i {c_idOut, c_as} tb) = 
(\<Squnion>i::nat. ubclRestrict {c_idOut, c_as}\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))"
    apply (subst f10005)
    apply (subst f10007) 
    by (simp add: chain_eq_proof)

  have f10004: "(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as}) . c_idOut =
(ubclRestrict {c_idOut, c_as}\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))  .  c_idOut "
    apply (simp add: ubFix_def)
    apply (subst f10002)
    by (simp add: f10003)

  have f20000: "ubfun_io_eq (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut))))) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"
      apply (simp add: ubclDom_ubundle_def)
       apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
     apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
    by blast

  have f20001: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) = 
iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
    apply (subst ubfix_eq, simp add: f20000) 
    apply (subst ubfix_eq, simp add: f20000)
    apply (subst ubfix_eq, simp add: f20000)
    apply (subst ubfix_eq, simp add: f20000)
    by simp
  have f20002: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) = 
iterate (Suc (Suc (Suc 0)))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
    apply (subst ubfix_eq, simp add: f20000)
    apply (subst ubfix_eq, simp add: f20000)
    apply (subst ubfix_eq, simp add: f20000)
    by simp

  have f20003: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_idOut = 
(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_abpOut"
  proof -
    have f1: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_idOut = 
iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_idOut"
      apply (subst f20001)
      by simp
    show ?thesis
      apply (subst f1)
      apply (simp only: fixABPHelperCont_ext_iter_4_c_idOut2 f12 f13 f14)
      apply (fold f20002)
      apply (rule ubgetch_tsmap_idI)
        apply (fold ubclDom_ubundle_def)
        apply (subst ubfix_dom)
         apply (simp add: ubclDom_ubundle_def)
         apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
         apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
      by blast +
  qed

  have f20004: "(ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))  .  c_abpOut
 = (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut"
    apply (unfold f20003)
    by (simp add: ubclRestrict_ubundle_def)

  have f20005: "Lub abphelper_chain . c_abpOut = (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut"
  proof -
    have f1: "chain (\<lambda> i. iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}))"
      apply (rule ub_iterate_chain)
      apply (simp add: ubclDom_ubundle_def)
      apply (simp add: fixABPHelper_cont f12 f13 f14)
      apply (simp add: fixABPHelper_dom f12 f13 f14)
      by blast
    have f2: "ubDom\<cdot>(\<Squnion>i::nat. iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})) = {c_abpOut, c_ar, c_as, c_dr, c_ds}"
      apply (subst ubdom_lub2)
      apply (simp add: f1)
      apply (fold ubclDom_ubundle_def)
      apply (subst iter_ubfix2_dom)
       apply (simp_all add: ubclDom_ubundle_def)
      apply (simp add: fixABPHelper_cont f12 f13 f14)
      apply (simp add: fixABPHelper_dom f12 f13 f14)
      by blast
    have f3: "\<And> i. ubDom\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})) = {c_abpOut, c_ar, c_as, c_dr, c_ds}"
      apply (fold ubclDom_ubundle_def)
      apply (subst iter_ubfix2_dom)
       apply (simp_all add: ubclDom_ubundle_def)
      apply (simp add: fixABPHelper_cont f12 f13 f14)
      apply (simp add: fixABPHelper_dom f12 f13 f14)
      by blast

    have f100: "Lub abphelper_chain = (ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
      apply (simp add: ubFix_def)
      apply (simp add: ubclRestrict_ubundle_def)
      apply (subst ubrestrict_lub)
       apply (simp add: fixABPHelper_ext_chain f12 f13 f14)
      apply (simp add: abphelper_chain_def)
      apply (rule lub_eq)
      apply (induct_tac i)
       apply (simp add: ubclLeast_ubundle_def ubrestrict_ubleast_inter)
      apply (fold ubclRestrict_ubundle_def)
    proof -
      fix i::nat and n::nat
      assume a1: "iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}) =
       ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
      obtain n_step where n_step_def: "n_step = iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})"
        by simp
      obtain n_restrict_step where n_restrict_step_def: "n_restrict_step = (iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
        by simp
      have f299: "ubDom\<cdot>(Abs_ubundle (ABPBundleHelper s ora1 ora2 tb n_step)) = {c_abpOut, c_ar, c_as, c_dr, c_ds}"
        apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
        by blast
      have f300: "\<And> c. c \<in> {c_abpOut, c_ar, c_as, c_dr, c_ds} \<Longrightarrow> (ubRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>n_restrict_step) . c = n_restrict_step . c"
        by (simp add: n_restrict_step_def)
      have f301: "n_step= ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>n_restrict_step"
        apply (simp add: n_step_def n_restrict_step_def)
        by (simp add: a1)
      have f302: "\<And> c. c \<in> {c_abpOut, c_ar, c_as, c_dr, c_ds} \<Longrightarrow> n_restrict_step . c = n_step . c"
        by (simp add: f301 ubclRestrict_ubundle_def)
      show "iterate (Suc n)\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}) =
       ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(iterate (Suc n)\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
        apply (simp)
        apply (fold n_step_def)
        apply (fold n_restrict_step_def)
        apply (simp add: fixABPHelper_cont fixABPHelper_ext_cont f12 f13 f14)
        apply (rule ub_eq)
         apply (simp_all only: f299)
        apply (simp add: ubclRestrict_ubundle_def)
         apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
        apply auto
            apply (simp_all add: ubclRestrict_ubundle_def)
            apply (simp_all add: ubgetch_ubrep_eq ABPBundleHelper_ubWell ABPBundleHelper_ext_ubWell)
            by (simp add: f302) +
    qed
    show ?thesis
      apply (fold f20004) 
      by (simp add: f100)
  qed

  have f20006: "Lub abphelper_chain . c_abpOut = (ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})  .  c_abpOut"
    by (simp add: ubFix_def abphelper_chain_def)

  have f3_ext: "(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as})  .  c_idOut = 
 (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut"
    apply (subst f10001)
    by (simp add: f10004)
  have f3: "(ubFix (ufFeedH (innerABP s ora1 ora2) tb) {c_idOut, c_as})  .  c_idOut = 
 (ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})  .  c_abpOut"
    apply (fold f20006)
    apply (simp add: f3_ext)
    by (simp add: f20005)

  have f40: "ubfun_io_eq (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds}"
  proof - 
    have f401: "ubWell [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb  .  c_abpIn))\<cdot>\<bottom>), c_dr \<mapsto> \<bottom>, c_ar \<mapsto> \<bottom>, c_abpOut \<mapsto> \<bottom>, c_as \<mapsto> \<bottom>]"
      apply(simp add: ubWell_def usclOkay_tstream_def)
      using tsmap_tsdom_range by auto
    show ?thesis
      apply(simp add: ubclDom_ubundle_def ubclLeast_ubundle_def)
      apply(simp add:  fixABPHelper_cont assms f12 f13 f14)
      using f401 by (simp add: insert_commute ubdom_ubrep_eq)
  qed
  then have f41: "ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds} =  (fixABPHelperCont s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})"
    using ubfix_eq by blast

  have f42: "\<And>x. ubWell [
      c_ds     \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>(x . c_as))),
      c_dr     \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . c_ds))\<cdot>ora1),
      c_ar     \<mapsto> tsMap Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
      c_abpOut \<mapsto> tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . c_dr)))),
      c_as     \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . c_ar))\<cdot>ora2)
      ]"
    using ABPBundleHelper_ubWell by blast
  (* After proving the fixed points propties we can now show the assumptions of the tsaltbitpro_inp2out lemma
  
    i = (tsMap invData\<cdot>(tb . c_abpIn))
    ds_stream = (tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))
    as_stream = (tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))
   
    have f7: "(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr)) = s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))"
    sorry

    have f8: "(tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar)) = tsProjSnd\<cdot>(tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))"
    sorry
    
       and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"

    i = (tsMap invData\<cdot>(tb . c_abpIn))
    ds = (tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ds))
    dr = (tsMap invBoolPair\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_dr))
    as = (tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_as))
    ar = (tsMap invBool\<cdot>((ubFix (abpFixH s tb) {c_abpOut, c_ar, c_dr}) . c_ar))
  *)
  
  (*abpHelper_ubWell with f42 as x is ubWell*)
  have abpHelper_ubWell2: "ubWell [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot>(tsMap invBool\<cdot>Rep_ubundle
                       (ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).Abs_ubundle
                                  [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_as)),
                                   c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_ds)\<cdot>ora1),
                                   c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_ar)\<cdot>ora2)])
                       {c_abpOut, c_ar, c_as, c_dr, c_ds})\<rightharpoonup>c_as)),
            c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle
                       (ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).Abs_ubundle
                                  [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_as)),
                                   c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_ds)\<cdot>ora1),
                                   c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_ar)\<cdot>ora2)])
                       {c_abpOut, c_ar, c_as, c_dr, c_ds})\<rightharpoonup>c_ds)\<cdot>ora1),
            c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle
                       (ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).Abs_ubundle
                                  [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_as)),
                                   c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_ds)\<cdot>ora1),
                                   c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_ar)\<cdot>ora2)])
                       {c_abpOut, c_ar, c_as, c_dr, c_ds})\<rightharpoonup>c_dr))),
            c_abpOut \<mapsto>tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle
                       (ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).Abs_ubundle
                                  [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_as)),
                                   c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_ds)\<cdot>ora1),
                                   c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_ar)\<cdot>ora2)])
                       {c_abpOut, c_ar, c_as, c_dr, c_ds})\<rightharpoonup>c_dr))),
            c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>Rep_ubundle
                       (ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).Abs_ubundle
                                  [c_ds \<mapsto> tsMap BoolPair\<cdot>(s\<cdot>(tsMap invData\<cdot>Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_as)),
                                   c_dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_ds)\<cdot>ora1),
                                   c_ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>Rep_ubundle x\<rightharpoonup>c_dr))),
                                   c_as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>Rep_ubundle x\<rightharpoonup>c_ar)\<cdot>ora2)])
                       {c_abpOut, c_ar, c_as, c_dr, c_ds})\<rightharpoonup>c_ar)\<cdot>ora2)]"
  proof -
    (*ubgetch_def not yet inserted, ubFix (\<Lambda> u(*no type*). Abs_ubundle instead of 'a MABP tstream\<^sup>\<Omega> inside of Rep_ubundle*)
    have "ubWell [c_ds \<mapsto> tsMap BoolPair\<cdot> (s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot> (tsMap invBool\<cdot> (ubFix (\<Lambda> u. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot> (s\<cdot> (tsMap invData\<cdot> Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_as)), c_dr \<mapsto> tsMap BoolPair\<cdot> (tsMed\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_ds)\<cdot> ora1), c_ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_as \<mapsto> tsMap Bool\<cdot> (tsMed\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_ar)\<cdot> ora2)]) {c_abpOut, c_ar, c_as, c_dr, c_ds} . c_as))), c_dr \<mapsto> tsMap BoolPair\<cdot> (tsMed\<cdot> (tsMap invBoolPair\<cdot> (ubFix (\<Lambda> u. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot> (s\<cdot> (tsMap invData\<cdot> Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_as)), c_dr \<mapsto> tsMap BoolPair\<cdot> (tsMed\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_ds)\<cdot> ora1), c_ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_as \<mapsto> tsMap Bool\<cdot> (tsMed\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_ar)\<cdot> ora2)]) {c_abpOut, c_ar, c_as, c_dr, c_ds} . c_ds))\<cdot> ora1), c_ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot> (tsMap invBoolPair\<cdot> (ubFix (\<Lambda> u. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot> (s\<cdot> (tsMap invData\<cdot> Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_as)), c_dr \<mapsto> tsMap BoolPair\<cdot> (tsMed\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_ds)\<cdot> ora1), c_ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_as \<mapsto> tsMap Bool\<cdot> (tsMed\<cdot> (tsMap invBool\<cdot> Rep_ubundle u\<rightharpoonup>c_ar)\<cdot> ora2)]) {c_abpOut, c_ar, c_as, c_dr, c_ds} . c_dr)))), c_abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> (ubFix (\<Lambda> u. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot> (s\<cdot> (tsMap invData\<cdot> Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_as)), c_dr \<mapsto> tsMap BoolPair\<cdot> (tsMed\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_ds)\<cdot> ora1), c_ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_as \<mapsto> tsMap Bool\<cdot> (tsMed\<cdot> (tsMap invBool\<cdot> Rep_ubundle u\<rightharpoonup>c_ar)\<cdot> ora2)]) {c_abpOut, c_ar, c_as, c_dr, c_ds} . c_dr)))), c_as \<mapsto> tsMap Bool\<cdot> (tsMed\<cdot> (tsMap invBool\<cdot> (ubFix (\<Lambda> u. Abs_ubundle [c_ds \<mapsto> tsMap BoolPair\<cdot> (s\<cdot> (tsMap invData\<cdot> Rep_ubundle tb\<rightharpoonup>c_abpIn)\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_as)), c_dr \<mapsto> tsMap BoolPair\<cdot> (tsMed\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_ds)\<cdot> ora1), c_ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> Rep_ubundle u\<rightharpoonup>c_dr))), c_as \<mapsto> tsMap Bool\<cdot> (tsMed\<cdot> (tsMap invBool\<cdot>Rep_ubundle u\<rightharpoonup>c_ar)\<cdot> ora2)]) {c_abpOut, c_ar, c_as, c_dr, c_ds} . c_ar))\<cdot> ora2)]"
      using f42 by blast
    then show ?thesis
      by (simp add: ubgetch_insert)
  qed

  have f90: "cont ( fixABPHelper s ora1 ora2 tb)"
    apply(subst fixABPHelper_cont, simp_all add: assms)
    by(simp_all add: f12 f13 f14)

  have f91: "(abpFix s ora1 ora2 tb) . c_abpOut = tsMap Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(abpFix s ora1 ora2 tb . c_dr))))"
    apply (subst f41)
    apply (simp add: f90)
    apply (simp add: ubGetCh_def)
    apply (subst ubrep_ubabs) 
    apply (simp add: abpHelper_ubWell2)
    by simp

  have tsMap_invBoolPair: "\<And>s. tsMap invBoolPair\<cdot>(tsMap BoolPair\<cdot>s) = s"
    by (simp add: inj_def)

  have tsMap_invBool: "\<And>s. tsMap invBool\<cdot>(tsMap Bool\<cdot>s) = s"
    by (simp add: inj_def)

  have eq_c_dr: "(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_dr)) = tsMed\<cdot>(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_ds))\<cdot>ora1"
    apply (subst f41)
    apply (simp add: f90)
    apply (simp add: ubGetCh_def)
    apply (subst ubrep_ubabs) 
     apply (simp add: abpHelper_ubWell2)
    apply simp
    apply(subst tsMap_invBoolPair)
    by blast

  have eq_c_as: "(tsMap invBool\<cdot>((abpFix s ora1 ora2 tb) . c_as)) = tsMed\<cdot>(tsMap invBool\<cdot>((abpFix s ora1 ora2 tb) . c_ar))\<cdot>ora2"
    apply (subst f41)
    apply (simp add: f90)
    apply (simp add: ubGetCh_def)
    apply (subst ubrep_ubabs) 
     apply (simp add: abpHelper_ubWell2)
    apply simp
    apply(subst tsMap_invBool)
    by blast

  have eq_c_ds: "(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_ds)) = s\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))\<cdot>(tsMap invBool\<cdot>((abpFix s ora1 ora2 tb) . c_as))"
    apply (subst f41)
    apply (simp add: f90)
    apply (simp add: ubGetCh_def)
    apply (subst ubrep_ubabs) 
     apply (simp add: abpHelper_ubWell2)
    apply simp
    apply(subst tsMap_invBoolPair)
    by blast

  have eq_c_ar: "(tsMap invBool\<cdot>((abpFix s ora1 ora2 tb) . c_ar)) = tsProjSnd\<cdot>(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_dr))"
    apply (subst f41)
    apply (simp add: f90)
    apply (simp add: ubGetCh_def)
    apply (subst ubrep_ubabs) 
     apply (simp add: abpHelper_ubWell2)
    apply simp
    apply(subst tsMap_invBool)
    by(simp add: tsRec_def)

  (* Result *)
  have f8: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_dr)))) = tsAbs\<cdot>(tsMap invData\<cdot>(tb . c_abpIn))"
    using tsaltbitpro_inp2out  using eq_c_ar eq_c_as eq_c_dr eq_c_ds f12 f13 f14 by blast

  have f9: "tsAbs\<cdot>(tsMap Data\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMap invBoolPair\<cdot>((abpFix s ora1 ora2 tb) . c_dr))))) = tsAbs\<cdot>(tb . c_abpIn)"
  proof - 
    have f90: "\<And>s. invData (Data s) = s"
      by simp
    have f91: "tsDom\<cdot>(tb . c_abpIn) \<subseteq> range Data"
      by (metis assms(2) ctype_MABP.simps(1) insert_iff ubdom_channel_usokay ubgetch_insert usclOkay_tstream_def)
    show ?thesis
      using f8 tsAbs_data_eq using f91 by blast 
  qed
  show ?thesis
  proof - 
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



section\<open>Composition with general operator\<close>


lemma h100: "\<And>bst. #({True} \<ominus> bst) = \<infinity> \<Longrightarrow> #bst =\<infinity>"
  using sfilterl4 by auto

lemma abp_gencomp_final: assumes "f \<in> Rep_rev_uspec gencompABP"
                            and "ubDom\<cdot>tb = {c_abpIn}"
                          shows "tsAbs\<cdot>((f \<rightleftharpoons> tb) . c_abpOut) = tsAbs\<cdot>(tb . c_abpIn)"
proof - 
  have f1: "\<exists>s ora1 ora2. s \<in> tsSender \<and> (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and> f = (senderTSPF s) \<otimes> (medSR_TSPF ora1) \<otimes> recvTSPF \<otimes> (medRS_TSPF ora2) "
    sorry
  then obtain s where f11: "\<exists>ora1 ora2. s \<in> tsSender \<and> (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and> f = (senderTSPF s) \<otimes> (medSR_TSPF ora1) \<otimes> recvTSPF \<otimes> (medRS_TSPF ora2)"
    by blast
  then obtain ora1 where f12: "\<exists>ora2. s \<in> tsSender \<and> (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and> f = (senderTSPF s) \<otimes> (medSR_TSPF ora1) \<otimes> recvTSPF \<otimes> (medRS_TSPF ora2)"
    by blast
  then obtain ora2 where f13: "s \<in> tsSender \<and> (#({True} \<ominus> ora1) = \<infinity>) \<and> (#({True} \<ominus> ora2) = \<infinity>) \<and> f = (senderTSPF s) \<otimes> (medSR_TSPF ora1) \<otimes> recvTSPF \<otimes> (medRS_TSPF ora2)"
    by blast
  then have f14: "f = (senderTSPF s) \<otimes> (medSR_TSPF ora1) \<otimes> recvTSPF \<otimes> (medRS_TSPF ora2)"
    by blast

  have s_msr_compI: "ufCompI (senderTSPF s) (medSR_TSPF ora1) = ufDom\<cdot>(senderTSPF s)"
    apply (simp add: ufCompI_def)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom) 
  have s_msr_compO: "ufCompO (senderTSPF s) (medSR_TSPF ora1) = ufRan\<cdot>(senderTSPF s) \<union> ufRan\<cdot>(medSR_TSPF ora1)"
    apply (simp add: ufCompO_def)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom) 
  have s_msr_ran_empt: "ufRan\<cdot>(senderTSPF s) \<inter> ufRan\<cdot>(medSR_TSPF ora1) = {}"
    by (metis (no_types, lifting) Int_empty_right Int_insert_right c_dr_boolpair_ctype channel.distinct(245) 
        f13 inf_commute inf_sup_aci(1) med_tspfran2 sender_tspfran singletonD)
  have f20: "ufDom\<cdot>(senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) = {c_abpIn, c_as}"
    apply (simp add: ufunclComp_ufun_def)
    apply (subst ufcomp_dom)
     apply (simp add: ufcomp_ran s_msr_ran_empt)
    apply (subst s_msr_compO)
     apply (simp add: recv_tspfran sender_tspfran med_tspfran2 f13)
    apply (simp add: ufCompI_def)
    apply (simp add: ufcomp_dom ufcomp_ran s_msr_ran_empt)
    apply (subst s_msr_compO)
    apply (subst s_msr_compI)
    apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 
    by blast
  have f21: "ufRan\<cdot>(senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) = {c_ar, c_abpOut, c_dr, c_ds}"
    apply (simp add: ufunclComp_ufun_def)
    apply (subst ufcomp_ran)
    apply (simp add: ufcomp_ran s_msr_ran_empt)
    apply (subst s_msr_compO)
    apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 
    apply (simp add: ufCompO_def)
    apply (simp add: ufcomp_ran s_msr_ran_empt)
    apply (subst s_msr_compO)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 

  have s_msr_apply_sercomp_eq: "Rep_cufun (ufComp (senderTSPF s) (medSR_TSPF ora1))
        = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s)) \<leadsto> (ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))"
    apply (simp add: ufComp_def)
    apply (subst rep_abs_cufun)
    apply simp
     apply (rule ufcomp_well)
     apply (simp add:  med_tspfran2 f13 sender_tspfran)
    apply (simp only: ubFix_def)
    apply (subst ufcomp_serial_iterconst_eq)
      apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom) +
    by (simp only: ubclRestrict_ubundle_def ubclUnion_ubundle_def)

paragraph \<open>m_msr_sercomp\<close>
  obtain s_msr_sercomp where s_msr_sercomp_def: "s_msr_sercomp = (ufComp (senderTSPF s) (medSR_TSPF ora1))"
    by simp

  have s_msr_sercomp_dom: "ufDom\<cdot>s_msr_sercomp = ufDom\<cdot>(senderTSPF s)"
    apply (simp add: s_msr_sercomp_def) 
    apply (subst ufcomp_dom)
     apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom) 
    apply (simp add: ufCompI_def)
    using s_msr_compI ufCompI_def by blast
  have s_msr_sercomp_ran: "ufRan\<cdot>s_msr_sercomp = ufRan\<cdot>(senderTSPF s) \<union> ufRan\<cdot>(medSR_TSPF ora1)"
    apply (simp add: s_msr_sercomp_def)
    apply (subst ufcomp_ran)
     apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom) 
    apply (simp add: ufCompO_def)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran) 
  have s_msr_sercomp_recv_compI: "ufCompI s_msr_sercomp recvTSPF = {c_as, c_abpIn}"
    apply (simp add: ufCompI_def)
    apply (simp add: s_msr_sercomp_dom)
    apply (subst s_msr_sercomp_ran)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 

  have io_eq_s_msr_recv: "\<And> x. ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow> ubfun_io_eq (ufCompH s_msr_sercomp recvTSPF x) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF)"
    apply (subst ufCompH_dom)
    apply (simp add: s_msr_sercomp_recv_compI sender_tspfdom)
     apply (simp add: ubcldom_least_cs)
    by (simp add: recv_tspfran) +

  have sender_dom: "ufDom\<cdot>(senderTSPF s) = {c_as, c_abpIn}"
    by (simp add: sender_tspfdom)

  have some_eq: "\<And> a b. a = b \<Longrightarrow> Some a = Some b"
    by simp 

  have s_msr_dom_empt: "\<And> x. ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow> ubDom\<cdot>(senderTSPF s \<rightleftharpoons> x) \<inter> ubDom\<cdot>(medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> x)) = {}"
    by (metis f13 ctype_MABP.simps(4) med_tspfdom2 s_msr_ran_empt sender_tspfran ubclDom_ubundle_def ufran_2_ubcldom2)
  have s_msr_apply: "\<And> x. ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow> ufComp (senderTSPF s) (medSR_TSPF ora1) \<rightleftharpoons> x =
(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))))"
    apply (subst s_msr_apply_sercomp_eq)
    by (simp add: assms ubclDom_ubundle_def)
  have s_msr_apply2: "\<And> x. ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow> ufComp (senderTSPF s) (medSR_TSPF ora1) \<rightleftharpoons> x =
(ubUnion\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))))\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))"
    apply (subst s_msr_apply_sercomp_eq)
    apply (simp add: assms ubclDom_ubundle_def)
    apply (simp only: ubclRestrict_ubundle_def)
    apply (simp only: assms ubrestrict_id)
    using s_msr_dom_empt ubunion_commutative by blast

  have s_msr_recv_iter_ubfix2_dom: "\<And> i x. ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow>
    ubDom\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) i (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x) = ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF"
    apply (fold ubclDom_ubundle_def)
    apply (subst iter_ubfix2_dom)
    using assms io_eq_s_msr_recv apply blast
    by (simp add: recv_tspfran ubcldom_least_cs)
        
  have s_msr_ran_recv_dom_eq: "\<And> x. ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow> ubDom\<cdot>(medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> x)) = ufDom\<cdot>recvTSPF"
    apply (fold ubclDom_ubundle_def)
    apply (subst ufran_2_ubcldom2) +
      apply (simp add: assms ubclDom_ubundle_def)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)  +

  have lub_max_in_chain_eq: "\<And> x. ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s) \<Longrightarrow>
    ubFix (ufCompH s_msr_sercomp recvTSPF x) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) = 
ubclUnion\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x))\<cdot>(recvTSPF \<rightleftharpoons> ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x)))"
  proof (simp only: ubFix_def)
    fix x::"'a MABP tstream\<^sup>\<Omega>"
    assume a1: "ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s)"  
    have f3215_iter_2: "\<And> i. ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc (Suc i)) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x) =  
                                              ((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))"
      proof -
        fix i::nat
        have f32151: "\<And> i. (iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc (Suc i)) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x) = 
((ufCompH s_msr_sercomp recvTSPF) x)\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc i) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x)"
          by (simp add: recv_tspfran)
        have x_iter_ubfix2_restrict_union_recv_ran: "\<And>i. ubDom\<cdot>(recvTSPF \<rightleftharpoons> (ubRestrict (ufDom\<cdot>recvTSPF)\<cdot>(ubUnion\<cdot>x\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) i (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x)))) = ufRan\<cdot>recvTSPF"
          apply (fold ubclDom_ubundle_def)
          apply (fold ubclUnion_ubundle_def)
          apply (fold ubclRestrict_ubundle_def)
          apply (subst ufran_2_ubcldom2)
           apply (simp only: ubclrestrict_dom ubclunion_ubcldom)
           apply (subst iter_ubfix2_dom)
            apply (metis a1 io_eq_s_msr_recv ubclDom_ubundle_def)
           apply (subst s_msr_sercomp_ran)
           apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
        by (simp add: recv_tspfdom recv_tspfran)
        have f3215_iter2_unionL: "ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>(ubclUnion\<cdot>x\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc i) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x)) = x"
          apply (simp add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
          apply (subst ubunion_restrict2)
           apply (fold ubclDom_ubundle_def)
           apply (subst ufCompH_dom)
             apply (simp add: ubclDom_ubundle_def s_msr_sercomp_recv_compI sender_tspfdom a1)
            apply (metis iter_ufCompH_dom recv_tspfran s_msr_sercomp_recv_compI sender_tspfdom ubclDom_ubundle_def a1)
           apply (metis a1 Diff_disjoint s_msr_sercomp_dom s_msr_sercomp_recv_compI sender_tspfdom ufCompI_def)
          by (simp add: s_msr_sercomp_dom a1)
        show "ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc (Suc i)) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x) =  ((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))"
          apply (subst f32151)
          apply (simp only: ufcomph_insert)
          apply (simp only: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
          apply (subst ubunion_restrict2)
           apply (subst x_iter_ubfix2_restrict_union_recv_ran)
           apply (simp add: recv_tspfdom recv_tspfran)
           apply (fold ubclUnion_ubundle_def)
          apply (fold ubclRestrict_ubundle_def)
          apply (subst f3215_iter2_unionL)
          apply (simp only: s_msr_sercomp_def)
          apply (simp add: a1 s_msr_apply)
          apply (simp only: ubclRestrict_ubundle_def a1 ubrestrict_id)
          apply (subst ubunion_restrict)
           apply (simp add: a1 s_msr_ran_recv_dom_eq)
          by simp
      qed          
    have max_comp: "\<And>i. (iter_ufCompH s_msr_sercomp recvTSPF (Suc (Suc (Suc i))) x) = 
      ubclUnion\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x))\<cdot>(recvTSPF \<rightleftharpoons> ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x)))"
    proof -
      fix i::nat
      have f32151: "\<And> i. (iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc (Suc i)) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x) = 
  ((ufCompH s_msr_sercomp recvTSPF) x)\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc i) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x)"
        by (simp add: recv_tspfran)
      obtain iter2 where iter2_def: "iter2 = (iter_ufCompH s_msr_sercomp recvTSPF  (Suc (Suc i)) x)"
        by simp
      have f1: "(iter_ufCompH s_msr_sercomp recvTSPF (Suc (Suc (Suc i))) x) = ufCompH s_msr_sercomp recvTSPF x\<cdot>iter2"
        by (simp add: iter2_def)
      have f2: "ubRestrict (ufDom\<cdot>recvTSPF)\<cdot>(ubUnion\<cdot>x\<cdot>iter2) = ubRestrict (ufDom\<cdot>recvTSPF)\<cdot>iter2"
        apply (subst ubunion_commutative)
         apply (simp only: iter2_def)
         apply (fold ubclDom_ubundle_def)
         apply (subst iter_ubfix2_dom)
          apply (metis a1 io_eq_s_msr_recv ubclDom_ubundle_def)
         apply (metis ubclDom_ubundle_def a1 s_msr_sercomp_recv_compI sender_dom ufCompO_def ufcomp_I_inter_Oc_empty)
        apply (subst ubunion_restrict2)
         apply (simp add: a1 sender_dom recv_tspfdom)
        by (simp add: recv_tspfdom)
      have f3: "ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> x) = ((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))"
        apply (simp add: s_msr_sercomp_def)
        apply (subst s_msr_apply_sercomp_eq)
        apply (simp add: a1 ubclDom_ubundle_def)
        apply (simp only: ubclRestrict_ubundle_def) 
        apply (simp only: ubrestrict_id a1)
        apply (subst ubunion_restrict) 
        using a1 s_msr_ran_recv_dom_eq apply blast
        by simp
      show "(iter_ufCompH s_msr_sercomp recvTSPF (Suc (Suc (Suc i))) x) = 
      ubclUnion\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x))\<cdot>(recvTSPF \<rightleftharpoons> ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x)))"
        apply (subst f1)
        apply (simp only: ufcomph_insert)
        apply (simp only: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
        apply (subst ubunion_restrict2)
         apply (simp only: iter2_def)
         apply (fold ubclDom_ubundle_def)
         apply (subst iter_ubfix2_dom)
          apply (subst io_eq_s_msr_recv)
           apply (simp add: a1 ubclDom_ubundle_def)
        using ubclDom_ubundle_def a1 io_eq_s_msr_recv apply blast
         apply (metis Int_commute s_msr_sercomp_dom s_msr_sercomp_recv_compI sender_dom ufCompO_def ufcomp_I_inter_Oc_empty)
        apply (simp add: a1 s_msr_sercomp_dom)
        apply (subst f2)
        apply (simp only: iter2_def)
        apply (fold ubclRestrict_ubundle_def)
        apply (fold ubclUnion_ubundle_def)
        apply (subst f3215_iter_2)
        apply (simp only:  ubclRestrict_ubundle_def a1 ubrestrict_id)
        apply (fold ubclRestrict_ubundle_def)
        apply (simp only: f3)
        by (simp only:  ubclRestrict_ubundle_def a1 ubrestrict_id)
    qed
    have max_in_chain_s_msr_r: "max_in_chain (Suc (Suc (Suc 0))) (\<lambda>i. iter_ufCompH s_msr_sercomp recvTSPF i x)"
    proof (rule max_in_chainI)
      fix j
      assume a11: "Suc (Suc (Suc 0)) \<le> j"
      have f1: "ufDom\<cdot>s_msr_sercomp \<inter> ufDom\<cdot>recvTSPF = {}"
        by (simp add: s_msr_sercomp_dom sender_dom recv_tspfdom)
      obtain k where o1: "j = Suc (Suc (Suc k))"
        by (metis (no_types) Suc_leD Suc_n_not_le_n a11 not0_implies_Suc)  
      show "iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc (Suc (Suc 0))) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x =
         iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) j (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x"
        apply (subst o1)
        by (metis a1 max_comp recv_tspfran)
    qed
    have f1: "ufRan\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun) = ufRan\<cdot>(recvTSPF::('b MABP tstream\<^sup>\<Omega>) ufun)"
      by (simp add: recv_tspfran)
    have f2: "(iter_ufCompH s_msr_sercomp recvTSPF (Suc (Suc (Suc 0))) x) = 
      ubclUnion\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x))\<cdot>(recvTSPF \<rightleftharpoons> ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x)))"
      using max_comp by blast
    have "chain (\<lambda>n. iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) n (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>(recvTSPF::('a MABP tstream\<^sup>\<Omega>) ufun)) x)"
      by (metis (no_types, lifting) a1 cont_pref_eq2I io_eq_s_msr_recv iterate_Suc2 po_class.chainI ubclDom_ubundle_def ubcldom_least)
    then show "(\<Squnion>n. iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) n (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>(recvTSPF::('b MABP tstream\<^sup>\<Omega>) ufun)) x) = 
ubclUnion\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x))\<cdot>(recvTSPF \<rightleftharpoons> ubclRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>s_msr_sercomp)\<cdot>x)))"
      apply (fold f2)
      using f1 max_in_chain_s_msr_r maxinch_is_thelub by fastforce
  qed

  have f32: "Rep_cufun (ufComp (ufComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF)
        = (\<lambda> x. (ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s)) \<leadsto> (ubUnion\<cdot>(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))\<cdot>
                                                                                              (recvTSPF \<rightleftharpoons>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))"
  proof -
    have f320: "\<And> x. ubclDom\<cdot>x = ufCompI (senderTSPF s) (medSR_TSPF ora1) \<Longrightarrow> s_msr_sercomp \<rightleftharpoons> x = 
(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))))"
      apply (simp add: s_msr_sercomp_def)
      apply (subst s_msr_apply_sercomp_eq)
      by (simp add: s_msr_compI)
    have f321: "\<And>x::'a MABP tstream\<^sup>\<Omega>.
       \<not> ubclDom\<cdot>x \<noteq> ufDom\<cdot>(senderTSPF s) \<Longrightarrow>
       Rep_cufun (ufComp s_msr_sercomp recvTSPF) x =
       (ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s))\<leadsto>(ubUnion\<cdot>(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))\<cdot>
                                                                                              (recvTSPF \<rightleftharpoons>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))))"
    proof -
      fix x::"'a MABP tstream\<^sup>\<Omega>"
      assume a1: "\<not> ubclDom\<cdot>x \<noteq> ufDom\<cdot>(senderTSPF s)"
      have f32101: " ubDom\<cdot>x = ufDom\<cdot>(senderTSPF s)"
        by (metis a1 ubclDom_ubundle_def)
      have x_ubcldom: "ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s)"
        using a1 by auto
      have x_sender_restrict_id: " ubRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x = x"
        by (simp add: f32101)
      have f32102: "(ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s))\<leadsto>(ubUnion\<cdot>(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))\<cdot>
                                                                                              (recvTSPF \<rightleftharpoons>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))) = 
          Some ((ubUnion\<cdot>(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))\<cdot>
                                                                                              (recvTSPF \<rightleftharpoons>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))"
        using a1 by auto
      have f3214: "Rep_cufun (ufComp s_msr_sercomp recvTSPF) x = Some (ubFix (ufCompH s_msr_sercomp recvTSPF x) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF))"
        apply (simp add: ufComp_def)
        apply (subst rep_abs_cufun)
          apply simp
         apply (rule ufcomp_well)
         apply (subst s_msr_sercomp_ran)
         apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran) 
        by (simp add: recv_tspfran s_msr_sercomp_recv_compI sender_tspfdom x_ubcldom)
      have f32151: "\<And> i. (iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc (Suc i)) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x) = 
((ufCompH s_msr_sercomp recvTSPF) x)\<cdot>(iter_ubfix2 (ufCompH s_msr_sercomp recvTSPF) (Suc i) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF) x)"
        by (simp add: recv_tspfran)
      have f2: " ubRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x = x"
          by (simp add: f32101)
      have f3: " ubRestrict (ufDom\<cdot>recvTSPF)\<cdot>(s_msr_sercomp \<rightleftharpoons> x) =
((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))"
          apply (simp only: ubclRestrict_ubundle_def)
          apply (simp only: x_sender_restrict_id)
          apply (simp add: s_msr_sercomp_def)
          apply (simp add: f32101 s_msr_apply)
          apply (simp only: ubclRestrict_ubundle_def)
        apply (simp only: x_sender_restrict_id)
        by (simp add: f32101 s_msr_ran_recv_dom_eq)
      have f3215: "Some (ubFix (ufCompH s_msr_sercomp recvTSPF x) (ufRan\<cdot>s_msr_sercomp \<union> ufRan\<cdot>recvTSPF)) = Some ((ubUnion\<cdot>(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))\<cdot>
                                                                                              (recvTSPF \<rightleftharpoons>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))"
        apply (rule some_eq)
        apply (subst lub_max_in_chain_eq)
          apply (simp only: f32101)
          apply (simp only: s_msr_sercomp_dom)
          apply (simp only: ubclRestrict_ubundle_def)
          apply (simp only: x_sender_restrict_id)
          apply (simp only: s_msr_sercomp_def)
          apply (simp add: f32101 s_msr_apply)
          apply (simp only: ubclRestrict_ubundle_def)
          apply (simp only: x_sender_restrict_id)
          apply (subst ubunion_restrict)
           apply (simp add: f32101 s_msr_ran_recv_dom_eq)
          by (simp add: ubclUnion_ubundle_def)
      show "Rep_cufun (ufComp s_msr_sercomp recvTSPF) x =
       (ubclDom\<cdot>x = ufDom\<cdot>(senderTSPF s))\<leadsto>(ubUnion\<cdot>(ubUnion\<cdot>((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))\<cdot>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x)))))\<cdot>
                                                                                              (recvTSPF \<rightleftharpoons>((medSR_TSPF ora1) \<rightleftharpoons> ((senderTSPF s) \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>(senderTSPF s))\<cdot>x))))"
        by (metis (no_types, lifting) f32102 f3214 f3215)
    qed
    show ?thesis
      apply (fold s_msr_sercomp_def)
      apply (simp only: fun_eq_iff)
      apply (rule)
      apply (case_tac "(ubclDom\<cdot>x \<noteq> ufDom\<cdot>(senderTSPF s))")
       apply (metis (no_types, hide_lams) f20 insert_commute not_Some_eq s_msr_sercomp_def sender_tspfdom ufdom_2ufundom ufunclComp_ufun_def)
      by (simp add: f321)
  qed
paragraph \<open>eq proof between abp and abpbundlehelper\<close>
  obtain s_msr_r_comp where s_msr_r_comp_def: "s_msr_r_comp = (ufComp (ufComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF)"
    by simp
  have s_msr_r_comp_dom: "ufDom\<cdot>s_msr_r_comp = ufDom\<cdot>(senderTSPF s)"
    apply (simp add: s_msr_r_comp_def)
    apply (fold s_msr_sercomp_def)
    apply (subst ufcomp_dom)
     apply (subst s_msr_sercomp_ran)
     apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
    by (simp add: s_msr_sercomp_recv_compI sender_tspfdom)
  have s_msr_r_comp_ran: "ufRan\<cdot>s_msr_r_comp = ufRan\<cdot>(senderTSPF s) \<union> ufRan\<cdot>(medSR_TSPF ora1) \<union> ufRan\<cdot>recvTSPF"
    apply (simp add: s_msr_r_comp_def)
    apply (fold s_msr_sercomp_def)
    apply (subst ufcomp_ran)
     apply (subst s_msr_sercomp_ran)
     apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
    apply (simp add: ufCompO_def)
    apply (subst s_msr_sercomp_ran)
    by (simp add: recv_tspfran)
  have s_msr_r_comp_mrs_compI: "ufCompI s_msr_r_comp (medRS_TSPF ora2) = {c_abpIn}"
    apply (simp add: ufCompI_def)
    apply (simp add: s_msr_r_comp_dom)
    apply (subst s_msr_r_comp_ran)
    by (simp add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 
  subparagraph \<open>Define chains\<close>
  obtain innerABP_chain where innerABP_chain_def: "innerABP_chain = (\<lambda> i::nat. iter_ubfix2 (ufCompH (ufComp (ufComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (medRS_TSPF ora2)) i {c_abpOut, c_as, c_ar, c_dr, c_ds} tb)"
    by simp
  obtain innerABP_chain_shift where innerABP_chain_shift_def: "innerABP_chain_shift = (\<lambda> i. innerABP_chain (2 * (Suc i)))"
    by simp
  subparagraph \<open>chain eq proof\<close>
  have innerABP_chain_ischain: "chain innerABP_chain"
    apply (simp add: innerABP_chain_def)
    apply (rule ub_iterate_chain)
    apply (simp add: ufCompH_def)
    apply (simp add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 
    apply (fold s_msr_r_comp_def)
    apply (simp only: s_msr_r_comp_dom sender_tspfdom)
    apply (simp add: ubclunion_restrict)
    apply (simp only: ubclRestrict_ubundle_def ubclUnion_ubundle_def ubclLeast_ubundle_def)
    apply (subst ubrestrict_id)
     apply (simp add: assms(2))
    apply (simp add: ubrestrict_ubleast_inter)
    apply (fold ubclUnion_ubundle_def)
    apply (simp add: ubclunion_ubcldom)
    apply (subst ufran_2_ubcldom2)
     apply (simp add: s_msr_r_comp_dom sender_tspfdom ubclunion_ubcldom)
     apply (simp add: assms(2) ubclDom_ubundle_def)
    apply (subst ufran_2_ubcldom2)
    apply (simp add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom ubclDom_ubundle_def)
    apply (subst s_msr_r_comp_ran)
    apply (simp add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 
    by blast
  have innerABP_chain_shift_ischain: "chain innerABP_chain_shift"
    apply (simp add: innerABP_chain_shift_def)
    apply (rule chainI)
    apply (rule chain_mono_less)
     apply (simp add: innerABP_chain_ischain)
    apply (induct_tac i)
     apply simp
    by simp
  have innerABP_chain_shift_in_range : "\<And> i . innerABP_chain_shift i \<in> range innerABP_chain"
    by (simp add: innerABP_chain_shift_def)

  have innerABP_chain_eq: "Lub innerABP_chain = Lub innerABP_chain_shift"
    apply (subst po_eq_conv) apply rule
     apply (rule lub_mono)
       apply (simp_all add: innerABP_chain_ischain innerABP_chain_shift_ischain)
     apply (simp only: innerABP_chain_shift_def innerABP_chain_def)
     apply (rule chain_mono)
      apply (fold innerABP_chain_def)
      apply (simp add: innerABP_chain_ischain)
     apply (induct_tac i)
    by (simp add: innerABP_chain_ischain innerABP_chain_shift_ischain cpo is_ub_thelub_ex innerABP_chain_shift_in_range lub_below) +


  have innerABP_chain_dom: "\<And> i. ubDom\<cdot>(iter_ubfix2 (ufCompH (ufComp (ufComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
                                                                    (medRS_TSPF ora2)) i {c_abpOut, c_as, c_ar, c_dr, c_ds} tb) =
                                             {c_abpOut, c_as, c_ar, c_dr, c_ds}"
    apply (fold s_msr_r_comp_def)
    apply (fold ubclDom_ubundle_def)
    apply (rule iter_ubfix_dom)
     apply (subst ufCompH_dom)
       apply (simp add: assms(2) s_msr_r_comp_mrs_compI ubclDom_ubundle_def)
    apply (simp add: ubcldom_least_cs)
      apply (subst s_msr_r_comp_ran) defer
      apply (subst s_msr_r_comp_ran) defer
      apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom 
          recv_tspfran recv_tspfdom)
    by blast +
  have sender_tb_innerABP_dom: "\<And>i. ubclDom\<cdot>(ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))) = ufDom\<cdot>(senderTSPF s)"
    apply (simp add: ubclunion_dom)
    apply (simp add: ubclrestrict_dom innerABP_chain_def)
    apply (simp only: ubclDom_ubundle_def)
    by (simp add: innerABP_chain_dom assms(2) sender_tspfdom)
  have innerABP_chain_c_ar_medrs: "\<And>i::nat. ubclDom\<cdot>(ubclRestrict {c_ar}\<cdot>(innerABP_chain i)) = ufDom\<cdot>(medRS_TSPF ora2)"
    apply (simp add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
    apply (simp add: ubclrestrict_ubcldom)
    apply (simp add: innerABP_chain_def ubclDom_ubundle_def)
    by (simp add: innerABP_chain_dom)

  have medrs_innerABP_chain_dom: "\<And>i. ubclDom\<cdot>(medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) = {c_as}"
    apply (subst ufran_2_ubcldom2)
    apply (simp add: innerABP_chain_c_ar_medrs)
    by (simp add: med_tspfran2 f13)
  have medsr_sender_innerABP_chain_dom: "\<And>i. ubclDom\<cdot>(medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))) = {c_dr}"
    apply (subst ufran_2_ubcldom2) +
       apply (simp add: sender_tb_innerABP_dom)
    by (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom 
          recv_tspfran recv_tspfdom) 
  have innerABP_apply_step: "\<And>i. innerABP_chain (Suc i) = 
    ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i)))"
  proof -
    fix i::nat
    obtain iter_i where iter_i_def: "iter_i = (iter_ubfix2 (ufCompH (ufComp (ufComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) 
                                                                    (medRS_TSPF ora2)) i {c_abpOut, c_as, c_ar, c_dr, c_ds} tb)"
      by simp
    have f1: "ubDom\<cdot>(iter_i) = {c_abpOut, c_as, c_ar, c_dr, c_ds}"
      by (simp add: innerABP_chain_dom iter_i_def)
    have f2: "(ubclDom\<cdot>(ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>iter_i)) = ufDom\<cdot>(senderTSPF s))"
      apply (simp add: ubclunion_ubcldom)
      apply (simp add: ubclrestrict_dom sender_tspfdom)
      by (simp add: ubclDom_ubundle_def assms(2) f1)
    have f3: "innerABP_chain i = iter_ubfix2 (ufCompH (ufComp (ufComp (senderTSPF s) (medSR_TSPF ora1)) recvTSPF) (medRS_TSPF ora2)) i
             {c_abpOut, c_as, c_ar, c_dr, c_ds} tb"
      by (simp add: innerABP_chain_def)
    have f4: "ubclRestrict {c_as, c_abpIn}\<cdot>tb = tb"
      apply (simp add: ubclRestrict_ubundle_def)
      by (simp add: assms(2))
    show "innerABP_chain (Suc i) = 
ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i)))"
      apply (simp add: innerABP_chain_def)
      apply (fold iter_i_def)
      apply (fold s_msr_r_comp_def)
      apply (simp add: ufCompH_def)
      apply (simp add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom 
          recv_tspfran recv_tspfdom s_msr_r_comp_dom)
      apply (simp add: ubclunion_restrict)
      apply (simp add: f4)
      apply (simp only: ubclUnion_ubundle_def ubclRestrict_ubundle_def)
       apply (simp_all add: assms(2))
      apply (subst ubrestrict_ubdom_sup_inter)
      apply (simp only: f1)
      apply (simp add: s_msr_r_comp_def)
      apply (fold ubclUnion_ubundle_def)
      apply (fold ubclRestrict_ubundle_def)
      apply (subst f32)
      apply (simp add: f2)
      apply (simp add: sender_tspfdom)
      apply (simp add: ubclunion_restrict)
      apply (simp add: ubclrestrict_twice)
      apply (simp add: f4)
      by (simp only: ubclUnion_ubundle_def ubclRestrict_ubundle_def)
  qed

  have innerABP_c_as: "\<And>i. ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) . c_as = 
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) . c_as"
    apply (simp only: ubclUnion_ubundle_def)
    apply (rule ubunion_getchR)
    apply (fold ubclDom_ubundle_def)
    by (simp add: medrs_innerABP_chain_dom)

  have recv_innerABP_chain_dom: "\<And> i. ubclDom\<cdot>(recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> (ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))) = {c_abpOut, c_ar}"
    apply (subst ufran_2_ubcldom2) +
       apply (simp add: sender_tb_innerABP_dom)
    apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom 
          recv_tspfran recv_tspfdom) 
    by blast
  have innerABP_c_ar: "\<And>i. ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) . c_ar = 
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))) . c_ar"
    apply (simp only: ubclUnion_ubundle_def)
    apply (subst ubunion_getchL)
    apply (fold ubclDom_ubundle_def)
    apply (simp add: medrs_innerABP_chain_dom)
    apply (rule ubunion_getchR)
    using ubclDom_ubundle_def ubclUnion_ubundle_def
    by (metis insert_iff recv_innerABP_chain_dom)
  have innerABP_c_abpOut: "\<And>i. ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) . c_abpOut = 
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))) . c_abpOut"
    apply (simp only: ubclUnion_ubundle_def)
    apply (subst ubunion_getchL)
    apply (fold ubclDom_ubundle_def)
     apply (simp add: medrs_innerABP_chain_dom)
    apply (rule ubunion_getchR)
    using ubclDom_ubundle_def ubclUnion_ubundle_def
    by (metis insert_iff recv_innerABP_chain_dom)

  have innerABP_c_ds: "\<And>i. ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) . c_ds = 
    (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))) . c_ds"
    apply (simp only: ubclUnion_ubundle_def)
    apply (subst ubunion_getchL)
    apply (fold ubclDom_ubundle_def)
     apply (simp add: medrs_innerABP_chain_dom)
    apply (subst ubunion_getchL)
    apply (fold ubclDom_ubundle_def)
    apply (fold ubclUnion_ubundle_def)
    apply (simp add: recv_innerABP_chain_dom)
    apply (simp add: ubclUnion_ubundle_def)
    apply (rule ubunion_getchL)
    using ubclDom_ubundle_def ubclUnion_ubundle_def 
    by (metis channel.simps(246) medsr_sender_innerABP_chain_dom singletonD)

  have innerABP_c_dr: "\<And>i. ubclUnion\<cdot>(ubclUnion\<cdot>(ubclUnion\<cdot>(senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))\<cdot>
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))))\<cdot>
    (recvTSPF \<rightleftharpoons> (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i))))))\<cdot>
    (medRS_TSPF ora2 \<rightleftharpoons> (ubclRestrict {c_ar}\<cdot>(innerABP_chain i))) . c_dr = 
    (medSR_TSPF ora1 \<rightleftharpoons> (senderTSPF s \<rightleftharpoons> ubclUnion\<cdot>tb\<cdot>(ubclRestrict {c_as}\<cdot>(innerABP_chain i)))) . c_dr"
    apply (simp only: ubclUnion_ubundle_def)
    apply (subst ubunion_getchL)
    apply (fold ubclDom_ubundle_def)
    apply (simp add: medrs_innerABP_chain_dom)
    apply (subst ubunion_getchL)
    apply (fold ubclDom_ubundle_def)
    apply (fold ubclUnion_ubundle_def)
    apply (simp add: recv_innerABP_chain_dom)
    apply (simp add: ubclUnion_ubundle_def)
    apply (rule ubunion_getchR)
    using ubclDom_ubundle_def ubclUnion_ubundle_def 
    by (metis insertI1 medsr_sender_innerABP_chain_dom)

  obtain abphelper_chain where abphelper_chain_def: "abphelper_chain = (\<lambda> i. (iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})))"
    by simp
  obtain abphelper_chain_shift where abphelper_chain_shift_def: "abphelper_chain_shift = (\<lambda> i. abphelper_chain (4 * (Suc i)))"
    by simp
  obtain abphelper_ext_chain1 where abphelper_ext_chain1_def: "abphelper_ext_chain1 = (\<lambda> i. (iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))"
    by simp
  obtain abphelper_ext_chain1_shift where abphelper_ext_chain1_shift_def: "abphelper_ext_chain1_shift = (\<lambda> i.  abphelper_ext_chain1 (4 * (Suc i)))"
    by simp
  obtain abphelper_ext_chain where abphelper_ext_chain_def: "abphelper_ext_chain = (\<lambda> i. ubclRestrict {c_abpOut, c_as}\<cdot>(iterate i\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})))"
    by simp
  obtain abphelper_ext_chain_shift where abphelper_ext_chain_shift_def: "abphelper_ext_chain_shift = (\<lambda> i. abphelper_ext_chain (4 * (Suc i)))"
    by simp

  have abphelper_chain_ischain: "chain abphelper_chain"
    apply (simp add:  abphelper_chain_def)
    by (simp add: fixABPHelper_chain f12 f13 f14)
  have abphelper_ext_chain1_ischain: "chain abphelper_ext_chain1"
    apply (simp add:  abphelper_ext_chain1_def)
    by (simp add: fixABPHelper_ext_chain f12 f13 f14)
  have abphelper_ext_chain1_shift_ischain: "chain abphelper_ext_chain1_shift"
    apply (rule chainI)
    apply (simp add: abphelper_ext_chain1_shift_def)
    apply (rule chain_mono_less)
     apply (simp add: abphelper_ext_chain1_ischain)
    apply (induct_tac i)
     apply simp
    by simp
  have abphelper_ext_chain1_shift_in_range : "\<And> i . abphelper_ext_chain1_shift i \<in> range abphelper_ext_chain1"
    by (simp add: abphelper_ext_chain1_shift_def abphelper_ext_chain1_def)
  have abphelper_chain_shift_ischain: "chain abphelper_chain_shift"
    apply (rule chainI)
    apply (simp add: abphelper_chain_shift_def)
    apply (rule chain_mono_less)
     apply (simp add: abphelper_chain_ischain)
    apply (induct_tac i)
     apply simp
    by simp

  have abphelper_ext_chain_ischain: "chain abphelper_ext_chain"
    apply (simp add: abphelper_ext_chain_def)
    apply (simp add: ubclRestrict_ubundle_def)
    apply (rule chainI)
    apply (rule ubrestrict_belowI1)
    apply (rule chainE)
    apply (subst fixABPHelper_ext_chain)
    by (simp_all add: f12 f13 f14)

  have abphelper_ext_chain_shift_ischain: "chain abphelper_ext_chain_shift"
    apply (rule chainI)
    apply (simp add: abphelper_ext_chain_shift_def)
    apply (rule chain_mono_less)
     apply (simp add: abphelper_ext_chain_ischain)
    apply (induct_tac i)
     apply simp
    by simp

  have four_times_simp_suc: "\<And> i. 4 * (Suc i) = (Suc (Suc (Suc (Suc (4 * i)))))"
    by simp
  have four_times_zero: "4 * (0::nat) = 0"
    by simp
  have two_times_simp_suc: "\<And> i. 2 * (Suc i) = Suc (Suc (2 * i))"
    by simp
  have two_times_zero: "2 * (0::nat) = 0"
    by simp

  have abphelper_ext_chain_shift_in_range : "\<And> i . abphelper_ext_chain_shift i \<in> range abphelper_ext_chain"
    by (simp add: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
  have abphelper_ext_chain_shift_lub_eq: "Lub abphelper_ext_chain = Lub abphelper_ext_chain_shift"
    apply (subst po_eq_conv) apply rule
     apply (rule lub_mono)
       apply (simp_all add: abphelper_ext_chain_shift_ischain abphelper_ext_chain_ischain)
     apply (simp add: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
     apply (rule chain_mono)
      apply (fold abphelper_ext_chain_def)
      apply (simp add: abphelper_ext_chain_ischain)
     apply (induct_tac i)
    by (simp add: abphelper_ext_chain_ischain abphelper_ext_chain_shift_ischain cpo is_ub_thelub_ex abphelper_ext_chain_shift_in_range lub_below) +

  have f4: "(ubFix (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) tb) {c_abpOut, c_as, c_ar, c_dr, c_ds}) . c_abpOut =
            (ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})  .  c_abpOut" 
  proof -
    have f41: "Lub abphelper_chain . c_abpOut = (ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})  .  c_abpOut"
      by (simp add: abphelper_chain_def ubFix_def)

    have ubfun_io_eq_abphelper_ext: "ubfun_io_eq (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut))))) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}"
      apply (simp add: ubclDom_ubundle_def)
       apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
     apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
    by blast

    have f200010: "\<And>i. (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) =
      iterate i\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
      apply (induct_tac i)
       apply simp
      apply (simp only: iterate_Suc)
      apply (rule ubfix_eq)
      by (simp only: ubfun_io_eq_abphelper_ext)
    have abp_ex_abpout_idout_eq: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_idOut = 
      (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_abpOut"
    proof -
      have f20001: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) =
          iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
        by (simp only: f200010)
      have f20002: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) =
          iterate (Suc (Suc (Suc 0)))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})"
        by (simp only: f200010)
      have f1: "(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_idOut =
      iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(fixABPHelperCont_ext s ora1 ora2 tb)\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_idOut"
        apply (subst f20001)
        by simp
      show ?thesis
        apply (subst f1)
        apply (simp only: fixABPHelperCont_ext_iter_4_c_idOut2 f12 f13 f14)
        apply (fold f20002)
        apply (rule ubgetch_tsmap_idI)
          apply (fold ubclDom_ubundle_def)
          apply (subst ubfix_dom)
           apply (simp add: ubclDom_ubundle_def)
        apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
           apply (simp_all add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
        by blast +
    qed
    have abphelper_N_ext_chain_eq: "Lub abphelper_chain . c_abpOut = (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut"
      proof -
          have abp_ex_abpout_idout_res_eq: "(ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))  .  c_abpOut
       = (ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut"
              apply (unfold abp_ex_abpout_idout_eq)
              by (simp add: ubclRestrict_ubundle_def)
          have f100: "Lub abphelper_chain = (ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(ubFix (fixABPHelperCont_ext s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
            apply (simp add: ubFix_def)
            apply (simp add: ubclRestrict_ubundle_def)
            apply (subst ubrestrict_lub)
             apply (simp add: fixABPHelper_ext_chain f12 f13 f14)
            apply (simp add: abphelper_chain_def)
            apply (rule lub_eq)
            apply (induct_tac i)
             apply (simp add: ubclLeast_ubundle_def ubrestrict_ubleast_inter)
            apply (fold ubclRestrict_ubundle_def)
          proof -
            fix i::nat and n::nat
            assume a1: "iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}) =
             ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
            obtain n_step where n_step_def: "n_step = iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds})"
              by simp
            obtain n_restrict_step where n_restrict_step_def: "n_restrict_step = (iterate n\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
              by simp
            have f299: "ubDom\<cdot>(Abs_ubundle (ABPBundleHelper s ora1 ora2 tb n_step)) = {c_abpOut, c_ar, c_as, c_dr, c_ds}"
              apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ubWell)
              by blast
            have f300: "\<And> c. c \<in> {c_abpOut, c_ar, c_as, c_dr, c_ds} \<Longrightarrow> (ubRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>n_restrict_step) . c = n_restrict_step . c"
              by (simp add: n_restrict_step_def)
            have f301: "n_step= ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>n_restrict_step"
              apply (simp add: n_step_def n_restrict_step_def)
              by (simp add: a1)
            show "iterate (Suc n)\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds}) =
             ubclRestrict {c_abpOut, c_ar, c_as, c_dr, c_ds}\<cdot>(iterate (Suc n)\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
              apply (simp)
              apply (fold n_step_def)
              apply (fold n_restrict_step_def)
              apply (simp add: fixABPHelper_cont fixABPHelper_ext_cont f12 f13 f14)
              apply (rule ub_eq)
               apply (simp_all only: f299)
              apply (simp add: ubclRestrict_ubundle_def)
               apply (simp add: ubdom_ubrep_eq ABPBundleHelper_ext_ubWell)
              apply auto
                  apply (simp_all add: ubclRestrict_ubundle_def)
                  apply (simp_all add: ubgetch_ubrep_eq ABPBundleHelper_ubWell ABPBundleHelper_ext_ubWell)
                  by (simp add: f301 ubclRestrict_ubundle_def) +
              qed
      show ?thesis
        apply (fold abp_ex_abpout_idout_res_eq) 
        by (simp add: f100)
    qed
    have abphelper_ext_gencomp_eq: " ubFix (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) tb) {c_abpOut, c_as, c_ar, c_dr, c_ds}  .  c_abpOut =
    ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}  .  c_idOut"
    proof -
  (*
      have f0: "ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut} .  c_idOut = Lub abphelper_ext_chain_shift . c_idOut"
        apply (fold abphelper_ext_chain_shift_lub_eq)
        apply (simp add: ubFix_def)
        apply (subst ubgetch_lub)
          apply (simp add: fixABPHelper_ext_chain f12 f13 f14)
        apply (subst ubdom_lub2)
          apply (simp add: fixABPHelper_ext_chain f12 f13 f14)
          apply (simp add: fixABPHelperCont_ext_iter_dom f12 f13 f14)
        apply (subst ubgetch_lub)
          apply (simp add: abphelper_ext_chain_ischain)
        apply (subst ubdom_lub2)
          apply (simp add: abphelper_ext_chain_ischain)
         apply (simp add: abphelper_ext_chain_def)
         apply (fold ubclDom_ubundle_def)
         apply (simp add: ubclrestrict_dom)
         apply (simp add: ubclDom_ubundle_def)
         apply (simp add: fixABPHelperCont_ext_iter_dom f12 f13 f14)
        apply (simp add: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
        by (simp add: ubclRestrict_ubundle_def)
*)
      have f1: "ubFix (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) tb) {c_abpOut, c_as, c_ar, c_dr, c_ds}  .  c_abpOut = 
          ubclRestrict {c_as, c_abpOut}\<cdot>(ubFix (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) tb) {c_abpOut, c_as, c_ar, c_dr, c_ds})  .  c_abpOut" 
        by (simp add: ubclRestrict_ubundle_def)
      have f2: "ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}  .  c_idOut = 
ubclRestrict {c_as, c_idOut}\<cdot>(ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).  Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut"
        by (simp add: ubclRestrict_ubundle_def)
      have f4:"ubclRestrict {c_as, c_idOut}\<cdot>(ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).  Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_idOut = 
          (ubFix (\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>).  Abs_ubundle (ABPBundleHelper_ext s ora1 ora2 tb x)) {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})  .  c_abpOut"
        apply (simp add: ubclRestrict_ubundle_def)
        by (simp add: abp_ex_abpout_idout_eq)
      have f6: "chain (\<lambda>i::nat. iter_ubfix2 (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2)) i {c_abpOut, c_as, c_ar, c_dr, c_ds} tb)"
        apply (rule iter_ubfix2_chain)
        apply (simp only: ufunclComp_ufun_def)
        apply (fold s_msr_r_comp_def)
        apply (subst ufCompH_dom)
          apply (simp add: s_msr_r_comp_mrs_compI)
          apply (simp add: assms(2) ubclDom_ubundle_def)
         apply (subst s_msr_r_comp_ran)
         apply (simp add: ubcldom_least_cs)
         apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
         apply blast
        apply (subst s_msr_r_comp_ran)
        apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom) 
        by blast
      have f7: "ubfun_io_eq (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) tb) {c_abpOut, c_as, c_ar, c_dr, c_ds}"
        proof -
          have "ubfun_io_eq (ufCompH s_msr_r_comp (medRS_TSPF ora2) tb) (insert c_as (ufRan\<cdot>s_msr_r_comp))"
            by (metis (no_types) Un_empty_right Un_insert_right assms(2) innerABP_chain_c_ar_medrs medrs_innerABP_chain_dom s_msr_r_comp_mrs_compI ubclDom_ubundle_def ubcldom_least_cs ufCompH_dom ufran_2_ubcldom2)
          then show "ubfun_io_eq (ufCompH (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) tb) {c_abpOut, c_as, c_ar, c_dr, c_ds}"
            by (metis (no_types) f21 insert_commute s_msr_r_comp_def ufunclComp_ufun_def)
        qed
        have f80: "\<And>i. ubclDom\<cdot>(ubclRestrict {c_as, c_abpOut}\<cdot>(innerABP_chain_shift i)) = {c_as, c_abpOut}"
          apply (simp add: ubclRestrict_ubundle_def ubclDom_ubundle_def)
          apply (simp only: innerABP_chain_shift_def innerABP_chain_def)
          apply (fold s_msr_r_comp_def)
          apply (fold ubclDom_ubundle_def)
          apply (subst iter_ubfix2_dom)
            apply (subst ufCompH_dom)
              apply (simp add: s_msr_r_comp_mrs_compI)
              apply (simp add: ubclDom_ubundle_def  assms(2))
           apply (subst s_msr_r_comp_ran)
             apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom ubcldom_least_cs)
          apply blast
           apply (subst s_msr_r_comp_ran)
            apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 f14 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
          by blast
        have f8: "ubclRestrict {c_as, c_abpOut}\<cdot>(Lub innerABP_chain_shift)  = Lub abphelper_ext_chain_shift "
          apply (simp add: ubclRestrict_ubundle_def)
          apply (subst ubrestrict_lub)
          apply (simp add: innerABP_chain_shift_ischain)
          apply (rule lub_eq)
          apply (induct_tac i)
           apply (rule ub_eq)
            apply (fold ubclDom_ubundle_def)
            apply (fold ubclRestrict_ubundle_def)
            apply (simp_all add: f80)
            apply (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
            apply (simp only: ubclrestrict_dom)
            apply (simp only: ubclDom_ubundle_def)
            apply (simp add: fixABPHelperCont_ext_iter_dom f12 f13 f14)
            apply blast
           apply auto
            apply (simp add: ubclRestrict_ubundle_def)
            apply (simp only: innerABP_chain_shift_def)
            apply (simp only: two_times_simp_suc two_times_zero)

            apply (subst innerABP_apply_step)
    apply (simp only: ubclUnion_ubundle_def)
    apply (subst ubunion_getchR)
    apply (fold ubclDom_ubundle_def)
             apply (simp add: medrs_innerABP_chain_dom)
            apply (subst innerABP_apply_step)
    apply (simp only: ubclUnion_ubundle_def)
            apply (simp add: innerABP_chain_def)
            apply (simp only: ubclLeast_ubundle_def ubclRestrict_ubundle_def)
            apply (simp add: ubrestrict_ubleast_inter)

            apply (subst ubunion_restrict2)
             apply (fold ubclDom_ubundle_def)
    apply (subst ufran_2_ubcldom2)
    apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
    apply (fold ubclLeast_ubundle_def)
             apply (simp add: ubcldom_least_cs)

            apply (subst medrs_tspf_apply)
          apply simp
             apply (fold ubclDom_ubundle_def)
              apply (subst ufran_2_ubcldom2)
          apply (fold ubclUnion_ubundle_def)
               apply (simp add: ubclunion_ubcldom)
               apply (simp add: ubcldom_least_cs)
               apply (simp_all add: ubclDom_ubundle_def assms(2) sender_tspfdom sender_tspfran)
             apply (fold ubclDom_ubundle_def)
              apply (subst ufran_2_ubcldom2) +
               apply (simp add: ubclunion_ubcldom)
               apply (simp add: ubcldom_least_cs)
               apply (simp_all add: ubclDom_ubundle_def assms(2) sender_tspfdom sender_tspfran)
    apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
             apply (fold ubclDom_ubundle_def)
              apply (subst ufran_2_ubcldom2) +
               apply (simp add: ubclunion_ubcldom)
               apply (simp add: ubcldom_least_cs)
               apply (simp_all add: ubclDom_ubundle_def assms(2) sender_tspfdom sender_tspfran)
                apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
          using f13 sfilterl4 apply blast
            apply (subst ubgetch_ubrep_eq)
             apply (simp add: ubWell_def)
             apply (simp add: usclOkay_tstream_def)
             apply (simp add: tsmap_tsdom_range)
            apply simp
            apply (simp add: ubclLeast_ubundle_def)
            apply (simp add: ubclUnion_ubundle_def)
            apply (subst ubunion_getchR)

             apply (fold ubclDom_ubundle_def)
              apply (subst ufran_2_ubcldom2) +
               apply (simp_all add: ubclDom_ubundle_def assms(2) sender_tspfdom sender_tspfran)
                apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)




            apply (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
            apply (simp only: four_times_simp_suc four_times_zero)
            apply (simp only: ubclRestrict_ubundle_def )
            apply (subst ubgetch_ubrestrict)
             apply simp
            apply (simp only: fixABPHelperCont_ext_iter_4_c_as f12 f13 f14)
            apply (simp add: ubclLeast_ubundle_def)
            apply (subst senderTSPF_apply)
              apply (simp add: f13)
             apply (simp add: ubclUnion_ubundle_def assms(2))
             apply blast
            apply (subst medsr_tspf_apply)
              apply (subst ubdom_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply simp
          using f13 sfilterl4 apply blast
            apply (subst recvTSPF_apply)
          apply (simp add: ubclDom_ubundle_def)
              apply (subst ubdom_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
             apply (simp add: tsmap_tsdom_range)
          apply simp



            apply (simp add: ubclRestrict_ubundle_def)
            apply (simp add: innerABP_chain_shift_def)
            apply (subst innerABP_apply_step)
           apply (simp add: innerABP_c_abpOut)


            apply (subst senderTSPF_apply)
              apply (simp add: f13)
            apply (fold ubclDom_ubundle_def)
            apply (subst sender_tb_innerABP_dom)
            apply (simp add: sender_tspfdom)
          apply blast

            apply (subst medsr_tspf_apply)
              apply (subst ubdom_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply simp
          using f13 sfilterl4 apply blast
            apply (subst recvTSPF_apply)
          apply (simp add: ubclDom_ubundle_def)
              apply (subst ubdom_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
               apply (simp add: tsmap_tsdom_range)
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
             apply (simp add: tsmap_tsdom_range)
           apply simp
          apply (simp only: ubclUnion_ubundle_def)
           apply (subst ubunion_getchL)
          apply (fold ubclDom_ubundle_def)
            apply (simp add: ubclrestrict_dom innerABP_chain_def)
           apply (subst ubunion_getchR)       
          apply (fold ubclDom_ubundle_def)
            apply (simp only: ubclrestrict_dom innerABP_chain_def)
            apply (subst iter_ubfix2_dom)
             apply (fold ufunclComp_ufun_def)
             apply (simp add: f7)
            apply blast
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
            apply (simp add: tsmap_tsdom_range)
          apply simp

           apply (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
           apply (simp only: four_times_simp_suc four_times_zero)
           apply (simp only: ubclRestrict_ubundle_def)
           apply (subst ubgetch_ubrestrict)
            apply simp
           apply (subst ubgetch_ubrestrict)
            apply simp
           apply (simp only: fixABPHelperCont_ext_iter_3_c_abpOut f12 f13 f14)
           apply (simp only: fixABPHelperCont_ext_iter_2 f12 f13 f14)
           apply (simp only: fixABPHelperCont_ext_iter_1 f12 f13 f14)
           apply simp
           apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
           apply (simp add: ubclLeast_ubundle_def)
           apply (subst ubgetch_ubrep_eq)
            apply (simp add: ubWell_def)
            apply (simp add: usclOkay_tstream_def tsmap_tsdom_range)

           apply (subst innerABP_apply_step)
           apply (simp add: innerABP_c_as)
            apply (simp add: innerABP_chain_def)
            apply (simp add: ubclLeast_ubundle_def ubclRestrict_ubundle_def)
           apply (simp add: ubrestrict_ubleast_inter)
           apply (subst medrs_tspf_apply)
          apply simp
          using f13 sfilterl4 apply blast
              apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
           apply (simp add: tsmap_tsdom_range)
        proof -
          fix n::nat
          assume a1: "ubclRestrict {c_as, c_abpOut}\<cdot>(innerABP_chain_shift n) = abphelper_ext_chain_shift n"
          have s1: "innerABP_chain_shift n = innerABP_chain (Suc (Suc (2 * n)))"
            apply (simp add: innerABP_chain_shift_def)
            done
          have s2: "(abphelper_ext_chain_shift n) . c_as= 
(iterate (Suc (Suc (Suc (Suc ((4::nat) * n)))))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>
                                                             (ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut})) . c_as"
            apply (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
            apply (simp only: four_times_simp_suc four_times_zero)
            apply (simp only: ubclRestrict_ubundle_def)
            apply (rule ubgetch_ubrestrict)
            by simp
          have s3: "ubclRestrict {c_as, c_abpOut}\<cdot>(innerABP_chain_shift n) . c_as = (innerABP_chain_shift n) . c_as"
            by (simp add: ubclRestrict_ubundle_def)
          have f4: "(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>(abphelper_ext_chain_shift n) . c_as= 
(iterate (Suc (Suc (Suc (Suc (Suc ((4::nat) * n))))))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut))))))\<cdot>
                                         (ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}) . c_as"
            apply (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
            apply (simp only: four_times_simp_suc)
            apply (subst iterate_Suc)
            sorry
          obtain bla where bla_def: "bla = (iterate (Suc (Suc (Suc (Suc ((4::nat) * n)))))\<cdot>(\<Lambda> (x::'a MABP tstream\<^sup>\<Omega>). Abs_ubundle (ABPBundleHelper s ora1 ora2 tb x(c_idOut \<mapsto> tsMap Data\<cdot>(tsMap invData\<cdot>(x  .  c_abpOut)))))\<cdot>
                                          (ubclLeast {c_abpOut, c_ar, c_as, c_dr, c_ds, c_idOut}))"
            by simp
          show "ubclRestrict {c_as, c_abpOut}\<cdot>(innerABP_chain_shift (Suc n)) = abphelper_ext_chain_shift (Suc n)"
            apply (rule ub_eq)
             apply (fold ubclDom_ubundle_def)
             apply (simp_all add: f80)
             apply (simp only: abphelper_ext_chain_shift_def)
            apply (simp only: abphelper_ext_chain_def)
             apply (simp only: ubclrestrict_dom)
            apply (simp only: ubclDom_ubundle_def)
             apply (simp only: fixABPHelperCont_ext_iter_dom f12 f13 f14)
             apply blast
            apply auto
             apply (simp_all add: ubclRestrict_ubundle_def)
             apply (simp only: innerABP_chain_shift_def)
            apply (simp only: two_times_simp_suc)
             apply (subst innerABP_apply_step)
             apply (subst innerABP_c_as)


             apply (subst medrs_tspf_apply)
            apply (simp add: ubclRestrict_ubundle_def)
            apply (simp only: innerABP_chain_def)
               apply (fold ubclDom_ubundle_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
                apply (simp add: f7)
               apply blast
            using f13 sfilterl4 apply blast
            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
            apply (simp add: ubclRestrict_ubundle_def)

             apply (subst innerABP_apply_step)
             apply (subst innerABP_c_ar)

            apply (subst recvTSPF_apply)
              apply (subst ufran_2_ubcldom2) +
               apply (simp_all add: ubclDom_ubundle_def assms(2) sender_tspfdom sender_tspfran)
                apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
              apply (fold ubclDom_ubundle_def)
              apply (simp add: ubclunion_dom)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply (simp add: ubclDom_ubundle_def assms(2))
            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
             apply (subst medsr_tspf_apply)
            apply (fold ubclDom_ubundle_def)
               apply (subst ufran_2_ubcldom2) +
              apply (simp add: ubclunion_dom)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply (simp add: ubclDom_ubundle_def assms(2) sender_tspfdom)
               apply (simp add: sender_tspfran)
            using f13 sfilterl4 apply blast


            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
             apply (subst senderTSPF_apply)
               apply (simp add: f13)
            apply (fold ubclDom_ubundle_def)apply (simp add: ubclunion_dom)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply (simp add: ubclDom_ubundle_def assms(2) sender_tspfdom)
            apply blast


            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply (fold s1)
            apply (simp only: ubclUnion_ubundle_def)
             apply (subst ubunion_getchL)
              apply (fold ubclDom_ubundle_def)
            apply (simp add: ubclrestrict_dom)
             apply (subst ubunion_getchR)
              apply (fold ubclDom_ubundle_def)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_shift_def innerABP_chain_def)
              apply (subst iter_ubfix2_dom)
               apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply simp +
             apply (simp only: abphelper_ext_chain_shift_def abphelper_ext_chain_def)
             apply (simp only: ubclRestrict_ubundle_def)
             apply (subst ubgetch_ubrestrict)
            apply simp
             apply (subst ubgetch_ubrestrict)
            apply simp
             apply (simp only: four_times_simp_suc four_times_zero)
             apply (subst fixABPHelperCont_ext_iter_4_c_as)
                apply (simp add: f13)
               apply (simp add: f13)
              apply (simp add: f13)
             apply (fold s2) 
             apply (fold s3)
             apply (simp add: a1)
(*=======================================================================================*)
            apply (simp only: innerABP_chain_shift_def)
            apply (simp only: two_times_simp_suc)
            apply (subst innerABP_apply_step)
            apply (subst innerABP_c_abpOut)


            apply (subst recvTSPF_apply)
              apply (subst ufran_2_ubcldom2) +
               apply (simp_all add: ubclDom_ubundle_def assms(2) sender_tspfdom sender_tspfran)
                apply (simp_all add:  med_tspfran2 med_tspfdom2 f13 sender_tspfran  sender_tspfdom recv_tspfran recv_tspfdom)
              apply (fold ubclDom_ubundle_def)
              apply (simp add: ubclunion_dom)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply (simp add: ubclDom_ubundle_def assms(2))
            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
             apply (subst medsr_tspf_apply)
            apply (fold ubclDom_ubundle_def)
               apply (subst ufran_2_ubcldom2) +
              apply (simp add: ubclunion_dom)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply (simp add: ubclDom_ubundle_def assms(2) sender_tspfdom)
               apply (simp add: sender_tspfran)
            using f13 sfilterl4 apply blast


            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
              apply (simp add: tsmap_tsdom_range)
             apply simp
             apply (subst senderTSPF_apply)
               apply (simp add: f13)
            apply (fold ubclDom_ubundle_def)apply (simp add: ubclunion_dom)
              apply (simp add: ubclrestrict_dom)
              apply (simp only: innerABP_chain_def)
               apply (subst iter_ubfix2_dom)
                apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply (simp add: ubclDom_ubundle_def assms(2) sender_tspfdom)
            apply blast


            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
             apply (simp add: tsmap_tsdom_range)
            apply simp
            apply (simp only: ubclUnion_ubundle_def)
            apply (subst ubunion_getchL)
              apply (fold ubclDom_ubundle_def)
              apply (simp add: ubclrestrict_dom)
             apply (subst ubunion_getchR)
              apply (fold ubclDom_ubundle_def)
            apply (simp add: ubclrestrict_dom)
             apply (simp only: innerABP_chain_def)
             apply (subst iter_ubfix2_dom)
              apply (fold ufunclComp_ufun_def)
              apply (simp add: f7)
             apply simp
            apply (simp add: ubclRestrict_ubundle_def)
            apply (subst innerABP_apply_step)
            apply (subst innerABP_c_as)
            apply (fold s1)



            apply (simp only: abphelper_ext_chain_shift_def)
            apply (simp only: abphelper_ext_chain_def)
            apply (simp only: ubclRestrict_ubundle_def)
            apply (simp only: four_times_simp_suc)
            apply (subst ubgetch_ubrestrict)
             apply (simp)

            apply (subst fixABPHelperCont_ext_iter_3_c_abpOut)
               apply (simp add: f13)
              apply (simp add: f13)
             apply (simp add: f13)
            apply (subst fixABPHelperCont_ext_iter_2)
               apply (simp add: f13)
              apply (simp add: f13)
             apply (simp add: f13)
            apply (subst fixABPHelperCont_ext_iter_1)
               apply (simp add: f13)
              apply (simp add: f13)
             apply (simp add: f13)
            apply (subst iterate_Suc)
            apply (fold bla_def)
            apply (simp add: fixABPHelper_ext_cont f12 f13 f14)
            apply (subst ubgetch_ubrep_eq)
             apply (simp add: ABPBundleHelper_ext_ubWell)
            apply simp
            apply (subst medrs_tspf_apply)
              apply simp
              apply (simp only: innerABP_chain_shift_def innerABP_chain_def)
            apply (fold ubclDom_ubundle_def)
              apply (subst iter_ubfix2_dom)
               apply (fold ufunclComp_ufun_def)
               apply (simp add: f7)
              apply blast
            using f13 sfilterl4 apply blast
            apply simp
            apply (subst ubgetch_ubrep_eq)
               apply (simp add: ubWell_def)
               apply (simp add: usclOkay_tstream_def)
             apply (simp add: tsmap_tsdom_range)
            apply simp
            apply (simp only: bla_def)


            sorry
        qed
      show ?thesis
        apply (subst f0)
        sorry
    qed
    show ?thesis
      apply (simp add: ubFix_def)
      apply (fold abphelper_chain_def)
      apply (subst abphelper_N_ext_chain_eq)
      apply (fold ubFix_def)
      by (simp add: abphelper_ext_gencomp_eq)
    qed 
  paragraph \<open>proof end\<close>

  have f5: "(f \<rightleftharpoons> tb) . c_abpOut = (ubFix (fixABPHelperCont s ora1 ora2 tb) {c_abpOut, c_ar, c_as, c_dr, c_ds})  .  c_abpOut"
  proof - 
    have f51: "ufCompI (senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) (medRS_TSPF ora2) = {c_abpIn}"
      apply(simp add: ufCompI_def)
      apply(simp add: f20 f21)
     apply (simp add:  med_tspfran2 med_tspfdom2 f13)
      using f13 sfilterl4 by blast
    have f52: "(ufRan\<cdot>(senderTSPF s \<otimes> medSR_TSPF ora1 \<otimes> recvTSPF) \<union> ufRan\<cdot>(medRS_TSPF ora2)) = {c_ar, c_abpOut, c_dr, c_ds, c_as}"
      apply(simp add: f21, subst med_tspfran)
      using f13 sfilterl4 apply blast
       apply simp
      by auto
    show ?thesis
      apply(subst f14)
      apply(subst (1) ufunclComp_ufun_def)
      apply(simp add: ufComp_def)
      apply(subst rep_abs_cufun)
       apply(simp add:  ufcomp_cont)
       apply(rule ufcomp_well)
      sorry
  qed
  show ?thesis
    sorry
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