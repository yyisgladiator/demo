(*  Title:        ABP_TSPS.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  ABP modeled with TSPS
*)

theory ABP_TSPS
  imports "../../TSPS" Receiver Composition Medium "../../TSPF"

begin

  default_sort countable

(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)

datatype 'a::countable MABP = BoolPair "('a * bool)" | Bool bool | Data 'a

instantiation MABP ::  (countable) countable
begin
instance
   by (countable_datatype)
end

instantiation MABP ::  (countable) message
begin
fun ctype_MABP :: "channel \<Rightarrow> 'a MABP set" where
  "ctype_MABP abpIn = range Data" |
  "ctype_MABP abpOut = range Data" |
  "ctype_MABP ds = range BoolPair" |
  "ctype_MABP dr = range BoolPair" |
  "ctype_MABP as = range Bool" |
  "ctype_MABP ar = range Bool" |
  "ctype_MABP other = undefined"

  instance ..
end

 declare [[show_types]]
  declare [[show_sorts]]
declare [[show_consts]]

(* ----------------------------------------------------------------------- *)
section \<open>Definitions\<close>
(* ----------------------------------------------------------------------- *)

subsection \<open>datatype destructors\<close>
abbreviation invBoolPair :: "'a MABP \<Rightarrow> ('a \<times> bool)" where
"invBoolPair \<equiv> (inv BoolPair)"

abbreviation invBool :: "'a MABP \<Rightarrow> bool" where
"invBool \<equiv> (inv Bool)"

abbreviation invData :: "'a MABP \<Rightarrow> 'a" where
"invData \<equiv> (inv Data)"

abbreviation recvAbb where
"recvAbb \<equiv>
let recRes = (\<lambda> x. tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr)))
in (\<lambda> x. (tsbDom\<cdot>x = {dr}) \<leadsto> [ar    \<mapsto> tsMap Bool\<cdot>(fst (recRes x)),
                                        abpOut \<mapsto> tsMap Data\<cdot>(snd (recRes x))]\<Omega>)"


subsection \<open>receiver\<close>
definition recvTSPF :: "'a MABP TSPF" where
"recvTSPF \<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {dr}) \<leadsto> [ar    \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr)))),
                                        abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream) Data\<cdot>(snd ( tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr))))]\<Omega>)"

subsection \<open>medium_rs\<close>
  (* medium from receiver to sender *)
  (* input: ar, output: as, transport booleans *)

definition tsMedRSTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedRSTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"

abbreviation tsMedRSAbb  :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP TSB option" where
"tsMedRSAbb bst x \<equiv> ((tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"

subsection \<open>medium_sr\<close>
  (* medium from sender to receiver *)
  (* input: ds, output: dr, transport (data, bool) tuples *)


  (* TODO: fix types *)
definition tsMedSRTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedSRTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {ds})
                                \<leadsto> [dr \<mapsto> tsMap BoolPair\<cdot>(tsMed\<cdot>(tsMap invBoolPair\<cdot>(x . ds))\<cdot>bst)]\<Omega>)"


(* ----------------------------------------------------------------------- *)
section \<open>lemmata\<close>
(* ----------------------------------------------------------------------- *)

subsection \<open>general\<close>

lemma tsmap_id[simp]: assumes "inj f" shows "tsMap (inv f)\<cdot>(tsMap f\<cdot>ts) = ts"
apply(induction ts)
by(simp_all add: assms tsmap_delayfun  tsmap_mlscons)

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
definition recvCH1 :: "'a MABP TSB \<Rightarrow> 'a MABP tstream"  where
"recvCH1 \<equiv> (\<lambda> x. tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .dr)))))"

definition recvCH2 :: "'a MABP TSB \<Rightarrow> 'a MABP tstream"  where
"recvCH2 \<equiv> (\<lambda> x. tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .dr)))))"

lemma recvCH1_contlub: assumes "chain Y"
  shows "recvCH1 ((\<Squnion>i. Y i)) = (\<Squnion>i. (recvCH1 ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms recvCH1_def)

lemma recvCH2_contlub: assumes "chain Y"
  shows "recvCH2 ((\<Squnion>i. Y i)) = (\<Squnion>i. (recvCH2 ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms recvCH2_def)


lemma to_recvch1: "tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .dr))))
                    = (recvCH1::'a MABP TSB \<Rightarrow> 'a MABP tstream) x"
  by (simp add: recvCH1_def)

lemma to_recvch2: "tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x .dr))))
                    = (recvCH2::'a MABP TSB \<Rightarrow> 'a MABP tstream) x"
  by (simp add: recvCH2_def)





lemma recv_tsb_well [simp]:
  shows "tsb_well [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr)))),
                                  abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr))))]"
  apply (rule tsb_wellI)
  apply (simp add: tsmap_tsdom_range)
  by blast

lemma recv_tsb_dom: "tsbDom\<cdot>([ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr)))),
                              abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr))))]\<Omega>)
                     = {ar, abpOut}"
  apply (simp add: tsbdom_rep_eq)
    by auto



lemma rec_tsb_mono: "\<And>(x::'a MABP TSB) y::'a MABP TSB. tsbDom\<cdot>x = {dr} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow>
          [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  dr)))),
          abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  dr))))]\<Omega>
          \<sqsubseteq> [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  dr)))),
             abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  dr))))]\<Omega>"
      apply (rule tsb_below)
       apply (simp_all add: tsbdom_below tsbdom_rep_eq tsbgetch_rep_eq)
       by (simp add: fst_monofun snd_monofun monofun_cfun_arg tsbgetch_below)


lemma recvTSPF_mono [simp]: "monofun (\<lambda> x. (tsbDom\<cdot>x = {dr}) \<leadsto>
                                    [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr)))),
                                     abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr))))]\<Omega>)"
  apply (rule tspf_monoI)
  apply (rule tsb_below)
   apply (simp_all add: tsbdom_below tsbdom_rep_eq tsbgetch_rep_eq)
   by (simp add: fst_monofun snd_monofun monofun_cfun_arg tsbgetch_below)


lemma recvTSPF_tsb_getc: assumes "chain Y" and "tsbDom\<cdot>(\<Squnion>i. Y i) = {dr}"
  and "c \<in>  {ar, abpOut}"
  shows " (\<Squnion>i.
           [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))), abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr))))]\<Omega>) . c
          = (\<Squnion> i. ([ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))), abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr))))]\<Omega>) . c)"
proof (rule lubgetCh)
   have f2: "\<And> i. tsbDom\<cdot>(Y i) =  tsbDom\<cdot>(\<Squnion>i. Y i)"
     by (simp add: assms(1))
   show tb_chain: "chain (\<lambda>i::nat. [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))),
                             abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr))))]\<Omega>)"
     by (simp add: assms(1) assms(2) po_class.chainE po_class.chainI rec_tsb_mono)

   show " c \<in> tsbDom\<cdot>(\<Squnion>i::nat.
                          [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))),
                       abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr))))]\<Omega>)"
     using assms(3) recv_tsb_dom tb_chain tsbChain_dom_eq2 by blast
qed



  (* show that recTSPF is cont, proof concept taken from TSPF_Template_CaseStudy *)
lemma recvTSPF_cont [simp]:
  shows "cont (\<lambda> x. (tsbDom\<cdot>x = {dr}) \<leadsto>
                      [ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(x . dr)))),
                       abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr))))]\<Omega>)"
  proof (rule tspf_contI)
    show recv_mono: "\<And>(x::'a MABP TSB) y::'a MABP TSB. tsbDom\<cdot>x = {dr} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow>
          [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  dr)))),
          abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(x  .  dr))))]\<Omega>
          \<sqsubseteq> [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  dr)))),
             abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(y  .  dr))))]\<Omega>"
      by (simp add: rec_tsb_mono)

    have f1: " \<And>Y::nat \<Rightarrow> 'a MABP TSB. chain Y \<Longrightarrow> tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {dr} \<Longrightarrow>
                tsbDom\<cdot>(\<Squnion>i::nat. [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))),
                abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr))))]\<Omega>) = {abpOut, ar}"
     proof -
      fix Y :: "nat \<Rightarrow> 'a MABP TSB"
      assume a1: "chain Y"
      assume a2: "tsbDom\<cdot>(\<Squnion>i. Y i) = {dr}"
      have f3: "\<forall>t ta. (tsbDom\<cdot>t \<noteq> {dr} \<or> t \<notsqsubseteq> ta)
                        \<or> [ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(t . dr)))),
                            abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot> (t . dr)))::'a tstream)]\<Omega>
                          \<sqsubseteq> [ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(ta . dr)))),
                              abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(ta . dr))))]\<Omega>"
        using recv_mono by blast
      have f4: "\<forall>f n. \<not> chain f \<or> tsbDom\<cdot>(f n::'a MABP TSB) = tsbDom\<cdot>(Lub f)"
        by (meson tsbChain_dom_eq2)
      have f5: "\<And> elem_1 .tsbDom\<cdot> ([ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y elem_1 . dr))))
                          , abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot>(Y elem_1 . dr))))]\<Omega>)
                          = {ar, abpOut}"
        by (simp add: recv_tsb_dom)
      have "\<And> v1_0. tsbDom\<cdot> (Y (v1_0 (\<lambda>n. [ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y n . dr)))),
                                           abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot> (tsMap invBoolPair\<cdot>(Y n . dr))))]\<Omega>))) = {dr}"
        using f4 a2 a1 by presburger
      then have "chain (\<lambda>n. [ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y n . dr)))),
                             abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y n . dr))))]\<Omega>)"
        using f3 a1 by (simp add: po_class.chain_def)
      then show "tsbDom\<cdot> (\<Squnion>n. [ar \<mapsto> tsMap Bool\<cdot> (fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y n . dr)))),
                               abpOut \<mapsto> tsMap Data\<cdot> (snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y n . dr))))]\<Omega>) = {abpOut, ar}"
        using f5 f4 by blast
    qed


    have f3: "\<And>(Y::nat \<Rightarrow> 'a MABP TSB) c::channel. chain Y \<Longrightarrow> tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {dr}
              \<Longrightarrow> c = ar \<or> c = abpOut \<Longrightarrow> c = ar \<longrightarrow>
              (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Lub Y  .  dr))))
              \<sqsubseteq> (\<Squnion>i::nat. tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))))"
     by (simp add: recvCH1_contlub to_recvch1)

   have f4: "\<And>(Y::nat \<Rightarrow> 'a MABP TSB) c::channel. chain Y \<Longrightarrow> tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {dr}
               \<Longrightarrow> c = ar \<or> c = abpOut \<Longrightarrow> c = ar \<longrightarrow>
              tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Lub Y  .  dr))))
               \<sqsubseteq> (\<Squnion>i::nat. tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))))"
    by (simp add: recvCH2_contlub to_recvch2)

    show "\<And>Y::nat \<Rightarrow> 'a MABP TSB.
       chain Y \<Longrightarrow>
       tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {dr} \<Longrightarrow>
       [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  dr)))), abpOut \<mapsto>
        tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>((\<Squnion>i::nat. Y i)  .  dr))))]\<Omega> \<sqsubseteq>
       (\<Squnion>i::nat.
           [ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr)))), abpOut \<mapsto>
            tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(Y i  .  dr))))]\<Omega>)"
      apply (rule tsb_below)
       apply (simp_all add: tsbdom_below tsbdom_rep_eq tsbgetch_rep_eq f1)
      apply (simp add: recvTSPF_tsb_getc tsbdom_rep_eq tsbgetch_rep_eq)
      using f3 f4 by fastforce
  qed


  subsubsection \<open>tspf_well\<close>

 (* show that the recvTSPF fulfills the tickcount property *)
lemma recvTSPF_tick: assumes "tsbDom\<cdot>b = {dr}" and "(#\<surd>tsb b) = n"
  shows "n \<le> (#\<surd>tsb ([ar \<mapsto> tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  dr)))),
                       abpOut \<mapsto> tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  dr))))]\<Omega>))"
proof -
  have "(#\<surd>tsb b) = #\<surd>(b . dr)"
    apply (rule tsbtick_single_ch2)
     by (simp add: assms(1))
  hence f1: "n = #\<surd>(b . dr)"
     using assms(2) by blast
  hence f2: "n \<le> #\<surd>(tsMap Bool\<cdot>(fst (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  dr)))))"
    by (simp add: tsrec_insert)
  with f1 have f3: "n \<le> #\<surd>(tsMap Data\<cdot>(snd (tsRec\<cdot>(tsMap invBoolPair\<cdot>(b  .  dr)))))"
    by (simp add: tsrec_insert)
  show ?thesis
    apply (rule tsbtick_geI)
      apply (simp_all add: recv_tsb_dom)
      apply (simp add: tsbgetch_rep_eq)
      using f2 f3 by auto
qed


  (* recvTSPF is an actual TSPF *)
lemma recvTSPF_well:
  shows "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = {dr}) \<leadsto>
                      [ar \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                            Bool\<cdot>(fst ((tsRec::('a * bool) tstream \<rightarrow> (bool tstream \<times> 'a tstream))\<cdot>
                            ((tsMap invBoolPair)\<cdot>(x . dr)))),
                       abpOut \<mapsto> (tsMap::('a \<Rightarrow> 'a MABP) \<Rightarrow> 'a tstream \<rightarrow> 'a MABP tstream)
                            Data\<cdot>(snd (tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr))))]\<Omega>)"
  apply (rule tspf_wellI)
    apply (simp_all add: domIff2 recv_tsb_dom)
    by (simp add: recvTSPF_tick)




  subsection \<open>medium_rs\<close>

(*

definition tsMedRSTSPF :: "bool stream \<Rightarrow> 'a MABP TSPF" where
"tsMedRSTSPF bst\<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"

abbreviation tsMedRSAbb  :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP TSB option" where
"tsMedRSAbb bst x \<equiv> ((tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"

*)
subsubsection \<open>defs\<close>

definition medRSH :: "bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP tstream"  where
"medRSH bst \<equiv> (\<lambda> x. (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  ar))\<cdot>bst))"

lemma medrsh_cont [simp]: "cont (medRSH bst)"
  by (simp add: medRSH_def)

lemma medrsh_contlub: assumes "chain Y"
  shows "(medRSH bst) ((\<Squnion>i. Y i)) = (\<Squnion>i. ((medRSH bst) ((Y i))))"
  apply (rule cont2contlubE)
  by (simp_all add: assms)

lemma to_medrsh: "tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  ar))\<cdot>bst)
                  = ((medRSH :: bool stream \<Rightarrow> 'a MABP TSB \<Rightarrow> 'a MABP tstream) bst) x"
  by (simp add: medRSH_def)

subsubsection \<open>pre\<close>

lemma tsmed_input_cont [simp]: "cont (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  by simp

lemma tsmed_input_mono [simp]: "monofun (\<lambda> x. tsMed\<cdot>x\<cdot>bst)"
  using cont2mono tsmed_input_cont by blast


lemma medrs_tsb_well [simp]: "tsb_well  [as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]"
  apply (rule tsb_wellI)
  by (simp add: tsmap_tsdom_range)

lemma medrs_tsb_dom: "tsbDom\<cdot>([as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>) = {as}"
  by (simp add: tsbdom_rep_eq)


subsubsection \<open>cont\<close>

  (* prerequirement for the mono proofs of the tspf *)
lemma medrs_tsb_mono: "\<And>(x::'a MABP TSB) y::'a MABP TSB.
       tsbDom\<cdot>x = {ar} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x  .  ar))\<cdot>bst)]\<Omega> \<sqsubseteq> [as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(y  .  ar))\<cdot>bst)]\<Omega>"
  apply (simp_all add: tsbdom_below tsbdom_rep_eq tsbgetch_rep_eq)
  apply (rule tsb_below)
    apply (simp_all add: tsbdom_below tsbdom_rep_eq  tsbgetch_rep_eq)
    apply (simp add: to_medrsh)
    using cont2mono medrsh_cont monofun_def by blast


lemma medrs_mono [simp]: "monofun (\<lambda> x::'a MABP TSB. (tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"
  apply (rule tspf_monoI)
  by (simp add: medrs_tsb_mono)

lemma medrs_tsb_getc: assumes "chain (Y::nat \<Rightarrow> 'a MABP TSB)" and "tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {ar}"
                      and "c = as"
  shows "(\<Squnion>i::nat. [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  ar))\<cdot>bst)]\<Omega>)  .  as
          =  (\<Squnion>i::nat. ([as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  ar))\<cdot>bst)]\<Omega>) . as)"
proof (rule lubgetCh)
  have f2: "\<And> i. tsbDom\<cdot>(Y i) =  tsbDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  show tb_chain: "chain (\<lambda>i::nat. [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  ar))\<cdot>bst)]\<Omega>)"
    by (simp add: assms(1) assms(2) po_class.chainE po_class.chainI medrs_tsb_mono)
  show "as \<in> tsbDom\<cdot>(\<Squnion>i::nat. [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  ar))\<cdot>bst)]\<Omega>)"
    using assms(3) medrs_tsb_dom tb_chain tsbChain_dom_eq2 by blast
qed



lemma medrs_cont [simp]: "cont (\<lambda> x::'a MABP TSB. (tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"
proof (rule tspf_contI)
  show medrs_mo : "\<And>(x::'a MABP TSB) y::'a MABP TSB. tsbDom\<cdot>x = {ar} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow>
          [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>
                  (tsMed\<cdot>(tsMap invBool\<cdot>(x  .  ar))\<cdot>bst)]\<Omega>
          \<sqsubseteq> [as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(y  .  ar))\<cdot>bst)]\<Omega>"
    by (simp add: medrs_tsb_mono)

  have f1: " \<And>Y::nat \<Rightarrow> 'a MABP TSB. chain Y \<Longrightarrow> tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {ar} \<Longrightarrow>
       tsbDom\<cdot>(\<Squnion>i::nat. [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  ar))\<cdot>bst)]\<Omega>) = {as}"
    by (metis (mono_tags, lifting) medrs_mo medrs_tsb_dom po_class.chainE po_class.chainI tsbChain_dom_eq2)


  show "\<And>Y::nat \<Rightarrow> 'a MABP TSB. chain Y \<Longrightarrow> tsbDom\<cdot>(\<Squnion>i::nat. Y i) = {ar} \<Longrightarrow>
       [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>((\<Squnion>i::nat. Y i)  .  ar))\<cdot>bst)]\<Omega> \<sqsubseteq> (\<Squnion>i::nat. [as \<mapsto> tsMap Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(Y i  .  ar))\<cdot>bst)]\<Omega>)"
    apply (rule tsb_below)
      apply (simp_all add: tsbdom_below tsbdom_rep_eq tsbgetch_rep_eq f1)
      apply (simp add: medrs_tsb_getc tsbdom_rep_eq tsbgetch_rep_eq)
       by (simp add: medrsh_contlub to_medrsh)
qed


  subsubsection \<open>tspf_well\<close>
  
 (* show that the mediumRSTSPF template  fulfills the tickcount property *)
lemma medrs_tick: assumes "tsbDom\<cdot>b = {ar}" and "(#\<surd>tsb b) = n" and "#bst=\<infinity>"
  shows "n \<le> (#\<surd>tsb [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(b  .  ar))\<cdot>bst)]\<Omega>)"
proof -
  have "(#\<surd>tsb b) = #\<surd>(b . ar)"
    apply (rule tsbtick_single_ch2)
    by (simp add: assms(1))
  hence f1: "n = #\<surd>(b . ar)"
    using assms(2) by blast
  hence f2: "n \<le> #\<surd>((tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream) Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(b  .  ar))\<cdot>bst))"
    by (simp add: assms(3))
  show ?thesis
    apply (rule tsbtick_geI)
    apply (simp add: medrs_tsb_dom tsbgetch_rep_eq)
    using f2 by force
qed
  
      
    
  (* a medium is a tspf if the oracle bool stream bst is infinitly long*)
lemma medrs_well: assumes "#bst=\<infinity>"
shows "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = {ar})
                           \<leadsto> [as \<mapsto> (tsMap::(bool \<Rightarrow> 'a MABP) \<Rightarrow> bool tstream \<rightarrow> 'a MABP tstream)
                                Bool\<cdot>(tsMed\<cdot>(tsMap invBool\<cdot>(x . ar))\<cdot>bst)]\<Omega>)"
  apply (rule tspf_wellI)
    apply (simp_all add: domIff2 medrs_tsb_dom)
    apply (subst tsbtick_single_ch1, simp)
    by (simp add: assms tsbtick_single_ch2)
    
end