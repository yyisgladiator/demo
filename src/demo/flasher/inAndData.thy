theory inAndData

imports bundle.SB
begin

typedef inAnd="{cin1,cin2}"
  by auto


instantiation inAnd::"{somechan,finite}"
begin
definition "Rep = Rep_inAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_inAnd_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_inAnd cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_inAnd_inject injI) using cMsg.elims Rep_inAnd apply simp
  apply (metis cMsg.simps emptyE image_iff iso_tuple_UNIV_I)
  using type_definition.Abs_image type_definition_inAnd typedef_finite_UNIV by fastforce
end

definition "Andin1 \<equiv> Abs_inAnd cin1"
definition "Andin2 \<equiv> Abs_inAnd cin2"

free_constructors inAnd for "Andin1"  | "Andin2"
  apply auto
  unfolding Andin1_def Andin2_def
  apply (metis Rep_inAnd Rep_inAnd_inverse empty_iff insert_iff)
  by (simp add: Abs_inAnd_inject)

lemma Andin1_rep [simp]: "Rep (Andin1) = cin1"
  by (simp add: Abs_inAnd_inverse Andin1_def Rep_inAnd_def)

lemma Andin2_rep [simp]: "Rep (Andin2) = cin2"
  unfolding Rep_inAnd_def Andin2_def
  by (simp add: Abs_inAnd_inverse)

fun inAndChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin1 = Cc1 port_c1" |
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin2 = Cc2 port_c2"


(* Ich wollte ein Beispiel mit verschiedenen Zeiten machen... normalerweise würde man nicht
  zwei verschiedene Zeit-Arten kombinieren... stört aber auch nicht *)

(* cin1 = gezeitet (mehrere Elemente pro Zeitscheibe)
   cin2 = zeitsynchron
*)
abbreviation "buildAndinSBE \<equiv> inAndChan (Tsyn o (map_option) \<B>) (Tsyn o (map_option \<B>))" 

(* 
  Konstruktoren:
    \<^item> (Untimed o \<B>)
    \<^item> (Timed o map \<B>)
    \<^item> (Tsyn o (map_option \<B>))
*)



(* TODO: Mehr lemma über "inAndChan", damit das auch für "genSB" verwendet werden kann *)



lemma buildandin_ctype: "buildAndinSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a;simp)
  by(simp_all add: ctype_def,auto)

lemma buildandin_inj: "inj buildAndinSBE"
  apply (auto simp add: inj_def)
  by (metis inAndChan.simps inj_def inj_B inj_tsyncons)+

lemma buildandin_range: "range (\<lambda>a. buildAndinSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildandin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildAndinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildAndinSBE a c)"
    by (simp add: buildandin_range)
  hence "\<exists>prod. sbe = buildAndinSBE prod"
    apply(simp add: fun_eq_iff f_inv_into_f image_iff) (*shorter surj proof*)
  proof -
    assume a1: "\<And>c. \<exists>a b. sbe c = buildAndinSBE (a, b) c"
    { fix ii :: "bool option \<Rightarrow> bool option \<Rightarrow> inAnd"
      obtain zz :: "inAnd \<Rightarrow> bool option" and zza :: "inAnd \<Rightarrow> bool option" where
        ff1: "\<forall>i. sbe i = buildAndinSBE (zz i, zza i) i"
        using a1 by moura
      then have "(\<exists>z. ii (zz Andin1) z \<noteq> Andin2) \<or> (\<exists>z za. sbe (ii z za) = buildAndinSBE (z, za) (ii z za))"
        by (metis (no_types) inAndChan.simps(2))
      then have "\<exists>z za. sbe (ii z za) = buildAndinSBE (z, za) (ii z za)"
        using ff1 by (metis (full_types) inAnd.exhaust inAndChan.simps(1)) }
    then show "\<exists>z za. \<forall>i. sbe i = buildAndinSBE (z, za) i"
      by metis
  qed
  thus ?thesis
    by auto
qed

abbreviation "buildAndinSB \<equiv> inAndChan (Rep_cfun (smap (Tsyn o (map_option) \<B>))) (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 


lemma buildandinsb_ctype: "sValues\<cdot>(buildAndinSB a c) \<subseteq> ctype (Rep c)"
 apply(cases c)
   apply auto
  using smap_sValues Andin1_rep inAndChan.simps
 
proof -
  fix x :: M
  assume a1: "x \<in> sValues\<cdot>(buildAndinSB a Andin1)"
  have f2: "\<forall>z. (Tsyn \<circ> map_option \<B>) z \<in> ctype cin1"
    by (metis (full_types) Andin1_rep buildandin_ctype inAndChan.simps(1))
  obtain ss :: "bool option stream \<times> bool option stream \<Rightarrow> bool option stream" where
    "x \<in> (Tsyn \<circ> map_option \<B>) ` sValues\<cdot>(ss a)"
    using a1 by (metis inAndChan.simps(1) old.prod.exhaust smap_sValues)
  then show "x \<in> ctype cin1"
    using f2 by fastforce
next
  fix x :: M
  assume a1: "x \<in> sValues\<cdot>(buildAndinSB a Andin2)"
  have f2: "\<forall>z. (Tsyn \<circ> map_option \<B>) z \<in> ctype cin2"
    by (metis (full_types) Andin2_rep buildandin_ctype inAndChan.simps(2))
  obtain ss :: "bool option stream \<times> bool option stream \<Rightarrow> bool option stream" where
    "x \<in> (Tsyn \<circ> map_option \<B>) ` sValues\<cdot>(ss a)"
    using a1 by (metis inAndChan.simps(2) old.prod.exhaust smap_sValues)
  then show "x \<in> ctype cin2"
    using f2 by fastforce
qed

lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap (Tsyn o (map_option) \<B>)))"
  apply(rule smap_inj)
  by simp


lemma buildandintsb_inj: "inj buildAndinSB"
  apply(rule injI)
 
  by (metis inAndChan.simps(1) inAndChan.simps(2) inj_eq old.prod.exhaust rep_cfun_smap_bool_inj)




lemma buildandintsb_range: "(\<Union>a. sValues\<cdot>(buildAndinSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto
  apply (metis (no_types, lifting) Andin1_rep buildandinsb_ctype contra_subsetD inAndChan.simps)
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  apply (smt Andin1_rep buildandin_range comp_apply f_inv_into_f inAndChan.elims rangeI)
  apply (metis (no_types, lifting) Andin2_rep buildandinsb_ctype contra_subsetD inAndChan.simps)
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)

  apply(smt Andin2_rep buildandin_range comp_apply f_inv_into_f inAndChan.elims rangeI)
  done



  
lemma buildandinsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildAndinSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildAndinSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
  proof -
    have f1: "\<forall>i M. sValues\<cdot>(sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
      by (metis ctypewell dual_order.trans)
    have f2: "ctype (Rep Andin1) \<subseteq> range(Tsyn o (map_option) \<B>)"
           apply(smt buildandin_range f_inv_into_f inAndChan.elims rangeI subsetI)
      done
    have  "ctype (Rep Andin2) \<subseteq> range(Tsyn o (map_option) \<B>)"
      
      apply(smt buildandin_range f_inv_into_f inAndChan.elims rangeI subsetI)
      done
    then show "\<exists>a b. \<forall>i. sb i = buildAndinSB (a,b) i"
      using f1 f2  by (smt inAnd.exhaust inAndChan.simps sValues_def smap_well)
  qed 
  thus ?thesis
    by auto
qed


end