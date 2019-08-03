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
  apply(auto simp add: ctype_empty_gdw)
  using ctype_empty_gdw
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
abbreviation "buildAndinSBE \<equiv> inAndChan (Timed o map \<B>) (Tsyn o (map_option \<B>))" 

(* 
  Konstruktoren:
    \<^item> (Untimed o \<B>)
    \<^item> (Timed o map \<B>)
    \<^item> (Tsyn o (map_option \<B>))
*)



(* TODO: Mehr lemma über "inAndChan", damit das auch für "genSB" verwendet werden kann *)



lemma buildandin_ctype: "buildAndinSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a;simp)
  using ctype_def apply fastforce
  by(auto simp add: ctype_def)  (* TODO hilfslemma, damit das einfacher geht *)

lemma inj_h1:"inj (Timed o map \<B>)" 
  by (auto simp add: inj_def)

lemma inj_h2: "inj (Tsyn o (map_option \<B>))"
  apply(rule inj_compose)
   apply (simp add: inj_def)
  apply(rule option.inj_map)
  by (simp add: inj_def)

lemma buildandin_inj: "inj buildAndinSBE"
  apply (auto simp add: inj_def)
  by (metis inAndChan.simps inj_def inj_h1 inj_h2)+

lemma buildandin_range: "range (\<lambda>a. buildAndinSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  apply (meson ex_map_conv rangeE subset_iff)
  by (metis option.simps(9))
  

lemma buildandin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildAndinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildAndinSBE a c)"
    by (simp add: buildandin_range)
  hence "\<exists>prod. sbe = buildAndinSBE prod"
    apply(subst fun_eq_iff,auto simp add: ctype_def)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildAndinSB \<equiv> inAndChan (Rep_cfun (smap \<B>)) (Rep_cfun (smap \<B>))" 

end