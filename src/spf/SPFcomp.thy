theory SPFcomp

imports bundle.SB
begin

section \<open>General composition\<close>

subsection \<open>General composition definition\<close>

(*cbot werden nicht verbunden; cbot können nur bei der eingabe vorkommen (bei der ausgabe nicht vorgesehen, siehe BDD92 Kap3.4)*)
(*now with magic*)
definition genComp :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<rightarrow> 'E\<^sup>\<Omega> \<rightarrow> 'F\<^sup>\<Omega>"  where
"genComp \<equiv> \<Lambda> spf1 spf2 sbIn . fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) \<uplus>\<^sub>\<star> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"

subsection \<open>General composition abbreviation\<close>
 (* inifxr \<otimes> ... without magic*)
abbreviation genComp_abbr :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" (infixr "\<otimes>" 70) where 
"spf1 \<otimes> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"


definition spfConvert::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>)" where
"spfConvert = (\<Lambda> f sb. (f\<cdot>(sb\<star>))\<star>)"   (* TODO: weniger klammern + warnings *)

lemma spfcomp_eql[simp]: "genComp\<cdot>f\<cdot>g = f"
  apply(simp add: genComp_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  by simp+


(* TODO; Move *)
definition chDom::"'cs itself \<Rightarrow> channel set" where
"chDom a = (range (Rep::'cs \<Rightarrow> channel)) - cEmpty"

lemma chdom_minus: "chDom (TYPE('cs1 - 'cs2)) = chDom (TYPE ('cs1)) - chDom (TYPE('cs2))"
  apply(simp add: chDom_def Rep_minus_def)
  apply auto
  apply (meson Diff_iff Rep_minus)
  apply (metis DiffE Rep_minus repinrange)
proof -
  fix xa :: 'cs1
  assume a1: "Rep xa \<notin> range (\<lambda>x. Rep (x::'cs2))"
  then have f2: "\<not> range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> range (Rep::'cs2 \<Rightarrow> channel)"
    by (metis repinrange subsetD)
  have "range (Rep_minus::'cs1 - 'cs2 \<Rightarrow> channel) = (if range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> range (Rep::'cs2 \<Rightarrow> channel) then cEmpty else range (Rep::'cs1 \<Rightarrow> channel) - range (Rep::'cs2 \<Rightarrow> channel))"
    using type_definition.Rep_range type_definition_minus by blast
  then show "Rep xa \<in> range (\<lambda>m. Rep_minus (m::'cs1 - 'cs2))"
    using f2 a1 by (metis (full_types) DiffI repinrange)
qed

lemma "chDom (TYPE('cs1 - 'cs2)) \<inter> chDom (TYPE ('cs2)) = {}"
  by(auto simp add: chdom_minus )

lemma ubunion_commu:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
    assumes "chDom (TYPE ('cs1)) \<inter> chDom (TYPE ('cs2)) = {}"
    shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb2 \<uplus>\<^sub>\<star> sb1)::'cs3\<^sup>\<Omega>)"
  apply(rule sb_eqI)
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))")
  using assms apply auto[1]
  sorry

(* Solange output disjunkt *)
lemma spfcomp_commut: 
      fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
     shows  "genComp\<cdot>f\<cdot>g = genComp\<cdot>g\<cdot>f"
  apply(rule cfun_eqI)
  apply(simp add: genComp_def)
  apply(rule arg_cong [of _ _ "Rep_cfun fix"])
  apply(rule cfun_eqI, simp)
  apply(rule ubunion_commu)
  by(simp add: assms)

lemma spfcomp_eqr[simp]:
      fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
      shows "genComp\<cdot>f\<cdot>g = g"
  apply(subst spfcomp_commut)
  by(simp add: assms)+

lemma spfconvert_eq [simp]: "spfConvert\<cdot>f = f"
  apply(rule cfun_eqI)
  by(simp add: spfConvert_def)

lemma "genComp\<cdot>f\<cdot>g = spfConvert\<cdot>(f \<otimes> g)"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
   apply auto
  apply(rule sb_eqI)
  oops 

lemma ubunion_id[simp]: "out\<star> \<uplus> (out\<star>) = out"
  apply(rule sb_rep_eqI)
  apply(auto simp add: Abs_sb_inverse sbunion_insert sbgetch_insert)
  sorry

lemma  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"

      fixes out::"('fOut \<union> 'gOut)\<^sup>\<Omega>"
assumes "f\<cdot>(sb \<uplus>\<^sub>\<star> out) = out\<star>"
    and "g\<cdot>(sb \<uplus>\<^sub>\<star> out) = out\<star>"
      shows "((f\<otimes>g)\<cdot>sb) \<sqsubseteq> out"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule fix_least)
  by (simp add: assms)

lemma spfcomp2gencomp  [simp]: "spfConvert\<cdot>(f \<otimes> g) = genComp\<cdot>f\<cdot>g"
  oops

lemma spfcomp_surj: obtains f g where "f \<otimes> g = x"
  oops

definition spsComp::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set"  where
"spsComp F G = {f \<otimes> g | f g. f\<in>F \<and> g\<in>G }"

lemma fixes P::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> bool"
        and H::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> bool"
      assumes "chDom (TYPE ('O1)) \<inter> chDom (TYPE ('O2)) = {}"
      shows  "spsComp {x. P x} {x. H x} = {x. P (spfConvert\<cdot>x) \<and> H (spfConvert\<cdot>x)}"
  apply (auto simp add: spsComp_def)
  oops
(*  by (metis spfcomp2gencomp spfcomp_eql spfcomp_eqr spfcomp_surj) *)
(* Gegenbeispiel ... soweit ich sehe: 
    P = H = "ist schwachkausal"
    bleibt nicht unter der feedbackkomposition erhalten *)

end