(*<*)(*:maxLineLen=68:*)
theory inAndData

imports Data_inc
begin
(*>*)

subsection\<open>And component\<close> text\<open>label{sub:and}\<close>

text\<open>With the provided global channel and message datatypes we then
define the \<open>And\<close> component of the flasher. For this we need channel
datatypes, two bundle constructors that are interpreted in the
context of the \<open>sbeGen\<close> and \<open>sbGen\<close> local and the Automatons 
elements. Since everything generated for the channel types is 
analogous, only the input channel type is introduced explicitly.\<close>

subsubsection\<open>And Input Channel Type\<close>

text\<open>The \<open>And\<close> components has the two input channels @{const cin} 
and @{const cintern}.\<close>

typedef inAnd="{cin,cintern}"
  by auto

text\<open>It is then easily instantiated as a finite member of class 
@{class somechan} and then can be used as the domain of \glspl{sb}.\<close>

instance inAnd::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_inAnd 
        typedef_finite_UNIV by fastforce

instantiation inAnd::somechan
begin
  definition Rep_inAnd_def: "Rep = Rep_inAnd"

  lemma repand_range[simp]: "range (Rep::inAnd \<Rightarrow> channel) 
                           = {cin,cintern}"
  apply(subst Rep_inAnd_def)
  using type_definition.Rep_range type_definition_inAnd by fastforce
  
  instance
    apply(intro_classes)
    apply clarsimp
    unfolding Rep_inAnd_def by (meson Rep_inAnd_inject injI)
end

text\<open>Since @{const Rep_inAnd} is used as the @{const Rep} mapping of
class @{class chan}, @{type inAnd}s domain is equivalent to its 
type definition.\<close>

theorem inand_chdom[simp]: "chDom TYPE (inAnd) = {cin, cintern}"
  by (simp add: somechandom)

text\<open> Adding constructors for each channel of the domain eases the
converting from the channel type to type @{type inAnd} and vice 
versa by allowing pattern matching.\<close>

definition "Andin \<equiv> Abs_inAnd cin"
definition "Andintern \<equiv> Abs_inAnd cintern"

free_constructors inAnd for Andin | Andintern
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Andin_def Andintern_def
  apply (metis Rep_inAnd Rep_inAnd_inverse empty_iff insert_iff)
  apply (simp add: Abs_inAnd_inject)?
  done  (* Die "?" sind da, weil der Beweis für 1-port Datentypen 
  anders aussieht. Ich kann die "Eisbach" Dokumentation empfehlen! 
  Dort sind methoden beschrieben, um Beweise zu automatisieren *)

lemma andin_rep [simp]: "Rep Andin = cin"
  unfolding Rep_inAnd_def Andin_def
  by (simp add: Abs_inAnd_inverse)

lemma andintern_rep [simp]: "Rep Andintern = cintern"
  unfolding Rep_inAnd_def Andintern_def
  by (simp add: Abs_inAnd_inverse)




subsubsection \<open>Stream Bundle Constructors\<close>

text\<open>The usage of other datatypes beside @{type M} is possible by 
using converting constructors to construct a \gls{sb}. The 
converting part of the constructor maps arbitrary types to type 
@{type M}. Such constructors can be obtained by interpreting a 
constructor function in the context of locales @{locale sbeGen} or
@{locale sbGen}. The constructor function needed for the 
interpretation is defined with a helper function that uses a
converter for each different channel type and different converters 
for each of the locales.\<close>

(* Tuple:
      1. Value should go to port cin. It is of type "bool"
      2. Value should go to port cintern. It is of type "bool" 
*)

(* The first parameter is the converter from user-type 
  (here bool) to "M" 

  for every type in the tuple such a function must be in the 
  parameter. So if the tuple would consist of (nat\<times>bool) there are 
  2 converters required *)

text\<open>The helping constructor mapping has only generic types and 
@{type inAnd} in its signature.\<close>

fun inAndChan::"('bool \<Rightarrow> 'M) \<Rightarrow> ('bool\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'M" where
"inAndChan boolConv  (in1 , _ ) Andin     = boolConv in1"|
"inAndChan boolConv  ( _  ,in2) Andintern = boolConv in2"

text\<open>This allows the usage of @{const inAndChan} in both locale 
interpretations, only the converter functions are different. Because
we are in a timed environment it might be possible to get no 
boolean message.\<close> 

(* Helper Function for lemmata (mostly surj). Should be hidden from
the user! *)
definition %invisible inAndChan_inv::
            "('bool \<Rightarrow> 'M) \<Rightarrow> (inAnd \<Rightarrow> 'M) \<Rightarrow> ('bool\<times>'bool)" where
"inAndChan_inv boolConv f = 
              (inv boolConv (f Andin), inv boolConv (f Andintern))" 

lemma %invisible inAndChan_surj_helper: 
    assumes "f Andin \<in> range boolConv"
        and "f Andintern \<in> range boolConv"
  shows "inAndChan boolConv (inAndChan_inv boolConv f) = f"
  unfolding inAndChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

hide_const %invisible inAndChan_inv

lemma inAndChan_surj: 
    assumes "f Andin \<in> range boolConv"
        and "f Andintern \<in> range boolConv"
      shows "f \<in> range (inAndChan boolConv)"
  by (metis UNIV_I image_iff assms inAndChan_surj_helper)


lemma inAndChan_inj: assumes "inj boolConv"
  shows "inj (inAndChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms inAndChan.simps injD)+


text\<open>The converting function from a boolean optional message
realized by type @{type option} to a message of type @{type M} is 
input the input for our @{type sbElem} constructor used by locale
@{locale sbeGen}.\<close>

(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildAndInSBE \<equiv> inAndChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> inAnd \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)

text\<open>For the interpretation three properties must hold. First,
the output of the constructor has to be well typed for a 
@{type sbElem}. Second, the constructor has to be injective and 
third, the constructor has to be surjective to the @{type sbElem} 
type. This properties are proven in the following three theorems.\<close>

theorem buildandin_ctype[simp]: "buildAndInSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


theorem buildandin_inj[simp]: "inj buildAndInSBE"
  apply(rule inAndChan_inj)
  by simp

lemma buildandin_range:
  "range (\<lambda>a. buildAndInSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

theorem buildandin_surj[simp]: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildAndInSBE"
  apply(rule inAndChan_surj)
  apply (metis andin_rep assms rangecin)
(* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  by (metis andintern_rep assms rangecintern)

text\<open>The interpretation itself is then immediate.\<close>

interpretation andInSBE: sbeGen "buildAndInSBE"
  by %visible(unfold_locales,simp_all)

text\<open>The second constructor for locale @{locale sbGen} uses streams
of messages as its input. The converter then has to convert each 
message of the input streams analogous to the converter used in
@{const buildAndInSBE}.\<close>

abbreviation "buildAndInSB \<equiv> 
              inAndChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

text\<open>The three properties needed for a interpretation of 
@{locale sbGen} also the well typed output, and its bijectivity, but
of course for \glspl{sb} instead of @{type sbElem}s. They are 
defined in the following theorems.\<close>

theorem buildandinsb_ctype[simp]:
  "sValues\<cdot>(buildAndInSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

theorem buildandinsb_inj[simp]: "inj buildAndInSB"
  apply(rule inAndChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f" (*Move to stream.thy*)
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

theorem buildandinsb_surj[simp]: assumes "sb_well sb"
  shows "sb \<in> range buildAndInSB"
  apply(rule inAndChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecin apply simp
  using rangecintern apply simp
  done

text\<open>Again, the interpretation follows immediately from the proven
properties.\<close>

interpretation andInSB: sbGen "buildAndInSB"
  by(unfold_locales,simp_all)
(*<*)
end
(*>*)