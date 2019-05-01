theory TSPF_Demo
  
imports "../TStream" "../Channel" "../OptionCpo"
    
begin
default_sort message

   (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every TStream may only contain certain elements *)
definition tsb_well :: "(channel \<rightharpoonup> 'm tstream) => bool" where
"tsb_well f \<equiv> (\<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c)"

cpodef 'm :: message TSB = "{b :: channel \<rightharpoonup> 'm tstream . tsb_well b }"
  sorry

setup_lifting datatype_definition_m

definition tsbDom :: "'m TSB \<rightarrow> channel set" where
"tsbDom \<equiv> \<Lambda> tb. {}"
  

(* MINIMAL tickCount in all tStreams *)
definition tsbTickCount :: "'m TSB \<rightarrow> lnat" where
"tsbTickCount \<equiv>  \<Lambda> tb. 0"

abbreviation tsbTickCount_abbrv :: "'m TSB \<Rightarrow> lnat "  ("#\<surd>tsb _ ") where
" #\<surd>tsb tsb \<equiv> tsbTickCount\<cdot>tsb"

    

(* Wie in SPF definition *)
definition tspf_type:: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_type f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> tsbDom\<cdot>b = In) \<and> 
                            (b \<in> dom (Rep_cfun f) \<longrightarrow> tsbDom\<cdot>(the (f\<cdot>b)) = Out)"

definition tspf_well:: "('m TSB \<rightarrow> 'm TSB option) \<Rightarrow> bool" where
"tspf_well f \<equiv> tspf_type f \<and>
                (\<forall>b. (b \<in> dom (Rep_cfun f) \<longrightarrow> #\<surd>tsb b \<le> #\<surd>tsb (the (f\<cdot>b))))"

cpodef 'm :: message TSPF = "{f :: 'm TSB \<rightarrow> 'm TSB option. tspf_well f}"
  sorry

setup_lifting type_definition_TSPF

definition tsbGet :: "'m TSB \<Rightarrow> channel \<Rightarrow> 'm tstream" where
"tsbGet tb c \<equiv> \<bottom>"

abbreviation dummi :: "'m TSB \<Rightarrow> channel \<Rightarrow> 'm tstream "  ("_ . _") where
"tb . c \<equiv> tsbGet tb c"

abbreviation dummi2 :: "'m TSB \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB "  ("_ \<uplus> _") where
"f1 \<uplus> f2 \<equiv> f1"

abbreviation dummi3 :: "'m TSB \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB "  ("_ \<bar> _") where
"f1 \<bar> f2 \<equiv> f1"

(* wendet f auf tb an. Der input wird automatisch restricted *)
abbreviation dummi4 :: "'m TSPF \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB "  ("_\<rightleftharpoons>_") where
"f \<rightleftharpoons> tb \<equiv> tb"
  

definition tspfDom:: "'m TSPF \<rightarrow> channel set " where
"tspfDom \<equiv> \<Lambda> tb.  {}"

definition tsbFix::"('m TSB \<rightarrow> 'm TSB) \<Rightarrow> channel set \<Rightarrow> 'm TSB " where
"tsbFix f c = Abs_TSB (\<lambda> c. None)"

definition tspfIsStrong :: "'m TSPF \<Rightarrow> bool" where
"tspfIsStrong tf = True" (* ToDo *)

(* Returns "Some x" if the input is correct, "None" if the input is "wrong" and no TSPF can be produced *)
definition lift1x1TSPF :: " ('m tstream \<rightarrow> 'm tstream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> 'm TSPF option" where
"lift1x1TSPF f cIn cOut = Some (Abs_TSPF (\<Lambda> tb. None))"


lift_definition exampleTSPF :: "'m TSPF" is 
  "\<Lambda> tb. (tsbDom\<cdot>tb = {c1, c2}) \<leadsto> (Abs_TSB (\<lambda>c. (c=c3) \<leadsto> tsMap id \<cdot>(tb .c1)))"
  oops


definition tspfComp3 :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF" where
"tspfComp3 f1 f2 \<equiv> 
let I1 = tspfDom\<cdot>f1;
    I2 = tspfDom\<cdot>f2;
    I  = {};     (* ToDo: Input *)
    C  = {}      (* ToDo: All Channels *)
in Abs_TSPF (\<Lambda> tb. ((tsbDom\<cdot>tb = I) \<leadsto> (tsbFix (\<Lambda> z. (((f1 \<rightleftharpoons> z) \<uplus> (f2 \<rightleftharpoons> z)) \<uplus> tb)) C)))"

end