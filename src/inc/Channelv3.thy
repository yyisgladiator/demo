theory Channelv3

imports HOLCF
begin
default_sort type

section \<open>channel definition\<close>

datatype channel = c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | cbotNOPE | SomeBig nat

datatype M = nat | eps | B bool
instance M :: countable
  apply(intro_classes)
  by(countable_datatype)


text \<open>wird generiert\<close>
definition ctype :: "channel \<Rightarrow> M set" where 
"ctype  = undefined"

definition cEmpty :: "channel set" where
"cEmpty = {c. ctype c = {}}"

(* Axiom :D wird vom generator erfüllt*)
lemma ctype_ax1:"\<exists>c. ctype c = {}"
  oops (* Braucht man nur für "minus" Datentyp *)


class chan =
(* fixes Abs :: "channel \<Rightarrow> 'a" *)
fixes Rep :: "'a \<Rightarrow> channel"
(* assumes chan_type:"type_definition Rep Abs (range Rep)"  *)
assumes chan_botsingle:"\<And>c. (range Rep)\<subseteq> cEmpty \<or> (range Rep)\<inter>cEmpty = {}" (* TODO: geht das schöner ? *)
assumes chan_inj:"inj Rep"
begin

abbreviation "Abs \<equiv> inv Rep"
end


(*
(*example 1*)
typedef myPortIn = "{cbotNOPE}"
  apply auto
  done

instantiation myPortIn::chan
begin
definition "Abs = Abs_myPortIn"
definition "Rep = Rep_myPortIn"
instance
  apply(standard)
  oops
  using Abs_myPortIn_def Rep_myPortIn_def type_definition.Rep_range type_definition_myPortIn apply fastforce
  using Rep_myPortIn_def type_definition.Rep_range type_definition_myPortIn apply fastforce
  by simp
end


(*example 2*)
typedef myPortOut = "{c1,c2,c3}"
  apply auto
  done


section \<open>chan instantiations \<close>

instantiation myPortOut::chan
begin
definition "Abs = Abs_myPortOut"
definition "Rep = Rep_myPortOut"
instance
  apply(standard)
  oops
  using Abs_myPortOut_def Rep_myPortOut_def type_definition.Rep_range type_definition_myPortOut apply fastforce
  using Rep_myPortOut_def type_definition.Rep_range type_definition_myPortOut apply fastforce
  by simp
end

section \<open> rep abs chan lemmata \<close>

lemma repinrange[simp]:"Rep (c::'c::chan) = x \<Longrightarrow> x\<in> range(Rep::'c \<Rightarrow> channel)"
  by blast

lemma chan_eq[simp]:"Rep (c::'c::chan) = x \<Longrightarrow> x\<in> range(Rep::'d::chan \<Rightarrow> channel) 
                        \<Longrightarrow> Rep((Abs::channel \<Rightarrow> 'd)(Rep c)) = x"
  by (meson chan_type type_definition_def)

(*
instantiation channel :: chan 
begin 
definition "Abs == id" 
definition "Rep == (\<lambda> c. if c = cbot then c10 else c)"
instance
  apply intro_classes
  using type_definition.Rep_range type_definition_channel Abs_channel_def Rep_channel_def
  apply (smt channel.distinct(127) image_iff)
  by simp
end
*)
declare[[show_types]]
declare[[show_consts]]

section \<open>chan \<union> and - \<close>

typedef ('c1::chan, 'c2::chan) union (infixr "\<union>" 20) = "if range (Rep::'c1\<Rightarrow>channel)\<subseteq>cEmpty \<and>  range (Rep::'c2\<Rightarrow>channel)\<subseteq>cEmpty then cEmpty
                                                        else (range (Rep::'c1\<Rightarrow>channel) \<union> range (Rep::'c2\<Rightarrow>channel)) - cEmpty" 
   apply(auto)
  done

(* Axiom :/ *)
lemma "cEmpty \<noteq> {}"
  sorry

typedef ('c1::chan, 'c2::chan) minus (infixr "-" 20) = "(if range (Rep::'c1\<Rightarrow>channel) \<subseteq> range (Rep::'c2\<Rightarrow>channel) then cEmpty
                                                         else range (Rep::'c1\<Rightarrow>channel) - range (Rep::'c2\<Rightarrow>channel))" 
  sorry

lemma "False"
  oops

instantiation union :: (chan, chan) chan 
begin
definition "Abs == Abs_union"
definition "Rep == Rep_union"
instance
  apply intro_classes
  apply (smt Abs_union_def Rep_union_def type_definition.Rep_range type_definition_union)
  apply (smt Diff_iff Rep_union_def singletonD singletonI type_definition.Rep_range type_definition_union)
  by simp
end

section \<open> union range lemmata \<close>

lemma union_bot[simp]:"cbot \<in> range (Rep::'a::chan\<Rightarrow>channel) \<and> cbot \<in> range (Rep::'b::chan\<Rightarrow>channel) 
                       \<Longrightarrow> range (Rep::'a\<union>'b \<Rightarrow> channel) = {cbot}"
  by (smt Rep_union_def type_definition.Rep_range type_definition_union)

lemma union_notbot[simp]:"\<not>(cbot \<in> range (Rep::'a::chan\<Rightarrow>channel) \<and> cbot \<in> range (Rep::'b::chan\<Rightarrow>channel)) 
                          \<Longrightarrow> range (Rep::'a\<union>'b \<Rightarrow> channel) \<noteq> {cbot}"
  by (smt DiffE Rep_union_def singletonI type_definition.Rep_range type_definition_union)

lemma union_isunionwithoutbot[simp]:"\<not>(cbot \<in> range (Rep::'a::chan\<Rightarrow>channel) \<and> cbot \<in> range (Rep::'b::chan\<Rightarrow>channel)) 
                            \<Longrightarrow> range (Rep::'a\<union>'b \<Rightarrow> channel) = (range (Rep::'a::chan\<Rightarrow>channel)) \<union> range (Rep::'b::chan\<Rightarrow>channel) - {cbot}"
  by (smt DiffE Rep_union_def singletonI type_definition.Rep_range type_definition_union)


lemma union_isunion[simp]:"\<not>(cbot \<in> range (Rep::'a::chan\<Rightarrow>channel) \<or> cbot \<in> range (Rep::'b::chan\<Rightarrow>channel)) 
                            \<Longrightarrow> range (Rep::'a\<union>'b \<Rightarrow> channel) = (range (Rep::'a::chan\<Rightarrow>channel)) \<union> range (Rep::'b::chan\<Rightarrow>channel)"
  by simp


instantiation minus :: (chan, chan) chan 
begin
definition "Abs == Abs_minus"
definition "Rep == Rep_minus"
instance
  apply intro_classes
  apply (smt Abs_minus_def Rep_minus_def type_definition.Rep_range type_definition_minus)
  apply(case_tac "c \<in> range (Rep::'b \<Rightarrow> channel)")
  apply (smt Diff_iff Rep_minus_def singletonD type_definition.Rep_range type_definition_minus)
  apply (smt DiffD1 Rep_minus_def chan_botsingle singleton_iff type_definition.Rep_range type_definition_minus)
  by simp
end

section \<open> minus range lemmata \<close>

lemma minus_bot[simp]:"range (Rep::'a::chan\<Rightarrow>channel) \<subseteq> range (Rep::'b::chan\<Rightarrow>channel) 
                       \<Longrightarrow> range (Rep::'a-'b \<Rightarrow> channel) = {cbot}"
  by (smt Rep_minus_def type_definition.Rep_range type_definition_minus)

lemma minus_ismminus[simp]:"\<not>(range (Rep::'a::chan\<Rightarrow>channel) \<subseteq> range (Rep::'b::chan\<Rightarrow>channel)) 
                            \<Longrightarrow> range (Rep::'a-'b \<Rightarrow> channel) = (range (Rep::'a::chan\<Rightarrow>channel)) - range (Rep::'b::chan\<Rightarrow>channel)"
  by (smt Rep_minus_def type_definition.Rep_range type_definition_minus)

lemma minus_bot2[simp]:"range (Rep::'a::chan\<Rightarrow>channel) = {cbot}
                          \<Longrightarrow> range (Rep::'a-'b::chan \<Rightarrow> channel) = {cbot}"
  by (smt Diff_iff chan_notempty minus_bot minus_ismminus subsetI subset_singletonD)

*)
end