theory Channel

imports HOLCF user.Datatypes
begin


definition cEmpty :: "channel set" where
"cEmpty = {c. ctype c = {}}"


class chan =
  fixes Rep :: "'a \<Rightarrow> channel"


  assumes chan_botsingle:
      "(range Rep) \<subseteq> cEmpty 
           \<or> (range Rep) \<inter> cEmpty = {}" 

  assumes chan_inj[simp]:"inj Rep"

begin

  abbreviation "Abs \<equiv> inv Rep"
end

section \<open>chan Predicate definition\<close>

definition chIsEmpty ::"'cs::chan itself \<Rightarrow> bool" where
"chIsEmpty cs = (range(Rep::'cs\<Rightarrow>channel) \<subseteq> cEmpty)"


section \<open> rep abs chan lemmata \<close>

lemma repinrange[simp]:"Rep (c::'c::chan) = x \<Longrightarrow> x\<in> range(Rep::'c \<Rightarrow> channel)"
  by blast

lemma chan_eq[simp]:"Rep (c::'c::chan) = x \<Longrightarrow> x\<in> range(Rep::'d::chan \<Rightarrow> channel) 
                        \<Longrightarrow> Rep((Abs::channel \<Rightarrow> 'd)(Rep c)) = x"
  by (simp add: f_inv_into_f)




declare[[show_types]]
declare[[show_consts]]

section \<open>chan \<union> and - \<close>

typedef ('c1::chan, 'c2::chan) union (infixr "\<union>" 20) = "if range (Rep::'c1\<Rightarrow>channel)\<subseteq>cEmpty \<and>  range (Rep::'c2\<Rightarrow>channel)\<subseteq>cEmpty then cEmpty
                                                        else (range (Rep::'c1\<Rightarrow>channel) \<union> range (Rep::'c2\<Rightarrow>channel)) - cEmpty" 
   apply(auto)
  done

(* Axiom :/ *)
lemma cempty_exists: "cEmpty \<noteq> {}"
  apply(simp add: cEmpty_def)
  using ctype.simps(3) by blast

typedef ('c1::chan, 'c2::chan) minus (infixr "-" 20) = "(if range (Rep::'c1\<Rightarrow>channel) \<subseteq> range (Rep::'c2\<Rightarrow>channel) then cEmpty
                                                         else range (Rep::'c1\<Rightarrow>channel) - range (Rep::'c2\<Rightarrow>channel))" 
apply(cases "range Rep \<subseteq> range Rep", auto)
  using cempty_exists by blast+

instantiation union :: (chan, chan) chan 
begin
definition "Rep == Rep_union"
instance
  apply intro_classes
  apply auto
  apply (metis (full_types) Diff_iff Rep_union Rep_union_def)
  by (simp add: Channel.Rep_union_def Rep_union_inject inj_on_def)
end

instantiation minus :: (chan, chan) chan 
begin
definition "Rep == Rep_minus"
instance
  apply intro_classes
   apply auto
  apply (metis (mono_tags, lifting) Diff_eq_empty_iff Diff_iff IntI Rep_minus Rep_minus_def chan_botsingle)
  by (smt Rep_minus_def Rep_minus_inject injI)
end

end