theory EinChannel

imports bundle.SB

begin
text \<open>You need to set THIS directory as Session-Directory. NOT the root-directory of the repository\<close>

lemma cempty_empty[simp]: "cEmpty = {c3}"
  apply(auto simp add: cEmpty_def)
  using ctype.elims by force

typedef singleChan = "{c1}"
  by blast

lemma [simp]: "range Rep_singleChan = {c1}"
  using type_definition.Rep_range type_definition_singleChan by blast

lemma "Abs_singleChan c1 = undefined"
  oops
text \<open>Macht nicht wirklich sinn, aber da wir nur den einen Channel haben...
  Normalerweise erstellt der Nutzer hier seine eigenen channels zuerst\<close>
instantiation singleChan::chan
begin
definition "Rep = Rep_singleChan"
  
  instance
    apply(intro_classes)
     apply(auto simp add: Rep_singleChan_def)
    by (meson Rep_singleChan_inject injI)

end


section\<open>Datatype Konstruktor\<close>

(* FYI: the old approach from v2 to create the datatype is not really reusable, 
  because: 
      lift_definition elem_raw_i :: "int \<Rightarrow> ndaExampleMessage sbElem" is
  Thats an old "single-channel" setter...
  One has to replace the "ndaExampleMessage" with a "chan"... but which?
  There can only be ONE channel in the replacement! ! !
  But what if the channel-datatype of the component has 2 or more channels?
*)

text \<open>Motivation: I HATE freemarker and other templates. 
  And the workflow sucks. The generator people have no idea about isabelle, 
  feature-request take FOREVER and then it might not work in every case\<close>

text\<open>Goal: Move the heavy-stuff from the Generator to Isabelle.
  Pretty much every proof should be done in Isabelle, the generator
  can still create datatypes, functions and so on\<close>

text\<open>Implementation: Is using Locales... \<close>


default_sort type

text \<open>Getter/Setter for a SINGLE Channel! There is exactly one channel in 'cs 
  'a is the user-defined datatype, in case the "M"-datatype is a combination of multiple
  messages\<close>

locale singleChannel =
  fixes lChannel::"'cs::chan" and lConstructor::"'a \<Rightarrow> M"
  assumes Rep: "\<And>a. lConstructor a \<in> ctype (Rep lChannel)"
    and c_inj: "inj lConstructor"
    and the_only: "\<And>c. c=lChannel" (* Only ONE SINGLE channel *)
begin
lift_definition setter::"'a \<Rightarrow> 'cs\<^sup>\<surd>" is
"\<lambda>a. Some (\<lambda>c. lConstructor a)"
  sorry

definition getter::"'cs\<^sup>\<surd> \<Rightarrow> 'a" where
"getter sbe = (inv lConstructor) ((the (Rep_sbElem sbe)) lChannel)"

lemma get_set[simp]: "getter (setter a) = a"
  by (simp add: c_inj getter_def setter.rep_eq)

end


text \<open>Ein Beispiel:
  Aktuell ist "M=nat", die Nachrichten müssten nicht konvertiert werden. daher "id" \<close>
interpretation dada:"singleChannel" "Abs_singleChan c1" id
  apply(unfold_locales)
  apply auto
  apply (simp add: Abs_singleChan_inverse Rep_singleChan_def)
  using Abs_singleChan_cases by auto

lemma "dada.getter (dada.setter 2) = 2"
  by(simp only: dada.get_set)


text \<open>Now comes the tricky part... I am VERY open to better ideas\<close>

text\<open>How do we go from a single-channel version to multiple channels?
  Answer: stepwise. For every step add a new "singleChannel"\<close>
locale multiChannel =
  fixes ls::"'cs::chan" and c::"'a::countable \<Rightarrow> M"
    and setter2::"'other::countable \<Rightarrow> ('cs2::chan)\<^sup>\<surd>"
    and getter2::"'cs2\<^sup>\<surd> \<Rightarrow> 'other"  (* There have to be MANY assumptions over these functions *)
  assumes Rep: "singleChannel ls c"
  assumes "\<And>x. getter2 (setter2 x) = x"
begin
definition combinedSetter::"('a\<times>'other) \<Rightarrow> ('cs \<union> 'cs2)\<^sup>\<surd>" where
"combinedSetter = undefined"

definition combinedGetter::" ('cs \<union> 'cs2)\<^sup>\<surd> \<Rightarrow> ('a\<times>'other)" where
"combinedGetter = undefined"

lemma combinedID[simp]: "combinedGetter (combinedSetter cs) = cs"
  sorry
end








typedef secondChan = "{c2}"
  by blast

lemma [simp]: "range Rep_secondChan = {c2}"
  using type_definition.Rep_range type_definition_secondChan by blast

instantiation secondChan::chan
begin
definition "Rep = Rep_secondChan"
  
  instance
    apply(intro_classes)
     apply(auto simp add: Rep_secondChan_def)
    by (meson Rep_secondChan_inject injI)

end

interpretation dudu: multiChannel "Abs_secondChan c2" id dada.setter dada.getter
  apply(unfold_locales, auto)
  apply (simp add: Abs_secondChan_inverse Rep_secondChan_def)
  using Abs_secondChan_cases by auto


lemma "dudu.combinedSetter (1,2) \<noteq> dudu.combinedSetter (2,2)"
  by (metis Suc_1 dudu.combinedID n_not_Suc_n old.prod.inject)


end