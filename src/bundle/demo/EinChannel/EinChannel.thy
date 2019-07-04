theory EinChannel

imports bundle.SB

begin
text \<open>You need to set THIS directory as Session-Directory. NOT the root-directory of the repository\<close>

lemma cempty_empty[simp]: "cEmpty = {c3}"
  apply(auto simp add: cEmpty_def)
  sorry

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


text \<open>\<open>'a\<close> should be interpreted as a tuple. The goal of this local is to create a
  bijective mapping from \<open>'a\<close> to \<open>'cs\<close>.
  The user can freely choose \<open>'a\<close>, hence he will not use the datatype \<open>M\<close>. 
  for example \<open>'a = (nat \<times> bool)\<close> which maps to a bundle with one bool-channel and one nat-channel\<close>
locale sbeGen =
  fixes lConstructor::"'a::countable \<Rightarrow> 'cs::chan \<Rightarrow> M"
  assumes c_well: "\<And>a. sbElem_well (Some (lConstructor a))"
      and c_inj: "inj lConstructor" 
      and c_surj: "\<And>sbe. sbElem_well (Some sbe) \<Longrightarrow> sbe\<in>range lConstructor" (* Schöner? *)
begin

lemma empty_neq: "\<not>chIsEmpty TYPE ('cs)"
  using c_well sbtypeempty_notsbewell by blast

lift_definition setter::"'a \<Rightarrow> 'cs\<^sup>\<surd>" is "Some o lConstructor"
  using c_well by auto

definition getter::"'cs\<^sup>\<surd> \<Rightarrow> 'a" where
"getter  = (inv lConstructor) o the o Rep_sbElem"



lemma get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  by (simp add: setter.rep_eq c_inj)  

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  sorry

lemma set_bij: "bij setter"
  by (metis bijI inj_onI sbeGen.get_set sbeGen_axioms set_surj)

lemma get_inv_set: "getter = (inv setter)"
  by (metis get_set set_surj surj_imp_inv_eq)

lemma set_get[simp]: "setter (getter sbe) = sbe"
  apply(simp add: get_inv_set)
  by (meson bij_inv_eq_iff set_bij)


lemma "getter A = getter B \<Longrightarrow> A = B"
  by (metis set_get)


fixrec setterSB::"'a stream \<rightarrow> 'cs\<^sup>\<Omega>" where
"setterSB\<cdot>((up\<cdot>l)&&ls) = (setter (undiscr l)) \<bullet>\<^sup>\<surd> (setterSB\<cdot>ls)" 
(* Man kann auch einen getterSB definieren (mit fixrec, nachdem das klappt(über endliche bündel)).... 
    Sollte man auch, die frage ist nur wie weitflächig der einsetzbar ist. Er schneidet längere Elemente ab *)


(* TODO: lemma über setterSB und getterSB *)
end






locale sumChanSB = (* TODO: anpassen wie oben, z.B. reihenfolge argumente *)
  fixes lConstructor::"'cs::chan \<Rightarrow> 'a::pcpo \<Rightarrow> M stream"
  assumes c_type: "\<And>a c. sValues (lConstructor c a) \<subseteq> ctype (Rep c)"
    and c_inj: "\<And>c. inj (lConstructor c)"
begin

definition setter2::"'a \<rightarrow> ('cs::chan)\<^sup>\<Omega>" where
"setter2 = (\<Lambda> a . Abs_sb (\<lambda>c. lConstructor c a))"


definition getter::"'cs\<^sup>\<Omega> \<rightarrow> 'a" where
"getter= (\<Lambda> sbe. (inv (\<lambda> a c. lConstructor c a)) (((Rep_sb sbe))))"


end



section \<open>Beispiel\<close>

typedef mymy = "{c1, c2}"
  by blast

definition "mymyC1 = Abs_mymy c1"
definition "mymyC2 = Abs_mymy c2"

(* Fuck Yeah, pattern matching! *)
(* TODO: is it possible to put everything in a "bundle"? 
    eg. bundleName.c1 = mymyC1
        bundleName.setter = dudu.setter"
*)
free_constructors mymy for "mymyC1"  | "mymyC2"
   apply auto
  unfolding mymyC1_def mymyC2_def
  apply (metis Rep_mymy Rep_mymy_inverse empty_iff insert_iff)
  by (meson channel.distinct(1) insertI1 insertI2 type_definition.Abs_inject type_definition_mymy)

lemma mymy_rep_range [simp]:"range Rep_mymy = {c1, c2}"
  using type_definition.Rep_range type_definition_mymy by blast

instantiation mymy::chan
begin
definition "Rep = Rep_mymy" (* TODO: abbreviation oÄ, ich will nicht immer "Rep_mymy_def" anwenden *) 

instance
  apply(intro_classes)
  unfolding Rep_mymy_def apply simp
  by (meson Rep_mymy_inject injI)
end



lemma myc1_rep [simp]: "Rep (mymyC1) = c1"
  unfolding Rep_mymy_def mymyC1_def
  by (simp add: Abs_mymy_inverse)

lemma myc2_rep [simp]: "Rep (mymyC2) = c2"
  unfolding Rep_mymy_def mymyC2_def
  by (simp add: Abs_mymy_inverse)

(* :/ Schöner? *)
fun orderChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> mymy \<Rightarrow> 'a" where
"orderChan Cc1 Cc2 (port_c1, port_c2) mymyC1 = Cc1 port_c1" |
"orderChan Cc1 Cc2 (port_c1, port_c2) mymyC2 = Cc2 port_c2"

abbreviation "buildSBE \<equiv> orderChan \<N> \<B>" 

lemma build_ctype: "buildSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a; simp)

lemma build_inj: "inj buildSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject orderChan.simps)

lemma build_range: "range (\<lambda>a. buildSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma build_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildSBE"
proof -
  have "\<And>c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildSBE a c)"
    by (simp add: build_range)
  thus ?thesis oops (* TODO *)

interpretation dudu: sbeGen "buildSBE"
  apply(unfold_locales)
  sorry

term "dudu.setter"

term "curry dudu.setter"  (* If you prefer the "old way" *)

lemma "dudu.getter (dudu.setter (1,True)) = (1,True)"
  by simp





abbreviation "buildSB \<equiv> orderChan (Rep_cfun (smap \<N>)) (Rep_cfun (smap \<B>))" 

interpretation duda: sumChanSB "buildSB"
  sorry

term "duda.setter2"
term "duda.getter"





end