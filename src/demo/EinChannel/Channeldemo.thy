theory Channeldemo

imports inc.Channel

begin
text \<open>You need to set THIS directory as Session-Directory. NOT the root-directory of the repository\<close>

lemma cempty_empty[simp]: "cEmpty = {c3}"
  apply(simp add: cEmpty_def)
  by(insert ctype.elims,auto)

text \<open>Now we define and instantiate three different chan types, that will be used throughout 
      the demo\<close>

typedef emptychan="{c3}"
  by simp

instantiation emptychan::chan
begin
definition "Rep = Rep_emptychan"
instance
  apply(intro_classes)
  apply simp
  using Rep_emptychan_def type_definition.Rep_range type_definition_emptychan apply fastforce
  by (simp add: Rep_emptychan_def Rep_emptychan_inject inj_on_def)
end

lemma emptychan_range[simp]:"range(Rep::emptychan \<Rightarrow> channel) = {c3}"
  using Rep_emptychan_def type_definition.Rep_range type_definition_emptychan by fastforce

typedef inChan="{c1}"
  by simp

instantiation inChan::chan
begin
definition "Rep = Rep_inChan"
instance
  apply(intro_classes)
  apply simp
  using Rep_inChan Rep_inChan_def apply auto[1]
  by (simp add: Rep_inChan_def Rep_inChan_inject inj_on_def)
end

lemma inchan_range[simp]:"range(Rep::inChan \<Rightarrow> channel) = {c1}"
  using Rep_inChan_def type_definition.Rep_range type_definition_inChan by fastforce

typedef outChan="{c2}"
  by simp

instantiation outChan::chan
begin
definition "Rep = Rep_outChan"
instance
  apply(intro_classes)
  apply simp
  using Rep_outChan Rep_outChan_def apply auto[1]
  by (simp add: Rep_outChan_def Rep_outChan_inject inj_on_def)
end

lemma outchan_range[simp]:"range(Rep::outChan \<Rightarrow> channel) = {c2}"
  using Rep_outChan_def type_definition.Rep_range type_definition_outChan by fastforce





subsection \<open>Channel without \<open>typedef\<close>\<close>


datatype myChan = port_as | port_ar

instantiation myChan::chan
begin
fun Rep_myChan::"myChan \<Rightarrow> channel" where
"Rep_myChan port_as = c1" |
"Rep_myChan port_ar = c2"

instance
  apply(intro_classes, auto)
   apply (metis(full_types) Rep_myChan.elims channel.distinct(3) channel.distinct(5))
  apply(subst inj_def, auto)
  by (metis Rep_myChan.elims channel.distinct(1))
end


end