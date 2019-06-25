theory EinChannel

imports bundle.SB

begin
text \<open>You need to set THIS directory as Session-Directory. NOT the root-directory of the repository\<close>

lemma cempty_empty[simp]: "cEmpty = {}"
  by(auto simp add: cEmpty_def ctype_def)

text \<open>Macht nicht wirklich sinn, aber da wir nur den einen Channel haben...
  Normalerweise erstellt der Nutzer hier seine eigenen channels zuerst\<close>
instantiation channel::chan
begin
  definition Rep_channel::"channel \<Rightarrow> channel" where
  "Rep_channel = id"
  
  instance
    apply(intro_classes)
    by(auto simp add: Rep_channel_def)
end

lift_definition natSB::"nat stream \<rightarrow> channel\<^sup>\<Omega>" is
"(\<lambda> s. Abs_sb (\<lambda> _ . s))"
  apply(simp add: cfun_def)
  oops

end