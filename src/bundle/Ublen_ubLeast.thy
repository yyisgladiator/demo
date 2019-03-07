theory Ublen_ubLeast 
  imports UBundle_Conc
begin

default_sort uscl_conc

lemma ubleast_ublen_eq0: 
  assumes "cs \<noteq> {}"
  shows "ubLen (ubLeast cs:: 'M\<^sup>\<Omega>) = 0"
proof -
  obtain a where a_def: "a \<in> cs"
    using assms(1) by auto
  then show "ubLen (ubLeast cs :: 'M\<^sup>\<Omega>) = 0"
    using assms(1) ubleast_len by auto
qed

end