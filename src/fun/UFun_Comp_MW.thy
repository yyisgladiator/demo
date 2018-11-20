theory UFun_Comp_MW
  imports fun.UFun_Comp
begin


lemma assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "uf1 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf1) = ((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<bar> ufRan\<cdot>uf1"
  sorry

lemma assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "uf2 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf2) = ((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<bar> ufRan\<cdot>uf2"
  sorry


end