(*  Title:        NewSpfStep
    Author:       Hendrik Kausch
    e-mail:       hendrik.kausch@rwth-aachen.de
*)

theory NewSpfStep
imports SPF
begin
default_sort type

typedef 'm sbElem = "{x :: (channel\<rightharpoonup>'m::message) . sbElemWell x}"
   by(simp add: sbElemWellEx)
  
definition sbHdElemWell::"'m::message SB \<Rightarrow> bool" where
"sbHdElemWell sb = (\<forall>c \<in> ubDom\<cdot>(sb). (sbHdElem\<cdot>sb)\<rightharpoonup> c \<noteq> \<bottom>)"  

lemma sbHdElemWell_inv_ex:"sbHdElemWell sb \<Longrightarrow> \<exists>x. convDiscrUp x = (sbHdElem\<cdot>sb)"
  using convdiscrup_inv_eq sbHdElemWell_def sbHdElem_dom by blast

lemma sbHdElemWell_invConvDiscrUp:"sbHdElemWell sb \<Longrightarrow> \<forall>c\<in>ubDom\<cdot>(sb).((inv convDiscrUp) (sbHdElem\<cdot>sb)) \<rightharpoonup> c = inv Discr (inv Iup ((sbHdElem\<cdot>sb) \<rightharpoonup> c))"
  by (simp add: convDiscrUp_inv_subst sbHdElemWell_def)
     
(* updis bijectiv *)
thm inv_def
(* Returns the SPF that switches depending on input.  (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) computes the SPF which has to be applied to the input sb*)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb)))"


lemma "cont (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb))))"
  oops

lemma "inj (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb))))"
  oops

end