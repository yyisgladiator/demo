section {* Tutorial for Fixrec-Proofs *} 

  
  (* The name "Fixrec.thy" seems to be reserved or something... *)
theory FixrecTut

(* Official tutorial: https://isabelle.in.tum.de/library/HOL/HOLCF-Tutorial/document.pdf  
  and look at the second import! *)
imports "../TStream" "~~/src/HOL/HOLCF/Tutorial/Fixrec_ex"
begin

  (* Allways nice to know what the default_sort is *)
default_sort countable

  
subsection {* Streams / lNat*}
  
fixrec sSuc :: "nat stream \<rightarrow> nat stream" where
"sSuc\<cdot>\<bottom>=\<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> sSuc\<cdot>(x&&xs) = (upApply Suc\<cdot>x)&&(sSuc\<cdot>xs)"


  (* missing cases are implicitly created *)
fixrec myTake :: "lnat \<rightarrow> 'a stream \<rightarrow> 'a stream" where
"x\<noteq>\<bottom> \<Longrightarrow> myTake\<cdot>(lnsuc\<cdot>ln)\<cdot>(x&&xs) = x && myTake\<cdot>ln\<cdot>xs"

lemma "myTake\<cdot>\<bottom>\<cdot>xs = \<bottom>"
by(fixrec_simp)
  
lemma "myTake\<cdot>ln\<cdot>\<bottom> = \<bottom>"
  apply(fixrec_simp)
  oops
    
lemma "myTake\<cdot>ln\<cdot>\<bottom> = \<bottom>"
  apply(fixrec_simp)
  apply(cases ln)
  by auto

  
(* It is recommended to explicitly add all cases... *)
fixrec myTake2 :: "lnat \<rightarrow> 'a stream \<rightarrow> 'a stream" where
"myTake2\<cdot>\<bottom>\<cdot>xs = \<bottom>" |  
"myTake2\<cdot>ln\<cdot>\<bottom> = \<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> myTake2\<cdot>(lnsuc\<cdot>ln)\<cdot>(x&&xs) = x && myTake\<cdot>ln\<cdot>xs"  
  (* x\<noteq>\<bottom> is required! Otherwise (x&&xs) could be bot *)
  
lemma "myTake2\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  and "myTake2\<cdot>ln\<cdot>\<bottom> = \<bottom>"
  by(fixrec_simp)+
    
    
(* all cases must be mutually exclusive! *)
fixrec fix1 :: "lnat \<rightarrow>  'a stream" where
"fix1\<cdot>(lnsuc\<cdot>ln) = \<bottom>" |
"fix1\<cdot>ln = \<bottom>"  
  
end  