theory contVScomputable
  
imports HOLCF
    
begin
  
  (* Some new Datatypes and instanciations *)
  
datatype "DNum" = Eins | Zwei | Drei
  
instantiation DNum :: po
begin
  definition below_DNum_def: "b1 \<sqsubseteq> b2 \<equiv> ((b1::DNum)=b2) \<or> b1 = Eins \<or>(b1=Zwei \<and>b2=Drei)"
  instance
    apply intro_classes
      apply(auto simp add: below_DNum_def)
      done
end
  
instantiation DNum:: chfin
begin
  instance
    apply intro_classes
    by (smt DNum.distinct(4) below_DNum_def max_in_chainI po_class.chain_mono) 
end

instantiation nat :: discrete_cpo
begin
definition below_nat_def: "n1\<sqsubseteq>n2 \<equiv> (n1::nat)=n2"
instance
  apply intro_classes
  by(simp add: below_nat_def)
end
  
instantiation bool :: discrete_cpo
begin
definition below_bool_def: "n1\<sqsubseteq>n2 \<equiv> (n1::bool)=n2"
instance
  apply intro_classes
  by(simp add: below_bool_def)
end

setup_lifting type_definition_cfun
  
  



  
(**************************)  
  (* Main Part *)
(**************************)  

  
  (**** 1 ****)  
(* a computable and continuous function *)
lift_definition makeDrei:: "DNum \<rightarrow> DNum" is "\<lambda> n. Drei"
  by(simp add: cfun_def)


    


  (**** 2 ****)    
(* A computable but not monotonic function *)    
fun notMonofun:: "DNum \<Rightarrow> DNum" where
"notMonofun Eins = Zwei" |
"notMonofun Zwei = Eins" |
"notMonofun Drei = Drei"

lemma notmonofun_mono: "\<not>monofun notMonofun"
apply(simp add: monofun_def)
by (metis DNum.distinct(1) DNum.distinct(4) below_DNum_def notMonofun.simps(1) notMonofun.simps(2))

lemma "\<not>cont notMonofun"
  using cont2mono notmonofun_mono by blast 
    
(* Just a demonstration that the function is computable *)    
value "notMonofun Eins"
value "notMonofun Zwei"
value "notMonofun Drei"
  
  
 

  
  (**** 3 ****)
(* A continuous but not computable function: *)
  
(* This lemma states that EVERY function from nat\<Rightarrow>bool is continuous *)
(* The halting-problem can be described as function from nat\<Rightarrow>bool ....  hence it must be cont *)  
lemma fixes f:: "nat \<Rightarrow> bool"
  shows "cont f"
  by simp  

  
   
    
    
  (**** 4 ****)    
(* A not computable and not cont function *) 

fun neither:: "(DNum \<times> nat) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> DNum" where
"neither (Eins,n) f = Zwei" |
"neither (Zwei,n) f = Eins" |
"neither (Drei,n) f = (if(f n) then Eins else Drei)"

lemma "\<not>monofun neither"
apply(simp add: monofun_def)
  by (metis DNum.distinct(1) DNum.distinct(4) below_DNum_def fun_belowD neither.simps(1) neither.simps(2))  

  (* for all f the function is not monotonic *)    
lemma "\<not>monofun (\<lambda>p. neither p f)"
apply(simp add: monofun_def)
  by (metis DNum.distinct(1) DNum.distinct(4) below_DNum_def neither.simps(1) neither.simps(2))  


(* The function is not always computable, because sometimes the input f might me a non-computable function (lets call it nonComp). 
  Then the "neither (Drei, n) nonComp" is not computable. *)
  
end