section {* Tutorial for ISAR-Proofs *} 

theory ISAR
imports "../Streams"
begin

  (* Allways nice to know what the default_sort is *)
default_sort countable

  
subsection {* General Structure *}

lemma 
  fixes ln::lnat  (* nur zur demo, das braucht man normalerweise nicht *)
  assumes "ln < \<infinity>" and n_bot: "\<bottom> < ln"
  shows "P ln"
proof - (* "-" == empty rule... more later *)
  have "easyFormular" sorry
  from this have name: "complexFormular" sorry  (* "from this have" == "hence" *)
  hence "evenMoreComplex" sorry
  show ?thesis using name sorry  (* ?thesis is auto generated, we can also write "P ln" *)
      (* "from this show" == thus *)
qed
  
  
  
  
  
  (* copied from Streams.thy *)
lemma  assumes "\<forall>i. stake (i*y)\<cdot>xs = stake (i*y)\<cdot>ys" and "y\<noteq>0"
  shows "\<forall>i. stake i\<cdot>xs = stake i\<cdot>ys"
proof 
  fix i
  obtain k where "\<exists>l. k = y*l" and "k\<ge>i" by (metis One_nat_def Suc_le_eq assms(2) gr0I mult.commute mult_le_mono2 nat_mult_1_right)
  thus "stake i\<cdot>xs = stake i\<cdot>ys" by (metis assms(1) min_def mult.commute stream.take_take) 
qed

  (* (tiny bit) better variant *)
  (* use \<And> instead of \<forall> *)
  thm contI2
lemma assumes "\<And>i. stake (i*y)\<cdot>xs = stake (i*y)\<cdot>ys" and "y\<noteq>0"
  shows "stake i\<cdot>xs = stake i\<cdot>ys"
proof -
  obtain k where k_def1: "\<exists>l. k = y*l" and k_def2:"k\<ge>i" by (metis One_nat_def Suc_le_eq assms(2) gr0I mult.commute mult_le_mono2 nat_mult_1_right)
  thus "stake i\<cdot>xs = stake i\<cdot>ys" by (metis assms(1) min_def mult.commute stream.take_take) 
qed  
  
  (* "obtain" kann für existenz beweise verwendet werden *)
lemma assumes "\<exists>x::lnat. P x"
  shows "stuff"
proof -
  obtain z where z_def: "P z" using assms by auto
  hence "P (lnsuc\<cdot>z)" sorry
  oops
    
  
  
    
subsection {* Rules *}

lemma 
  fixes ln::lnat
  shows "P ln"
proof (cases "ln=\<infinity>")
  case True
  then show ?thesis sorry
next
  case False
  have "ln<\<infinity>" using False inf_less_eq leI by blast
  obtain n where n_def: "ln = Fin n"
    using \<open>ln < \<infinity>\<close> lnat_well_h2 by blast 
  then show ?thesis sorry
qed

lemma 
  fixes s::"'a stream"
  shows "P s"
proof (induction s)
  case adm
  then show ?case sorry
next
  case bottom
  then show ?case sorry
next
  (* case (lscons u s)
    then show ?case sorry *)
  
  (* alternativ (etwas hässlicher: )*)
  fix u:: "'a discr u"  
  fix s:: "'a stream"
  assume "u\<noteq>\<bottom>" and "P s"
  show "P (u&&s)" sorry
qed    
  

  
  
subsection \<open>Pattern Matching \<close>
lemma "monofun (\<lambda>s1. slookahd\<cdot>s1\<cdot>(\<lambda> a. slookahd\<cdot>s2\<cdot>(\<lambda> b. \<up>(a,b) \<bullet> (h\<cdot>(srt\<cdot>s1)\<cdot>(srt\<cdot>s2)))))" (is "monofun ?F")
proof (rule monofunI)
  fix x::"'a stream"
  fix y::"'a stream"

  assume "x\<sqsubseteq>y"
  thus "?F x \<sqsubseteq> ?F y" sorry
qed      
  
end  