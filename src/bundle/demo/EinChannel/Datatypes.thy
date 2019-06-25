theory Datatypes

imports HOLCF

begin

default_sort type

datatype channel = TheOneChannel



section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
type_synonym M = nat



text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
definition ctype :: "channel \<Rightarrow> M set" where 
"ctype _ = UNIV"




end
