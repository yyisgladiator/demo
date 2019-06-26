theory Datatypes

imports HOLCF

begin

default_sort type

datatype channel = c1 | c2 | c3



section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
type_synonym M = nat



text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
fun ctype :: "channel \<Rightarrow> M set" where 
"ctype c3 = {}" |
"ctype _ = UNIV"



end
