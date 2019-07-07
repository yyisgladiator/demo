theory Datatypes

imports HOLCF

begin

default_sort type

datatype channel = c1 | c2 | c3 | cin1 | cin2 | cout



section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
datatype M = \<N> nat | \<B> bool | eps

text \<open>* Introduce symbol @{text ~} for empty time-slots called eps. \<close>
syntax "@eps" :: M ("~")
translations "~" == "CONST eps"

instance M::countable
  apply(countable_datatype)
  done

text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
fun ctype :: "channel \<Rightarrow> M set" where 
"ctype c1 = range \<N>" |
"ctype c2 = range \<B>" |
"ctype c3 = {}" |
"ctype _ = range \<B>"



end
