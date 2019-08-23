(*<*)(*:maxLineLen=68:*)
theory Datatypes

imports inc.Prelude

begin

default_sort type
(*>*)

text\<open>The Composition operator is one of the most prominent and 
useful tools this framework provides. For its evaluation we 
introduce the Flasher casestudy. The Flasher is a component in the 
lightcontrol system\ref{fig:lcontr} that was verified in 
\cite{che19}. The flasher is a feedback component to realize the 
flashing light. If its output is \<open>True\<close>, the light will be turned 
on, if it is \<open>False\<close>, it will be turned off. The light can only be 
turned on by the flasher, if it did not turn it on in the prvious
step. This produces the flashing light.\<close>

text\<open>Abbildung lightcontrol \label{fig:lcintr}\<close>

text\<open>This flasher component consists  of a \<open>Not\<close> and a \<open>And\<close> 
subcomponent, where \<open>And\<close> and \<open>Not\<close> are serially composed and the 
\<open>Not\<close> also provides feedback to the \<open>And\<close>. The flasher uses both
components and connects their channels. The Montiarc models of these
components are in figure\ref{fig:montiflash}\<close>

text\<open>Abbildung montiarc and not flasher\label{fig:montiflash}\<close>

text\<open>The following section shows and explains the generated
Isabelle code and the finial evaluation of a flasher invariant for
its desired behaviour of blinking. Since the generated code for the
\<open>And\<close> and \<open>Not\<close> component is very similar, only the more complex
\<open>And\<close> components code is explained in detail.\<close>

subsection\<open>Channel and Message Datatypes\<close>

text\<open>The Channels and Messages types described in the Montiarc model
are translated to datatypes in Isabelle. \<close>

text\<open>The three channels are called \<open>cin\<close> \<open>cintern\<close> and \<open>cout\<close>.\<close>

datatype channel = cin | cintern | cout | cempty

text\<open>Furthermore, the channel \<open>cempty\<close> is added to the datatype,
because there must always be a channel on which nothing can be 
transmitted\ref{sec:data}.\<close>


text\<open>The pure messages of the Flasher are boolean messages. Hence, 
the generated message datatypes constructor is a injective mapping 
from booleans to our messages.\<close>
datatype M_pure = \<B> bool

text\<open>If there is more than one message type allowed on the channels
the @{type M_pure} is extended by another constructor and type. For 
booleans and natural numbers it would be \<open>M_pure = \<B> bool | \<N> nat\<close>.
This type is then instantiated as countable, necessary to 
instantiate type \<open>M\<close>\ref{sub:gmt} as countable in the core theory 
files.\<close>

instance M_pure::countable
  apply(countable_datatype)
  done

lemma inj_B[simp]:"inj \<B>"
  by (simp add: inj_def)

lemma inj_Bopt[simp]:"inj (map_option \<B>)"
  by (simp add: option.inj_map)

text\<open>The allowed pure messages on used channel are then defined as
all boolean messages. The @{const cempty} channel cannot transmit 
any messages.\<close>

fun cMsg :: "channel \<Rightarrow> M_pure set" where
"cMsg cin     = range \<B>" |
"cMsg cintern = range \<B>" |
"cMsg cout    = range \<B>" |
"cMsg cempty  = {}"

text\<open>The timing properties of each channel are defined as time 
synchronous with @{const TTsyn}. It would also be possible to define
different timing properties to each channel. The unused empty 
channel always has a undefined time type, because it is in our 
interpretation not a channel at all.\<close>
fun cTime :: "channel \<Rightarrow> timeType" where
"cTime cin = TTsyn" |
"cTime cintern = TTsyn" |
"cTime cout = TTsyn" |
"cTime _ = undefined"

text\<open>As always, a theorem that confirms the existence of an empty 
channel has to be provided for the framework theories.\<close>
theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  using cMsg.simps by blast
(*<*)
end
(*>*)