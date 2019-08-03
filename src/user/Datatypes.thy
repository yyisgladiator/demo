(*<*)
theory Datatypes

imports HOLCF

begin
(*>*)

default_sort %invisible type
text\<open>This section defines two datatypes that will be used for defining stream bundles,
stream processing functions and automatons \ref{sec:focus}.
The datatypes in this theory are only dummy types, that will be generated differently depending 
on the component. We need these dummy types to define the general framework.\<close>

section \<open>Channeldatatype\<close>
text \<open>The channel datatype is fixed before the proof begins. This datatype contains every channel, 
that is used. There is no way to "dynamically" add channels, except modifying this datatype.\<close>

datatype channel = DummyChannel nat

hide_const DummyChannel
text \<open>To ensure that the dummy channel type is never used for proving anything not holding 
over every channel type, the constructor is immediately hidden.\<close>

section \<open>Message Definition\<close>

text\<open>Analogous to the channel datatype, the message datatype contains all messages that a channel 
can transmit. Hence, every kind of message has to be described here.\<close>
datatype M = DummyMessage nat

hide_const DummyMessage
text \<open>To ensure that the dummy message type is never used for proving anything not holding for a 
different message type, the constructor is also immediately hidden.\<close>

instance M :: countable
  apply(intro_classes)
  by(countable_datatype)
text\<open>Since we want use the stream type \ref{sec:stream} for defining stream bundles, the message 
datatype has to be countable. In addition, a channel can be restricted to allow only a subset of 
messages on its stream. Therefore, each channel has a "type", a set of messages from datatype @{type M}.
These channel types are described by the ctype function. Only Messages included in the ctype are 
allowed to be transmitted on the respective channel.\<close>

definition ctype :: "channel \<Rightarrow> M set" where 
"ctype = (\<lambda>c. if c= undefined then {} else undefined)"

text\<open>Here we also use a dummy ctype definition. The only this that is assumed, is that there always
exists at least one channel, on which no channel can flow.\<close>

theorem ctypeempty_ex:"\<exists>c. ctype c = {}"
  by (simp add: ctype_def)

text\<open>Only with such an assumption we can always artificially define an "empty" stream bundle. The 
possibility to have an empty stream bundle is important for various reasons. Beside being able to 
define "sensors" and "sinks" as SPFs, also the general composition\ref{sec:focus} of components may 
result in components without in or output channels. Thus, we restrict the user to channel types, 
that contain a never transmitting channel.\<close>

hide_fact ctype_def
text\<open>At last we hide the ctype definition for other theories\<close>
(*<*)
end
(*>*)