(*<*)(*:maxLineLen=78:*)
theory Datatypes

imports inc.Prelude

begin
(*>*)
(*Todo include cref package and change ref to cref*)
default_sort %invisible type
text\<open>This section mainly introduces two datatypes that will be used for 
defining stream bundles, stream processing functions and automatons 
\ref{sec:focus}. The datatypes in this theory are only dummy types, that will 
be generated differently depending on the component. We need these dummy types 
to define the general framework.\<close>

section \<open>Channel Datatype \label{sec:chadata}\<close>
text \<open>The channel datatype is fixed before the proof begins. This datatype 
contains every channel, that is used. There is no way to "dynamically" add 
channels, except modifying this datatype.\<close>

datatype channel = DummyChannel nat
hide_const DummyChannel

text \<open>To ensure that the dummy channel type is never used for proving anything
not holding over every channel type, the constructor is immediately hidden.\<close>

section \<open>Pure Message Datatype \label{sec:pmsgdata}\<close>


text\<open>Analogous to the channel datatype, the pure message datatype contains the
messages that a channel can transmit. Hence, every kind of message has to be 
described here.\<close>
datatype M_pure = DummyMessage nat
hide_const DummyMessage

text \<open>To ensure that the dummy message type is never used for proving anything 
not holding for a different message type, the constructor is also immediately 
hidden.\<close>

instance M_pure :: countable
  apply(intro_classes)
  by(countable_datatype)
text\<open>Since we want use the stream type for defining stream bundles, the
message datatype has to be countable. In addition, each channel can be 
restricted to allow only a subset of messages from @{type M_pure} on its 
stream. Therefore, each channel can be mapped to a set of messages from 
datatype @{type M_pure}.Such a mapping is described by the cMsg function. Only
messages included in the cMsg are allowed to be transmitted on the respective
channel.\<close>

definition cMsg :: "channel \<Rightarrow> M_pure set" where
"cMsg c \<equiv> if c= undefined then {} else undefined"
text\<open>Here we almost use an undefined cMsg mapping. We only assume, is that 
there always exists at least one channel, on which no message can flow.\<close>

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  by (simp add: cMsg_def)

text\<open>Only with such an assumption we can always artificially define an "empty"
stream bundle. The possibility to have an empty stream bundle is important for
various reasons. Beside being able to define "sensors" and "sinks" as SPFs,
also the general composition of components may result in components without in
or output channels. Thus, we restrict the user to channel types, that contain 
a never transmitting channel.\<close>

text \<open>Since one can use different time models for components, we also have to 
use the correct time model for our streams. Therefore, we define a function 
that maps a channel to its time model. The @{type timeType} is defined as:

@{datatype timeType}\<close>

definition cTime :: "channel \<Rightarrow> timeType" where
"cTime = undefined"

hide_fact %invisible cMsg_def
hide_fact %invisible cTime_def

(*<*)
end
(*>*)
