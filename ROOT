session "inc" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    "inc/Channel"
    "inc/LNat"
    "inc/SetPcpo"
    "inc/SetRev"
    "inc/Prelude"
    "inc/OptionCpo"
    "inc/UnivClasses"
    "inc/CPOFix"


session "stream" (mustWork) = "inc" +
  options [quick_and_dirty = true]
  theories
    "stream/Streams"
    "stream/tsynStream"

session "bundle" (mustWork) = "stream" + 
  options [quick_and_dirty = true]
  theories
    "bundle/SB"
    "bundle/UBundle_Induction"
    "bundle/tsynBundle"

session "fun" (mustWork) = "bundle" + 
  options [quick_and_dirty = true]
  theories
    "fun/SPF"

session "spec" (mustWork) = "fun" + 
  options [quick_and_dirty = true]
  theories
    "spec/SPS"

session "automat" (mustWork) = "spec" + 
  theories
    "automat/SpfStep"
    "automat/dAutomaton"
    "automat/SpsStep"
    "automat/ndAutomaton"

