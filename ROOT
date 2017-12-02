session "Streams" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    Streams

session "SB" (mustWork) = "Streams" +
  options [quick_and_dirty = true]
  theories
    SB

session "SPF" (mustWork) = "SB" +
  options [quick_and_dirty = true]
  theories
    SB

session "Automat" (mustWork) = "SPF" +
  options [quick_and_dirty = true]
  theories
    Automaton
