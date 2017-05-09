session "StreamsSorry" (sorry) = "HOLCF" +
  options [quick_and_dirty = true]
  theories
    Streams

session "CompositionSorry" (sorry) = "StreamsSorry" + 
  options [quick_and_dirty = true]
  theories
    SPF_Composition_JB   
    


session "Streams" (verified) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    Streams

session "Composition" (verified) = "Streams" + 
  options [quick_and_dirty = false]
  theories
    SPF_Composition_JB
	