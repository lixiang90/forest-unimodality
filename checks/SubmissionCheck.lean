import ForestUnimodality.Completed

-- Check that the actual theorem inhabits the original all-forest target.
example : ForestUnimodality.CompleteTarget :=
  ForestUnimodality.Completed.completeTarget

#print axioms ForestUnimodality.Completed.rectangles_valid
#print axioms ForestUnimodality.Completed.parents_valid
#print axioms ForestUnimodality.Completed.countIndependent_unimodal_of_isAcyclic
#print axioms ForestUnimodality.Completed.completeTarget
