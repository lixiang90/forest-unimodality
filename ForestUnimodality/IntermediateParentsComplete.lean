import ForestUnimodality.IntermediateBridgeRemaining

/-! Discharge every parent-domain premise after all 130 domain proofs are present.
The full forest theorem still requires the remaining finite rectangles. -/
namespace ForestUnimodality.IntermediateParentsComplete
universe u
open IntermediateBridgeCover IntermediateBridgeAssembly IntermediateBridgeRemaining
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem all_parents_mem : ∀ i : Fin 130, i ∈ provedParents := by
  decide +kernel

theorem parents_valid : ParentsValid.{u} := by
  intro i
  exact proved_parents_valid i (all_parents_mem i)

theorem remaining_parents : RemainingParents.{u} := by
  intro i hi
  exact False.elim (hi (all_parents_mem i))

theorem completeTarget_of_remaining_rectangles (hr : RemainingRectangles.{0}) :
    CompleteTarget :=
  completeTarget_of_remaining remaining_parents hr

#print axioms all_parents_mem
#print axioms parents_valid
#print axioms remaining_parents
#print axioms completeTarget_of_remaining_rectangles
end ForestUnimodality.IntermediateParentsComplete
