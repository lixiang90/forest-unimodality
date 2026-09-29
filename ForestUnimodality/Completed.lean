import ForestUnimodality.IntermediateBridgeRemaining
import ForestUnimodality.IntermediateBridgeRequiredCatalog

namespace ForestUnimodality.Completed
universe u
open IntermediateBridgeCover IntermediateBridgeCoverData IntermediateBridgeAssembly
open IntermediateBridgeRemaining
set_option maxRecDepth 200000
set_option maxHeartbeats 0

private theorem proved_eq_catalog :
    provedRectangles = IntermediateBridgeRequiredCatalog.keys := by decide +kernel

private theorem cover59_mem :
    ∀ b ∈ cover59.bands, ∀ i ∈ b.cells, i ∈ provedRectangles := by
  rw [proved_eq_catalog]
  exact IntermediateBridgeRequiredCatalog.cover59_mem
private theorem cover80_mem :
    ∀ b ∈ cover80.bands, ∀ i ∈ b.cells, i ∈ provedRectangles := by
  rw [proved_eq_catalog]
  exact IntermediateBridgeRequiredCatalog.cover80_mem
private theorem cover99_mem :
    ∀ b ∈ cover99.bands, ∀ i ∈ b.cells, i ∈ provedRectangles := by
  rw [proved_eq_catalog]
  exact IntermediateBridgeRequiredCatalog.cover99_mem
private theorem cover130_mem :
    ∀ b ∈ cover130.bands, ∀ i ∈ b.cells, i ∈ provedRectangles := by
  rw [proved_eq_catalog]
  exact IntermediateBridgeRequiredCatalog.cover130_mem

private theorem required_mem_proved {i : CellKey} (hi : RequiredRectangle i) :
    i ∈ provedRectangles := by
  obtain ⟨b, hb, hi⟩ := hi
  rcases hb with h59 | h80 | h99 | h130
  · exact cover59_mem b h59 i hi
  · exact cover80_mem b h80 i hi
  · exact cover99_mem b h99 i hi
  · exact cover130_mem b h130 i hi

private theorem parents_mem : ∀ i : Fin 130, i ∈ provedParents := by decide +kernel

theorem rectangles_valid : RectanglesValid.{u} := by
  intro i hi
  exact proved_rectangles_valid i (required_mem_proved hi)

theorem parents_valid : ParentsValid.{u} := by
  intro i
  exact proved_parents_valid i (parents_mem i)

theorem countIndependent_unimodal_of_isAcyclic
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (hG : G.IsAcyclic) : WeaklyUnimodal (countIndependent G S) :=
  IntermediateBridgeAssembly.countIndependent_unimodal_of_domains
    parents_valid rectangles_valid G S hG

theorem completeTarget : CompleteTarget :=
  IntermediateBridgeAssembly.completeTarget_of_domains parents_valid rectangles_valid

#print axioms rectangles_valid
#print axioms parents_valid
#print axioms countIndependent_unimodal_of_isAcyclic
#print axioms completeTarget
end ForestUnimodality.Completed
