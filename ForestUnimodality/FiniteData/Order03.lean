import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem coverage_3 (a k : ℕ) (h : Domain 3 a k) :
    ∃ w : Witness, w.check 3 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 2 ≤ a := by omega
  have haHi : a ≤ 2 := by omega
  interval_cases a

  · omega


#print axioms coverage_3
end ForestUnimodality.FiniteRows.FiniteData
