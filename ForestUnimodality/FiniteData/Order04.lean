import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_4_3_1_checked :
    (Witness.rising).check 4 3 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_4 (a k : ℕ) (h : Domain 4 a k) :
    ∃ w : Witness, w.check 4 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 2 ≤ a := by omega
  have haHi : a ≤ 3 := by omega
  interval_cases a

  · omega

  · have hkHi : k ≤ 1 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_4_3_1_checked⟩


#print axioms coverage_4
end ForestUnimodality.FiniteRows.FiniteData
