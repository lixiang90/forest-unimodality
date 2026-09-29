import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_5_3_1_checked :
    (Witness.rising).check 5 3 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_5_4_1_checked :
    (Witness.rising).check 5 4 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_5_4_2_checked :
    (Witness.rising).check 5 4 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_5 (a k : ℕ) (h : Domain 5 a k) :
    ∃ w : Witness, w.check 5 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 3 ≤ a := by omega
  have haHi : a ≤ 4 := by omega
  interval_cases a

  · have hkHi : k ≤ 1 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_5_3_1_checked⟩

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_5_4_1_checked⟩

    · exact ⟨Witness.rising, case_5_4_2_checked⟩


#print axioms coverage_5
end ForestUnimodality.FiniteRows.FiniteData
