import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_6_3_1_checked :
    (Witness.rising).check 6 3 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_6_4_1_checked :
    (Witness.rising).check 6 4 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_6_4_2_checked :
    (Witness.rising).check 6 4 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_6_5_1_checked :
    (Witness.rising).check 6 5 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_6_5_2_checked :
    (Witness.rising).check 6 5 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_6 (a k : ℕ) (h : Domain 6 a k) :
    ∃ w : Witness, w.check 6 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 3 ≤ a := by omega
  have haHi : a ≤ 5 := by omega
  interval_cases a

  · have hkHi : k ≤ 1 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_6_3_1_checked⟩

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_6_4_1_checked⟩

    · exact ⟨Witness.rising, case_6_4_2_checked⟩

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_6_5_1_checked⟩

    · exact ⟨Witness.rising, case_6_5_2_checked⟩


#print axioms coverage_6
end ForestUnimodality.FiniteRows.FiniteData
