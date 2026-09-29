import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_7_4_1_checked :
    (Witness.rising).check 7 4 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_7_4_2_checked :
    (Witness.rising).check 7 4 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_7_5_1_checked :
    (Witness.rising).check 7 5 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_7_5_2_checked :
    (Witness.rising).check 7 5 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_7_6_1_checked :
    (Witness.rising).check 7 6 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_7_6_2_checked :
    (Witness.rising).check 7 6 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_7_6_3 : Certificate := {
  objectiveScale := 1
  eta := 1
  rows := #[]
  caps := #[0, 0] }

theorem case_7_6_3_checked :
    (Witness.linear .positive case_7_6_3).check 7 6 3 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_7 (a k : ℕ) (h : Domain 7 a k) :
    ∃ w : Witness, w.check 7 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 4 ≤ a := by omega
  have haHi : a ≤ 6 := by omega
  interval_cases a

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_7_4_1_checked⟩

    · exact ⟨Witness.rising, case_7_4_2_checked⟩

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_7_5_1_checked⟩

    · exact ⟨Witness.rising, case_7_5_2_checked⟩

  · have hkHi : k ≤ 3 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_7_6_1_checked⟩

    · exact ⟨Witness.rising, case_7_6_2_checked⟩

    · exact ⟨Witness.linear .positive case_7_6_3, case_7_6_3_checked⟩


#print axioms coverage_7
end ForestUnimodality.FiniteRows.FiniteData
