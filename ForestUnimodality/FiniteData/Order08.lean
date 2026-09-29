import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_8_4_1_checked :
    (Witness.rising).check 8 4 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_4_2_checked :
    (Witness.rising).check 8 4 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_5_1_checked :
    (Witness.rising).check 8 5 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_5_2_checked :
    (Witness.rising).check 8 5 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_6_1_checked :
    (Witness.rising).check 8 6 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_6_2_checked :
    (Witness.rising).check 8 6 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_8_6_3 : Certificate := {
  objectiveScale := 1
  eta := 1
  rows := #[]
  caps := #[0, 0, 1] }

theorem case_8_6_3_checked :
    (Witness.linear .positive case_8_6_3).check 8 6 3 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_7_1_checked :
    (Witness.rising).check 8 7 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_8_7_2_checked :
    (Witness.rising).check 8 7 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_8_7_3 : Certificate := {
  objectiveScale := 1
  eta := 1
  rows := #[]
  caps := #[0, 0] }

theorem case_8_7_3_checked :
    (Witness.linear .positive case_8_7_3).check 8 7 3 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_8_7_4 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0] }

theorem case_8_7_4_checked :
    (Witness.linear .negative case_8_7_4).check 8 7 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_8 (a k : ℕ) (h : Domain 8 a k) :
    ∃ w : Witness, w.check 8 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 4 ≤ a := by omega
  have haHi : a ≤ 7 := by omega
  interval_cases a

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_8_4_1_checked⟩

    · exact ⟨Witness.rising, case_8_4_2_checked⟩

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_8_5_1_checked⟩

    · exact ⟨Witness.rising, case_8_5_2_checked⟩

  · have hkHi : k ≤ 3 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_8_6_1_checked⟩

    · exact ⟨Witness.rising, case_8_6_2_checked⟩

    · exact ⟨Witness.linear .positive case_8_6_3, case_8_6_3_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_8_7_1_checked⟩

    · exact ⟨Witness.rising, case_8_7_2_checked⟩

    · exact ⟨Witness.linear .positive case_8_7_3, case_8_7_3_checked⟩

    · exact ⟨Witness.linear .negative case_8_7_4, case_8_7_4_checked⟩


#print axioms coverage_8
end ForestUnimodality.FiniteRows.FiniteData
