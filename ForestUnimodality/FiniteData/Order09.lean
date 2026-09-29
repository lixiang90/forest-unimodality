import ForestUnimodality.FiniteWitness
import Mathlib.Tactic.IntervalCases

/-! Generated candidate witnesses. Each sign is rechecked by the Lean kernel.
The coverage theorem quantifies over Domain, independently of this record list.
Source and integer-witness hashes are recorded in research/finite-integer-witnesses/manifest.json.
-/
namespace ForestUnimodality.FiniteRows.FiniteData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_9_5_1_checked :
    (Witness.rising).check 9 5 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_5_2_checked :
    (Witness.rising).check 9 5 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_6_1_checked :
    (Witness.rising).check 9 6 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_6_2_checked :
    (Witness.rising).check 9 6 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_6_3_checked :
    (Witness.rising).check 9 6 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_7_1_checked :
    (Witness.rising).check 9 7 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_7_2_checked :
    (Witness.rising).check 9 7 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_7_3_checked :
    (Witness.rising).check 9 7 3 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_9_7_4 : Certificate := {
  objectiveScale := 1
  eta := 0
  rows := #[]
  caps := #[0, 0, 0] }

theorem case_9_7_4_checked :
    (Witness.linear .negative case_9_7_4).check 9 7 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_8_1_checked :
    (Witness.rising).check 9 8 1 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

theorem case_9_8_2_checked :
    (Witness.rising).check 9 8 2 = true := by
  simp only [Witness.check, matchingUpperCount, shiftedChoose, Nat.choose_eq_fast_choose]
  decide +kernel

def case_9_8_3 : Certificate := {
  objectiveScale := 1
  eta := 1
  rows := #[]
  caps := #[0, 0] }

theorem case_9_8_3_checked :
    (Witness.linear .positive case_9_8_3).check 9 8 3 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

def case_9_8_4 : Certificate := {
  objectiveScale := 1
  eta := 2
  rows := #[]
  caps := #[0, 0] }

theorem case_9_8_4_checked :
    (Witness.linear .positive case_9_8_4).check 9 8 4 = true := by
  simp only [Witness.check, Certificate.check, Certificate.Accepts, Certificate.residual,
    Certificate.bound, Certificate.cap, targetCoeff, targetConstant, coeff, rhs,
    meanBase, meanBeta, edgeGap, differenceCoeff, shiftedChoose,
    Nat.choose_eq_fast_choose]
  decide +kernel

theorem coverage_9 (a k : ℕ) (h : Domain 9 a k) :
    ∃ w : Witness, w.check 9 a k = true := by
  obtain ⟨hnlo, hnhi, halo, hahi, hklo, hkhi⟩ := h
  have haLo : 5 ≤ a := by omega
  have haHi : a ≤ 8 := by omega
  interval_cases a

  · have hkHi : k ≤ 2 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_9_5_1_checked⟩

    · exact ⟨Witness.rising, case_9_5_2_checked⟩

  · have hkHi : k ≤ 3 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_9_6_1_checked⟩

    · exact ⟨Witness.rising, case_9_6_2_checked⟩

    · exact ⟨Witness.rising, case_9_6_3_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_9_7_1_checked⟩

    · exact ⟨Witness.rising, case_9_7_2_checked⟩

    · exact ⟨Witness.rising, case_9_7_3_checked⟩

    · exact ⟨Witness.linear .negative case_9_7_4, case_9_7_4_checked⟩

  · have hkHi : k ≤ 4 := by omega
    interval_cases k

    · exact ⟨Witness.rising, case_9_8_1_checked⟩

    · exact ⟨Witness.rising, case_9_8_2_checked⟩

    · exact ⟨Witness.linear .positive case_9_8_3, case_9_8_3_checked⟩

    · exact ⟨Witness.linear .positive case_9_8_4, case_9_8_4_checked⟩


#print axioms coverage_9
end ForestUnimodality.FiniteRows.FiniteData
