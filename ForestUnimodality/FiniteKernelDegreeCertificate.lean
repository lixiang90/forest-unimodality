import ForestUnimodality.FiniteKernelDegreeInterval
import ForestUnimodality.FiniteKernelRationalCertificate

/-! A finite rational condition suffices for degree propagation. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate
open Finset FiniteKernelInterpolation

def RationalRow.degreeFloorQ {ι : Type*} (r : RationalRow ι) (N : ℕ) (a b : ℚ) : ℚ :=
  r.dM * (2 * (N : ℚ) + 1) - r.B - r.dδ / 4 -
    ∑ i ∈ r.terms, r.price i * b * (1 - r.retention i) * (1 - a + a * r.retention i) ^ N

theorem RationalRow.cast_degreeFloorQ {ι : Type*} (r : RationalRow ι)
    (N : ℕ) (a b : ℚ) :
    (r.degreeFloorQ N a b : ℝ) = r.toReal.degreeFloor N (a : ℝ) (b : ℝ) := by
  simp [RationalRow.degreeFloorQ, Row.degreeFloor, RationalRow.toReal, transform]

def RationalRow.degreePropagationCheck {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (N : ℕ) (a b : ℚ) : Bool :=
  decide (r.fixedIndices = ∅ ∧ 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ 0 ≤ r.dM ∧ 0 ≤ r.dδ ∧
    (∀ i ∈ r.terms, 0 ≤ r.price i ∧ 0 ≤ r.retention i ∧ r.retention i ≤ 1) ∧
    0 ≤ r.degreeFloorQ N a b)

theorem RationalRow.degreePropagationCheck_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (N : ℕ) (a b : ℚ)
    (hc : r.degreePropagationCheck N a b = true)
    (hbase : ∀ q ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ j : ℤ, 0 ≤ r.toReal.residual N j q) :
    ∀ n, N ≤ n → ∀ q ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ j : ℤ, 0 ≤ r.toReal.residual n j q := by
  have hh : r.fixedIndices = ∅ ∧ 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ 0 ≤ r.dM ∧ 0 ≤ r.dδ ∧
      (∀ i ∈ r.terms, 0 ≤ r.price i ∧ 0 ≤ r.retention i ∧ r.retention i ≤ 1) ∧
      0 ≤ r.degreeFloorQ N a b := of_decide_eq_true hc
  obtain ⟨hf, ha, _hab, hb, hM, hδ, hp, hfloor⟩ := hh
  have hfixed : ∀ j, r.toReal.fixedPrice j = 0 := by
    intro j
    simp [RationalRow.toReal, RationalRow.fixed, hf]
  apply r.toReal.residual_nonneg_from_interval_degree hfixed N
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  · change (0 : ℝ) ≤ (r.dM : ℝ)
    exact_mod_cast hM
  · change (0 : ℝ) ≤ (r.dδ : ℝ)
    exact_mod_cast hδ
  · intro i hi
    have h := hp i hi
    change (0 : ℝ) ≤ (r.price i : ℝ) ∧ 0 ≤ (r.retention i : ℝ) ∧ (r.retention i : ℝ) ≤ 1
    exact_mod_cast h
  · rw [← r.cast_degreeFloorQ]
    exact_mod_cast hfloor
  · exact hbase

#print axioms RationalRow.cast_degreeFloorQ
#print axioms RationalRow.degreePropagationCheck_sound
end ForestUnimodality.FiniteKernelRationalCertificate
