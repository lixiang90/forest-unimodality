import ForestUnimodality.KernelBudget
import ForestUnimodality.GraphBounds
import ForestUnimodality.PathLowerBound

/-! Exact cancellation of conditional binomial noise in the stage-59
fixed-shift charge. Integer shifts are kept signed throughout. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem hardCoreLayerWeight_cancel_noise (G : SimpleGraph V) (S I : Finset V)
    {z : ℝ} (hz : 0 < z) (y m : ℕ) :
    hardCoreLayerWeight G S I z y m * (1 - z / (1 + z)) ^ m =
      (layerCount G I (S \ I) y m : ℝ) * z ^ y / partitionFunction G S z := by
  have hz1 : 1 + z ≠ 0 := ne_of_gt (by linarith)
  have hZ : partitionFunction G S z ≠ 0 := ne_of_gt (partitionFunction_pos G S hz.le)
  have he : 1 - z / (1 + z) = (1 + z)⁻¹ := by field_simp; ring
  rw [he, inv_pow]
  unfold hardCoreLayerWeight
  field_simp

theorem hardCoreFixedShiftMass_eq_count (G : SimpleGraph V) (S I : Finset V)
    {z : ℝ} (hz : 0 < z) (k y : ℕ) :
    hardCoreFixedShiftMass G S I z k ((k : ℤ) - y) =
      (countIndependent G (S \ I) y : ℝ) * z ^ y / partitionFunction G S z := by
  classical
  have he (j : ℕ) : (k : ℤ) - j = (k : ℤ) - y ↔ j = y := by omega
  unfold hardCoreFixedShiftMass hardCoreLayerExpectation
  simp_rw [he]
  have hinner (j : ℕ) :
      (∑ m ∈ range (I.card + 1), hardCoreLayerWeight G S I z j m *
        (if j = y then (1 - z / (1 + z)) ^ m else 0)) =
      if j = y then (countIndependent G (S \ I) j : ℝ) * z ^ j / partitionFunction G S z else 0 := by
    by_cases hj : j = y
    · simp only [hj, ↓reduceIte]
      simp_rw [hardCoreLayerWeight_cancel_noise G S I hz]
      rw [← sum_div, ← sum_mul, ← Nat.cast_sum, sum_layerCount_eq_countIndependent]
    · simp [hj]
  simp_rw [hinner]
  by_cases hy : y ∈ range ((S \ I).card + 1)
  · simp [hy]
  · have hlarge : (S \ I).card < y := by simpa using hy
    rw [countIndependent_eq_zero_of_gt G (S \ I) hlarge]
    simp [hy]

theorem hardCoreFixedShiftMass_eq_zero_of_lt (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) (k : ℕ) (r : ℤ) (hr : (k : ℤ) < r) :
    hardCoreFixedShiftMass G S I z k r = 0 := by
  unfold hardCoreFixedShiftMass hardCoreLayerExpectation
  have hneq (j : ℕ) : ¬ (k : ℤ) - j = r := by omega
  simp [hneq]

/-- Total signed-index form, with the nonnegative conversion guarded before
using `Int.toNat`. Out-of-cardinality support is handled by the true count. -/
theorem hardCoreFixedShiftMass_eq_guarded_count (G : SimpleGraph V) (S I : Finset V)
    {z : ℝ} (hz : 0 < z) (k : ℕ) (r : ℤ) :
    hardCoreFixedShiftMass G S I z k r =
      if r ≤ (k : ℤ) then
        (countIndependent G (S \ I) ((k : ℤ) - r).toNat : ℝ) *
          z ^ ((k : ℤ) - r).toNat / partitionFunction G S z else 0 := by
  by_cases hr : r ≤ (k : ℤ)
  · rw [if_pos hr]
    have he : (k : ℤ) - (((k : ℤ) - r).toNat : ℤ) = r := by omega
    simpa only [he] using hardCoreFixedShiftMass_eq_count G S I hz k ((k : ℤ) - r).toNat
  · rw [if_neg hr]
    exact hardCoreFixedShiftMass_eq_zero_of_lt G S I z k r (lt_of_not_ge hr)

/-- Any proved count envelope and positive partition lower bound yield the
actual charge bound; no independence between layer variables is assumed. -/
theorem hardCoreFixedShiftMass_le_of_count_partition
    (G : SimpleGraph V) (S I : Finset V) {z : ℝ} (hz : 0 < z)
    (k y : ℕ) (A P : ℝ) (hcount : (countIndependent G (S \ I) y : ℝ) ≤ A)
    (hP : 0 < P) (hpartition : P ≤ partitionFunction G S z) :
    hardCoreFixedShiftMass G S I z k ((k : ℤ) - y) ≤ A * z ^ y / P := by
  rw [hardCoreFixedShiftMass_eq_count G S I hz]
  apply le_trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcount (pow_nonneg hz.le _)) (partitionFunction_pos G S hz.le).le)
  apply div_le_div_of_nonneg_left _ hP hpartition
  exact mul_nonneg (le_trans (Nat.cast_nonneg _) hcount) (pow_nonneg hz.le _)

theorem partitionFunction_eq_count_sum (G : SimpleGraph V) (S : Finset V) (z : ℝ) :
    partitionFunction G S z =
      ∑ k ∈ range (S.card + 1), (countIndependent G S k : ℝ) * z ^ k := by
  classical
  have hcover : ∀ J ∈ independentSubsets G S, J.card ∈ range (S.card + 1) := by
    intro J hJ
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_independentSubsets.mp hJ).1))
  have hf := sum_fiberwise_of_maps_to hcover (fun J => z ^ J.card)
  unfold partitionFunction
  rw [← hf]
  apply sum_congr rfl
  intro k _
  have he : (∑ J ∈ (independentSubsets G S).filter (fun J => J.card = k), z ^ J.card) =
      ∑ _J ∈ (independentSubsets G S).filter (fun J => J.card = k), z ^ k := by
    apply sum_congr rfl
    intro J hJ
    rw [(mem_filter.mp hJ).2]
  rw [he]
  simp [countIndependent]

noncomputable def pathPartitionLower (n : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (Nat.choose (n + 1 - k) k : ℝ) * z ^ k

theorem pathPartitionLower_le_partitionFunction (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) {z : ℝ} (hz : 0 ≤ z) :
    pathPartitionLower S.card z ≤ partitionFunction G S z := by
  rw [partitionFunction_eq_count_sum]
  apply sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast choose_path_le_countIndependent G hG S k)
    (pow_nonneg hz _)

theorem pathPartitionLower_pos (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 < pathPartitionLower n z := by
  unfold pathPartitionLower
  apply sum_pos'
  · intro k _
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)
  · exact ⟨0, by simp, by simp⟩

theorem hardCoreFixedShiftMass_le_path_bound
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S I : Finset V) {z : ℝ} (hz : 0 < z)
    (k y : ℕ) (A : ℝ) (hcount : (countIndependent G (S \ I) y : ℝ) ≤ A) :
    hardCoreFixedShiftMass G S I z k ((k : ℤ) - y) ≤
      A * z ^ y / pathPartitionLower S.card z :=
  hardCoreFixedShiftMass_le_of_count_partition G S I hz k y A _ hcount
    (pathPartitionLower_pos _ hz.le) (pathPartitionLower_le_partitionFunction G hG S hz.le)

#print axioms hardCoreFixedShiftMass_eq_count
#print axioms hardCoreFixedShiftMass_eq_zero_of_lt
#print axioms hardCoreFixedShiftMass_eq_guarded_count
#print axioms hardCoreFixedShiftMass_le_of_count_partition
#print axioms hardCoreFixedShiftMass_le_path_bound
end ForestUnimodality
