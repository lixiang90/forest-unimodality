import ForestUnimodality.MarginalFixedShiftBound

/-! A finite, computable support and joint-count interface for the last
certificate stage. The finite list contains graph-order/rank pairs. Its
completeness is an explicit premise, not inferred from saved metadata. -/
namespace ForestUnimodality.FiniteMarginalSupport
open Finset

def pathPartitionRat (n : ℕ) (a : ℚ) : ℚ :=
  ∑ y ∈ range (n + 1), (Nat.choose (n + 1 - y) y : ℚ) * a ^ y

theorem pathPartitionRat_cast (n : ℕ) (a : ℚ) :
    (pathPartitionRat n a : ℝ) = pathPartitionLower n a := by
  simp [pathPartitionRat, pathPartitionLower]

theorem pathPartitionLower_mono (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    pathPartitionLower n a ≤ pathPartitionLower n b := by
  apply sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (Nat.cast_nonneg _)

def endpointMass (a b : ℚ) (nk : ℕ × ℕ) (j : ℤ) : ℚ :=
  if j ≤ (nk.2 : ℤ) then
    (marginalCountEnvelope nk.1 0 ((nk.2 : ℤ) - j).toNat : ℚ) *
      b ^ ((nk.2 : ℤ) - j).toNat / pathPartitionRat nk.1 a
  else 0

def jointCountBound (a b : ℚ) (j : ℤ) : List (ℕ × ℕ) → ℚ
  | [] => 0
  | nk :: rest => max (endpointMass a b nk j) (jointCountBound a b j rest)

theorem jointCountBound_nonneg (a b : ℚ) (j : ℤ) (pairs : List (ℕ × ℕ)) :
    0 ≤ jointCountBound a b j pairs := by
  induction pairs with
  | nil => rfl
  | cons nk rest ih => exact ih.trans (le_max_right _ _)

theorem endpointMass_le_jointCountBound (a b : ℚ) (j : ℤ) {nk : ℕ × ℕ}
    {pairs : List (ℕ × ℕ)} (hmem : nk ∈ pairs) :
    endpointMass a b nk j ≤ jointCountBound a b j pairs := by
  induction pairs with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact le_max_left _ _
      · exact (ih hrest).trans (le_max_right _ _)

def supportCheck (pairs : List (ℕ × ℕ)) (m : ℕ) (j : ℤ) : Bool :=
  pairs.any fun nk => decide (j ≤ (nk.2 : ℤ) ∧
    0 < marginalCountEnvelope nk.1 m ((nk.2 : ℤ) - j).toNat)

variable {V : Type*} [DecidableEq V]

theorem layerCount_pos_of_weight_pos {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    {y m : ℕ} (hw : 0 < hardCoreLayerWeight G S B z y m) :
    0 < layerCount G B (S \ B) y m := by
  by_contra h
  have hz : layerCount G B (S \ B) y m = 0 := by omega
  simp [hardCoreLayerWeight, hz] at hw

theorem actual_support {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) (k : ℕ)
    (pairs : List (ℕ × ℕ)) (hpairs : (S.card, k) ∈ pairs)
    {y m : ℕ} (hw : 0 < hardCoreLayerWeight G S B z y m) :
    supportCheck pairs m ((k : ℤ) - y) = true := by
  apply List.any_eq_true.mpr
  refine ⟨(S.card, k), hpairs, ?_⟩
  apply decide_eq_true
  have hy : ((k : ℤ) - ((k : ℤ) - y)).toNat = y := by omega
  refine ⟨by omega, ?_⟩
  simpa only [hy] using
    hB.marginalEnvelope_pos_of_layerCount_pos hG hz (layerCount_pos_of_weight_pos hw)

theorem actual_endpoint_bound {G : SimpleGraph V} (hG : G.IsAcyclic)
    {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    {a b : ℚ} (ha : 0 ≤ a) (hlo : (a : ℝ) ≤ z) (hhi : z ≤ (b : ℝ))
    (k : ℕ) (j : ℤ) :
    hardCoreFixedShiftMass G S B z k j ≤ (endpointMass a b (S.card, k) j : ℝ) := by
  by_cases hj : j ≤ (k : ℤ)
  · let y := ((k : ℤ) - j).toNat
    have hshift : (k : ℤ) - (y : ℤ) = j := by dsimp [y]; omega
    have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hp : pathPartitionLower S.card a ≤ partitionFunction G S z :=
      (pathPartitionLower_mono S.card haR hlo).trans
        (pathPartitionLower_le_partitionFunction G hG S hz.le)
    have hc : (countIndependent G (S \ B) y : ℝ) ≤
        (marginalCountEnvelope S.card 0 y : ℝ) := by
      exact_mod_cast hB.countIndependent_complement_le_marginalEnvelope hG hz (Nat.zero_le _) y
    have h := hardCoreFixedShiftMass_le_of_count_partition G S B hz k y
      (marginalCountEnvelope S.card 0 y) (pathPartitionLower S.card a) hc
      (pathPartitionLower_pos _ haR) hp
    rw [hshift] at h
    have hpw : z ^ y ≤ (b : ℝ) ^ y := pow_le_pow_left₀ hz.le hhi y
    have hm := mul_le_mul_of_nonneg_left hpw (Nat.cast_nonneg (marginalCountEnvelope S.card 0 y) : (0 : ℝ) ≤ _)
    have hd := div_le_div_of_nonneg_right hm (pathPartitionLower_pos S.card haR).le
    simpa only [endpointMass, hj, ↓reduceIte, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_pow, pathPartitionRat_cast, y] using h.trans hd
  · rw [hardCoreFixedShiftMass_eq_zero_of_lt G S B z k j (lt_of_not_ge hj)]
    simp [endpointMass, hj]

theorem actual_joint_count_bound {G : SimpleGraph V} (hG : G.IsAcyclic)
    {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    {a b : ℚ} (ha : 0 ≤ a) (hlo : (a : ℝ) ≤ z) (hhi : z ≤ (b : ℝ))
    (k : ℕ) (j : ℤ) (pairs : List (ℕ × ℕ)) (hpairs : (S.card, k) ∈ pairs) :
    hardCoreFixedShiftMass G S B z k j ≤ (jointCountBound a b j pairs : ℝ) := by
  apply (actual_endpoint_bound hG hB hz ha hlo hhi k j).trans
  exact_mod_cast endpointMass_le_jointCountBound a b j hpairs

#print axioms actual_support
#print axioms actual_endpoint_bound
#print axioms actual_joint_count_bound
end ForestUnimodality.FiniteMarginalSupport
