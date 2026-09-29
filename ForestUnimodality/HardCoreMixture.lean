import ForestUnimodality.AnalyticKernelSign
import ForestUnimodality.LayerCoefficients

/-! The hard-core cardinality distribution is an exact binomial mixture over
the actual layer counts of a fixed independent subset. Integer shifts are
guarded before conversion to natural indices; no independence of the layer
coordinates is assumed. -/

namespace ForestUnimodality
open Finset

noncomputable def binomialMass (m : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  if 0 ≤ j ∧ j ≤ (m : ℤ) then
    (m.choose j.toNat : ℝ) * q ^ j.toNat * (1 - q) ^ (m - j.toNat)
  else 0

theorem binomialMass_nonneg (m : ℕ) (j : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ binomialMass m j q := by
  unfold binomialMass
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _))
      (pow_nonneg (sub_nonneg.mpr hq1) _)
  · exact le_refl _

theorem binomial_activity_cancel (m d : ℕ) (hd : d ≤ m) {z : ℝ} (hz : 0 < z) :
    (1 + z) ^ m * (z / (1 + z)) ^ d * (1 - z / (1 + z)) ^ (m - d) = z ^ d := by
  have hb : 1 + z ≠ 0 := by positivity
  have hcomp : 1 - z / (1 + z) = 1 / (1 + z) := by field_simp; ring
  have hp : (1 + z) ^ d * (1 + z) ^ (m - d) = (1 + z) ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hd]
  rw [hcomp, div_pow, div_pow, one_pow]
  field_simp
  nlinarith [hp]

theorem weighted_binomialMass_eq (m y k : ℕ) {z Z : ℝ} (hz : 0 < z) :
    (z ^ y * (1 + z) ^ m / Z) * binomialMass m ((k : ℤ) - y) (z / (1 + z)) =
      (shiftedChoose m y k : ℝ) * z ^ k / Z := by
  by_cases hyk : y ≤ k
  · have hjnonneg : (0 : ℤ) ≤ (k : ℤ) - y := by omega
    have hjnat : ((k : ℤ) - y).toNat = k - y := by omega
    by_cases hkm : k - y ≤ m
    · have hjm : (k : ℤ) - y ≤ m := by omega
      rw [binomialMass, if_pos ⟨hjnonneg, hjm⟩, hjnat, shiftedChoose_of_le m hyk]
      have hc := binomial_activity_cancel m (k - y) hkm hz
      have hp : z ^ y * z ^ (k - y) = z ^ k := by
        rw [← pow_add, Nat.add_sub_of_le hyk]
      calc
        _ = (m.choose (k - y) : ℝ) * z ^ y / Z *
            ((1 + z) ^ m * (z / (1 + z)) ^ (k - y) *
              (1 - z / (1 + z)) ^ (m - (k - y))) := by ring
        _ = (m.choose (k - y) : ℝ) * z ^ k / Z := by rw [hc]; rw [← hp]; ring
    · have hjm : ¬ ((k : ℤ) - y ≤ (m : ℤ)) := by omega
      have hc : m.choose (k - y) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [binomialMass, hjm, shiftedChoose_of_le m hyk, hc]
  · simp [binomialMass, shiftedChoose, hyk]

variable {V : Type*} [DecidableEq V]

noncomputable def hardCoreLayerWeight (G : SimpleGraph V) (S I : Finset V)
    (z : ℝ) (j m : ℕ) : ℝ :=
  (layerCount G I (S \ I) j m : ℝ) * z ^ j * (1 + z) ^ m / partitionFunction G S z

theorem hardCoreLayerWeight_nonneg (G : SimpleGraph V) (S I : Finset V)
    {z : ℝ} (hz : 0 ≤ z) (j m : ℕ) : 0 ≤ hardCoreLayerWeight G S I z j m := by
  unfold hardCoreLayerWeight
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
    (pow_nonneg (by linarith) _)) (partitionFunction_pos G S hz).le

theorem sum_hardCoreLayerWeight (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 ≤ z) :
    (∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
      hardCoreLayerWeight G S I z j m) = 1 := by
  simp only [hardCoreLayerWeight, div_eq_mul_inv, ← sum_mul]
  have hZ := partitionFunction_layer_decomposition G S I hIS hI z
  rw [← hZ]
  exact mul_inv_cancel₀ (ne_of_gt (partitionFunction_pos G S hz))

/-- Every cardinality probability is the same mixture of guarded binomial
probabilities, including k outside the graph's support. -/
theorem tiltedProbability_eq_binomial_mixture (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) (k : ℕ) :
    tiltedProbability (countIndependent G S) z (partitionFunction G S z) k =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        hardCoreLayerWeight G S I z j m *
          binomialMass m ((k : ℤ) - j) (z / (1 + z)) := by
  have hterm : ∀ j m,
      hardCoreLayerWeight G S I z j m * binomialMass m ((k : ℤ) - j) (z / (1 + z)) =
        (layerCount G I (S \ I) j m : ℝ) * (shiftedChoose m j k : ℝ) *
          z ^ k / partitionFunction G S z := by
    intro j m
    have h := weighted_binomialMass_eq m j k (Z := partitionFunction G S z) hz
    dsimp [hardCoreLayerWeight]
    calc
      _ = (layerCount G I (S \ I) j m : ℝ) *
          ((z ^ j * (1 + z) ^ m / partitionFunction G S z) *
            binomialMass m ((k : ℤ) - j) (z / (1 + z))) := by ring
      _ = _ := by rw [h]; ring
  simp_rw [hterm]
  rw [tiltedProbability, countIndependent_cast_eq_layer_sum (R := ℝ) G S I hIS hI k]
  simp only [div_eq_mul_inv, sum_mul]

#print axioms weighted_binomialMass_eq
#print axioms sum_hardCoreLayerWeight
#print axioms tiltedProbability_eq_binomial_mixture

end ForestUnimodality
