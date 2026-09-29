import ForestUnimodality.ForestIndependenceBound
import ForestUnimodality.LayerCoefficients
import ForestUnimodality.GraphBounds
import Mathlib.Data.Nat.Choose.Sum

/-!
Coefficient bounds from maximum-independent-set layers. The comparison
polynomial is the independence polynomial of disjoint edges and isolated
vertices, but the proof does not require constructing a matching in the graph.
All binomial shifts include their lower-index guard.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- The explicit coefficient used for the matching comparison polynomial. -/
def matchingUpperCount (a v k : ℕ) : ℕ :=
  ∑ j ∈ range (v + 1), v.choose j * 2^j * shiftedChoose (a - v) j k

theorem shiftedChoose_mono_left {m n : ℕ} (hmn : m ≤ n) (j k : ℕ) :
    shiftedChoose m j k ≤ shiftedChoose n j k := by
  by_cases hjk : j ≤ k
  · simp only [shiftedChoose, if_pos hjk]
    exact Nat.choose_le_choose (k - j) hmn
  · simp [shiftedChoose, hjk]

/-- Triangular support and the elementary layer-mass bound give this
coefficient bound for any maximum independent subset of any graph. -/
theorem IsMaximumIndependentOn.countIndependent_le_layer_majorant
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (k : ℕ) :
    countIndependent G S k ≤
      ∑ j ∈ range ((S \ I).card + 1),
        ((S \ I).card).choose j * shiftedChoose (I.card - j) j k := by
  rw [countIndependent_eq_layer_sum G S I hI.subset hI.independent]
  apply sum_le_sum
  intro j hj
  calc
    (∑ m ∈ range (I.card + 1),
        layerCount G I (S \ I) j m * shiftedChoose m j k) ≤
        ∑ m ∈ range (I.card + 1),
          layerCount G I (S \ I) j m * shiftedChoose (I.card - j) j k := by
      apply sum_le_sum
      intro m hm
      by_cases hlarge : I.card < j + m
      · rw [hI.layerCount_eq_zero_of_card_lt hlarge]
        simp
      · apply Nat.mul_le_mul_left
        apply shiftedChoose_mono_left
        omega
    _ = countIndependent G (S \ I) j * shiftedChoose (I.card - j) j k := by
      rw [← sum_mul, sum_layerCount_eq_countIndependent]
    _ ≤ ((S \ I).card).choose j * shiftedChoose (I.card - j) j k :=
      Nat.mul_le_mul_right _ (countIndependent_le_choose G (S \ I) j)

/-- The binomial identity that rewrites the layer majorant as the matching
comparison polynomial. It uses only v ≤ a. -/
theorem sum_choose_shifted_binomial {R : Type*} [CommSemiring R]
    (a v : ℕ) (hva : v ≤ a) (z : R) :
    (∑ j ∈ range (v + 1), (v.choose j : R) * z^j * (1 + z)^(a - j)) =
      (1 + 2 * z)^v * (1 + z)^(a - v) := by
  have hbase : 1 + 2 * z = z + (1 + z) := by ring
  rw [hbase, add_pow, sum_mul]
  apply sum_congr rfl
  intro j hj
  have hjv : j ≤ v := Nat.le_of_lt_succ (mem_range.mp hj)
  have hexp : a - j = (v - j) + (a - v) := by omega
  rw [hexp, pow_add]
  ac_rfl

/-- Expanding the matching polynomial gives its explicit guarded coefficients. -/
theorem matching_polynomial_eq_sum {R : Type*} [CommSemiring R]
    (a v : ℕ) (z : R) :
    (1 + 2 * z)^v * (1 + z)^(a - v) =
      ∑ j ∈ range (v + 1), ((v.choose j * 2^j : ℕ) : R) *
        z^j * (1 + z)^(a - v) := by
  rw [add_comm 1 (2 * z), add_pow, sum_mul]
  apply sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one, mul_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem coeff_matching_polynomial (a v k : ℕ) :
    (((1 + 2 * Polynomial.X)^v * (1 + Polynomial.X)^(a - v) :
      Polynomial ℕ).coeff k) = matchingUpperCount a v k := by
  rw [matching_polynomial_eq_sum]
  simp only [Polynomial.finsetSum_coeff, mul_assoc,
    Polynomial.coeff_natCast_mul, coeff_shifted_binomial, matchingUpperCount,
    Nat.cast_id]

theorem layer_majorant_eq_matchingUpperCount
    (a v k : ℕ) (hva : v ≤ a) :
    (∑ j ∈ range (v + 1), v.choose j * shiftedChoose (a - j) j k) =
      matchingUpperCount a v k := by
  have h := congrArg (fun p : Polynomial ℕ => p.coeff k)
    (sum_choose_shifted_binomial a v hva (Polynomial.X : Polynomial ℕ))
  simpa only [Polynomial.finsetSum_coeff, mul_assoc,
    Polynomial.coeff_natCast_mul, coeff_shifted_binomial, Nat.cast_id,
    coeff_matching_polynomial] using h

/-- The finite-sum upper bound for graphs whose chosen maximum independent
subset contains at least half of their vertices. -/
theorem IsMaximumIndependentOn.countIndependent_le_matchingUpperCount
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hsize : (S \ I).card ≤ I.card) (k : ℕ) :
    countIndependent G S k ≤ matchingUpperCount I.card (S \ I).card k := by
  have h := hI.countIndependent_le_layer_majorant k
  rwa [layer_majorant_eq_matchingUpperCount _ _ _ hsize] at h

/-- Every finite forest satisfies the matching comparison bound, expressed
exactly as the guarded natural-number sum used in finite certificates. -/
theorem IsMaximumIndependentOn.countIndependent_le_matchingUpperCount_of_isAcyclic
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic) (k : ℕ) :
    countIndependent G S k ≤ matchingUpperCount I.card (S.card - I.card) k := by
  have hhalf := hI.card_le_two_mul_of_isAcyclic hG
  have hsub := card_le_card hI.subset
  have hdiff : (S \ I).card = S.card - I.card := card_sdiff_of_subset hI.subset
  have hsize : (S \ I).card ≤ I.card := by rw [hdiff]; omega
  simpa only [hdiff] using hI.countIndependent_le_matchingUpperCount hsize k

/-- Polynomial-coefficient form of the forest bound. -/
theorem IsMaximumIndependentOn.countIndependent_le_matching_coeff_of_isAcyclic
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic) (k : ℕ) :
    countIndependent G S k ≤
      (((1 + 2 * Polynomial.X)^(S.card - I.card) *
        (1 + Polynomial.X)^(2 * I.card - S.card) : Polynomial ℕ).coeff k) := by
  have hsub := card_le_card hI.subset
  have hexp : I.card - (S.card - I.card) = 2 * I.card - S.card := by omega
  rw [← hexp, coeff_matching_polynomial]
  exact hI.countIndependent_le_matchingUpperCount_of_isAcyclic hG k

#print axioms IsMaximumIndependentOn.countIndependent_le_layer_majorant
#print axioms sum_choose_shifted_binomial
#print axioms coeff_matching_polynomial
#print axioms layer_majorant_eq_matchingUpperCount
#print axioms IsMaximumIndependentOn.countIndependent_le_matchingUpperCount_of_isAcyclic
#print axioms IsMaximumIndependentOn.countIndependent_le_matching_coeff_of_isAcyclic

end ForestUnimodality
