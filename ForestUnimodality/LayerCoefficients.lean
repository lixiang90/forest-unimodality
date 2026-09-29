import ForestUnimodality.LayerCounts
import ForestUnimodality.SubsetPolynomial
import ForestUnimodality.ShiftedChoose

/-!
Taking coefficients in the layer decomposition gives the guarded binomial
formula for actual independent-set counts. The assumptions concern only an
independent subset of the ambient vertex set; no forest hypothesis is needed.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Each layer contributes its multiplicity times the coefficient of its
shifted binomial block, over any commutative coefficient semiring. -/
theorem coeff_partitionFunction_layer_sum {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S)
    (hI : G.IsIndepSet (I : Set V)) (k : ℕ) :
    (partitionFunction G S (Polynomial.X : Polynomial R)).coeff k =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : R) * (shiftedChoose m j k : R) := by
  rw [partitionFunction_layer_decomposition G S I hIS hI]
  simp only [Polynomial.finsetSum_coeff, mul_assoc,
    Polynomial.coeff_natCast_mul, coeff_shifted_binomial]

/-- The layer formula for independent-set counts after casting to a semiring. -/
theorem countIndependent_cast_eq_layer_sum {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S)
    (hI : G.IsIndepSet (I : Set V)) (k : ℕ) :
    (countIndependent G S k : R) =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : R) * (shiftedChoose m j k : R) := by
  rw [← coeff_partitionFunction G S k]
  exact coeff_partitionFunction_layer_sum G S I hIS hI k

/-- The exact natural-number layer formula for the coefficient of degree `k`. -/
theorem countIndependent_eq_layer_sum
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S)
    (hI : G.IsIndepSet (I : Set V)) (k : ℕ) :
    countIndependent G S k =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        layerCount G I (S \ I) j m * shiftedChoose m j k := by
  exact countIndependent_cast_eq_layer_sum (R := ℕ) G S I hIS hI k

/-- Adjacent differences use subtraction in the coefficient ring, retaining
the lower-index guards in both binomial terms. -/
theorem countIndependent_difference_eq_layer_sum {R : Type*} [CommRing R]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S)
    (hI : G.IsIndepSet (I : Set V)) (k : ℕ) :
    (countIndependent G S (k + 1) : R) - (countIndependent G S k : R) =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : R) *
          ((shiftedChoose m j (k + 1) : R) - (shiftedChoose m j k : R)) := by
  rw [countIndependent_cast_eq_layer_sum G S I hIS hI (k + 1),
    countIndependent_cast_eq_layer_sum G S I hIS hI k]
  simp only [mul_sub, Finset.sum_sub_distrib]

#print axioms coeff_partitionFunction_layer_sum
#print axioms countIndependent_cast_eq_layer_sum
#print axioms countIndependent_eq_layer_sum
#print axioms countIndependent_difference_eq_layer_sum

end ForestUnimodality
