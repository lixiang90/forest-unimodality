import ForestUnimodality.GraphCore
import Mathlib.Algebra.Polynomial.Coeff

/-! Finite subset sums and their generating polynomial coefficients. -/

namespace ForestUnimodality

open Finset

variable {V : Type*}
variable {R : Type*} [CommSemiring R]

/-- The generating function of all subsets of a finite set. -/
theorem sum_powerset_pow_card (S : Finset V) (z : R) :
    (∑ T ∈ S.powerset, z ^ T.card) = (1 + z) ^ S.card := by
  simpa using (Finset.prod_one_add (f := fun _ : V => z) S).symm

/-- Adding a fixed cardinality to each exponent shifts the subset generating function. -/
theorem sum_powerset_pow_add_card (S : Finset V) (z : R) (j : ℕ) :
    (∑ T ∈ S.powerset, z ^ (j + T.card)) = z ^ j * (1 + z) ^ S.card := by
  simp_rw [pow_add]
  rw [← Finset.mul_sum, sum_powerset_pow_card]

variable [DecidableEq V]

/-- The coefficient of degree `k` counts independent subsets of cardinality `k`. -/
theorem coeff_partitionFunction (G : SimpleGraph V) (S : Finset V) (k : ℕ) :
    (partitionFunction G S (Polynomial.X : Polynomial R)).coeff k =
      (countIndependent G S k : R) := by
  classical
  simp [partitionFunction, countIndependent, eq_comm]

end ForestUnimodality

#print axioms ForestUnimodality.sum_powerset_pow_card
#print axioms ForestUnimodality.sum_powerset_pow_add_card
#print axioms ForestUnimodality.coeff_partitionFunction
