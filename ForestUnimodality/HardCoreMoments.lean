import ForestUnimodality.GraphCore
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite hard-core moments, directly over the independent subsets of S.
No probability measure construction, forest assumption, or external moment
identity is used. Positive activity makes the partition function nonzero. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- The unnormalized q-th moment of independent-set size. -/
noncomputable def hardCoreMomentNumerator (G : SimpleGraph V) (S : Finset V)
    (q : ℕ) (z : ℝ) : ℝ :=
  ∑ J ∈ independentSubsets G S, (J.card : ℝ)^q * z^J.card

noncomputable def hardCoreMean (G : SimpleGraph V) (S : Finset V) (z : ℝ) : ℝ :=
  hardCoreMomentNumerator G S 1 z / partitionFunction G S z

noncomputable def hardCoreSecondMoment (G : SimpleGraph V) (S : Finset V) (z : ℝ) : ℝ :=
  hardCoreMomentNumerator G S 2 z / partitionFunction G S z

noncomputable def hardCoreVariance (G : SimpleGraph V) (S : Finset V) (z : ℝ) : ℝ :=
  hardCoreSecondMoment G S z - (hardCoreMean G S z)^2

theorem empty_mem_independentSubsets (G : SimpleGraph V) (S : Finset V) :
    ∅ ∈ independentSubsets G S := by
  simp [mem_independentSubsets, SimpleGraph.IsIndepSet, Set.Pairwise]

/-- The empty set contributes exactly one to every nonnegative-activity Z. -/
theorem one_le_partitionFunction (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 1 ≤ partitionFunction G S z := by
  have h := single_le_sum (s := independentSubsets G S) (f := fun J => z^J.card)
    (fun J _ => pow_nonneg hz _) (empty_mem_independentSubsets G S)
  simpa only [card_empty, pow_zero, partitionFunction] using h

theorem partitionFunction_pos (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 0 < partitionFunction G S z :=
  lt_of_lt_of_le zero_lt_one (one_le_partitionFunction G S hz)

@[simp] theorem hardCoreMomentNumerator_zero (G : SimpleGraph V) (S : Finset V) (z : ℝ) :
    hardCoreMomentNumerator G S 0 z = partitionFunction G S z := by
  simp [hardCoreMomentNumerator, partitionFunction]

private theorem weighted_pow_derivative (n q : ℕ) (z : ℝ) (hz : z ≠ 0) :
    (n : ℝ)^q * ((n : ℝ) * z^(n - 1)) = (n : ℝ)^(q + 1) * z^n / z := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one, pow_succ]
    field_simp

/-- Differentiating a moment increases its order and divides by activity. -/
theorem hasDerivAt_hardCoreMomentNumerator (G : SimpleGraph V) (S : Finset V)
    (q : ℕ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (hardCoreMomentNumerator G S q)
      (hardCoreMomentNumerator G S (q + 1) z / z) z := by
  have hd := HasDerivAt.fun_sum (u := independentSubsets G S)
    (fun J _ => (hasDerivAt_pow J.card z).const_mul ((J.card : ℝ)^q))
  have heq : (∑ J ∈ independentSubsets G S,
      (J.card : ℝ)^q * ((J.card : ℝ) * z^(J.card - 1))) =
      hardCoreMomentNumerator G S (q + 1) z / z := by
    simp_rw [weighted_pow_derivative _ _ z hz, div_eq_mul_inv]
    rw [← sum_mul]
    rfl
  rw [heq] at hd
  exact hd

theorem hasDerivAt_partitionFunction (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ => partitionFunction G S x)
      (hardCoreMomentNumerator G S 1 z / z) z := by
  have hfun : hardCoreMomentNumerator G S 0 =
      (fun x : ℝ => partitionFunction G S x) := by
    funext x
    exact hardCoreMomentNumerator_zero G S x
  rw [← hfun]
  exact hasDerivAt_hardCoreMomentNumerator G S 0 hz

/-- Exact finite-distribution identity dμ/dz = Var(K)/z. -/
theorem hasDerivAt_hardCoreMean (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (hardCoreMean G S) (hardCoreVariance G S z / z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hZne : partitionFunction G S z ≠ 0 := ne_of_gt (partitionFunction_pos G S hz.le)
  have hd := (hasDerivAt_hardCoreMomentNumerator G S 1 hzne).div
    (hasDerivAt_partitionFunction G S hzne) hZne
  have heq : hardCoreVariance G S z / z =
      ((hardCoreMomentNumerator G S 2 z / z) * partitionFunction G S z -
        hardCoreMomentNumerator G S 1 z * (hardCoreMomentNumerator G S 1 z / z)) /
          (partitionFunction G S z)^2 := by
    dsimp [hardCoreVariance, hardCoreSecondMoment, hardCoreMean]
    field_simp
  rw [heq]
  exact hd

/-- Expanding squared deviations gives the variance times the partition sum. -/
theorem hardCoreVariance_mul_partitionFunction (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) :
    hardCoreVariance G S z * partitionFunction G S z =
      ∑ J ∈ independentSubsets G S,
        ((J.card : ℝ) - hardCoreMean G S z)^2 * z^J.card := by
  have hZne : partitionFunction G S z ≠ 0 := ne_of_gt (partitionFunction_pos G S hz)
  have hsum : (∑ J ∈ independentSubsets G S,
      ((J.card : ℝ) - hardCoreMean G S z)^2 * z^J.card) =
      hardCoreMomentNumerator G S 2 z -
        (2 * hardCoreMean G S z) * hardCoreMomentNumerator G S 1 z +
        (hardCoreMean G S z)^2 * partitionFunction G S z := by
    calc
      _ = ∑ J ∈ independentSubsets G S,
          ((J.card : ℝ)^2 * z^J.card -
            (2 * hardCoreMean G S z) * ((J.card : ℝ) * z^J.card) +
            (hardCoreMean G S z)^2 * z^J.card) := by
        apply sum_congr rfl
        intro J _
        ring
      _ = _ := by
        simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum,
          hardCoreMomentNumerator, partitionFunction, pow_one]
  rw [hsum]
  dsimp [hardCoreVariance, hardCoreSecondMoment, hardCoreMean]
  field_simp
  ring

theorem hardCoreVariance_nonneg (G : SimpleGraph V) (S : Finset V)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ hardCoreVariance G S z := by
  have hsum : 0 ≤ ∑ J ∈ independentSubsets G S,
      ((J.card : ℝ) - hardCoreMean G S z)^2 * z^J.card :=
    sum_nonneg (fun J _ => mul_nonneg (sq_nonneg _) (pow_nonneg hz _))
  rw [← hardCoreVariance_mul_partitionFunction G S hz] at hsum
  exact nonneg_of_mul_nonneg_left hsum (partitionFunction_pos G S hz)

/-- A nonempty ambient set has positive mean because one singleton has
strictly positive weight. -/
theorem hardCoreMean_pos (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    {z : ℝ} (hz : 0 < z) : 0 < hardCoreMean G S z := by
  obtain ⟨v, hv⟩ := hS
  have hsingle : ({v} : Finset V) ∈ independentSubsets G S := by
    simp [mem_independentSubsets, hv, SimpleGraph.IsIndepSet, Set.Pairwise]
  have h := single_le_sum (s := independentSubsets G S)
    (f := fun J => (J.card : ℝ)^1 * z^J.card)
    (fun J _ => mul_nonneg (by positivity) (pow_nonneg hz.le _)) hsingle
  have hnum : z ≤ hardCoreMomentNumerator G S 1 z := by
    simpa only [card_singleton, Nat.cast_one, pow_one, one_mul,
      hardCoreMomentNumerator] using h
  exact div_pos (hz.trans_le hnum) (partitionFunction_pos G S hz.le)

/-- Positive mean and the empty-set contribution force strictly positive
variance on every nonempty graph at every positive activity. -/
theorem hardCoreVariance_pos (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty)
    {z : ℝ} (hz : 0 < z) : 0 < hardCoreVariance G S z := by
  have hmu := hardCoreMean_pos G S hS hz
  have h := single_le_sum (s := independentSubsets G S)
    (f := fun J => ((J.card : ℝ) - hardCoreMean G S z)^2 * z^J.card)
    (fun J _ => mul_nonneg (sq_nonneg _) (pow_nonneg hz.le _))
    (empty_mem_independentSubsets G S)
  have hsum : (hardCoreMean G S z)^2 ≤
      ∑ J ∈ independentSubsets G S,
        ((J.card : ℝ) - hardCoreMean G S z)^2 * z^J.card := by
    simpa only [card_empty, Nat.cast_zero, zero_sub, neg_sq, pow_zero, mul_one] using h
  rw [← hardCoreVariance_mul_partitionFunction G S hz.le] at hsum
  have hprod : 0 < hardCoreVariance G S z * partitionFunction G S z :=
    (sq_pos_of_pos hmu).trans_le hsum
  exact pos_of_mul_pos_left hprod (partitionFunction_pos G S hz.le).le

/-- The hard-core mean is strictly increasing throughout positive activity. -/
theorem hardCoreMean_strictMonoOn (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) :
    StrictMonoOn (hardCoreMean G S) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
  · intro z hz
    exact (hasDerivAt_hardCoreMean G S hz).continuousAt.continuousWithinAt
  · intro z hz
    have hzpos : 0 < z := by simpa only [interior_Ioi, Set.mem_Ioi] using hz
    rw [(hasDerivAt_hardCoreMean G S hzpos).deriv]
    exact div_pos (hardCoreVariance_pos G S hS hzpos) hzpos

#print axioms one_le_partitionFunction
#print axioms hasDerivAt_hardCoreMomentNumerator
#print axioms hasDerivAt_hardCoreMean
#print axioms hardCoreVariance_mul_partitionFunction
#print axioms hardCoreVariance_nonneg
#print axioms hardCoreMean_pos
#print axioms hardCoreVariance_pos
#print axioms hardCoreMean_strictMonoOn
end ForestUnimodality
