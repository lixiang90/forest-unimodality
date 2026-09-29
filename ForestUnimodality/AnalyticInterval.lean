import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Continuous-interval soundness for analytic certificates.

The proofs below are independent implementations of the elementary interpolation
argument used by the finite binomial-mixture certificates. No supplied numerical
certificate or forest-specific derivative bound is assumed to be verified here.
-/

namespace ForestUnimodality.AnalyticInterval

open Set
open scoped BigOperators

/-- After collecting constant and linear terms, every finite-mixture expectation
budget has this form. The rates may be arbitrary reals for concavity. -/
noncomputable def exponentialBudget {ι : Type*} (terms : Finset ι) (A B D : ℝ)
    (weight rate : ι → ℝ) (m : ℝ) : ℝ :=
  A + B * m - D * m ^ 2 - ∑ i ∈ terms, weight i * Real.exp (-rate i * m)

/-- Nonnegative quadratic and exponential costs make the budget concave.
This proves the required shape, rather than assuming concavity of a supplied
budget function. No sign conditions on the affine part are needed. -/
theorem concaveOn_exponentialBudget {ι : Type*} (terms : Finset ι) (A B D : ℝ)
    (weight rate : ι → ℝ) (hD : 0 ≤ D)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i) :
    ConcaveOn ℝ univ (exponentialBudget terms A B D weight rate) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  simp only [smul_eq_mul]
  have hsq : (s * x + t * y) ^ 2 ≤ s * x ^ 2 + t * y ^ 2 := by
    have ht' : t = 1 - s := by linarith
    subst t
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x - y))]
  have hexp : (∑ i ∈ terms, weight i * Real.exp (-rate i * (s * x + t * y))) ≤
      s * (∑ i ∈ terms, weight i * Real.exp (-rate i * x)) +
      t * (∑ i ∈ terms, weight i * Real.exp (-rate i * y)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := convexOn_exp.2 (mem_univ (-rate i * x))
      (mem_univ (-rate i * y)) hs ht hst
    simp only [smul_eq_mul] at h
    have heq : s * (-rate i * x) + t * (-rate i * y) =
        -rate i * (s * x + t * y) := by ring
    rw [heq] at h
    have hw := mul_le_mul_of_nonneg_left h (hweight i hi)
    nlinarith
  dsimp [exponentialBudget]
  have hcost := mul_le_mul_of_nonneg_left hsq hD
  have ht' : t = 1 - s := by linarith
  subst t
  nlinarith

/-- A concave function is bounded below by any common endpoint lower bound.
The closed interval may consist of a single point. -/
theorem lower_of_concave_endpoints {f : ℝ → ℝ} {a b L x : ℝ}
    (hab : a ≤ b) (hf : ConcaveOn ℝ (Icc a b) f)
    (ha : L ≤ f a) (hb : L ≤ f b) (hx : x ∈ Icc a b) : L ≤ f x := by
  exact (le_min ha hb).trans
    (hf.min_le_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hx)

/-- Strictly positive endpoints of a concave budget imply positivity at every
real parameter in the closed interval, including both endpoints. -/
theorem positive_of_concave_endpoints {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hf : ConcaveOn ℝ (Icc a b) f)
    (ha : 0 < f a) (hb : 0 < f b) (hx : x ∈ Icc a b) : 0 < f x := by
  exact (lt_min ha hb).trans_le
    (hf.min_le_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hx)

/-- Two strict endpoint budget checks cover every real mean in the rectangle. -/
theorem positive_exponentialBudget_of_endpoints {ι : Type*}
    (terms : Finset ι) (A B D : ℝ) (weight rate : ι → ℝ)
    {a b x : ℝ} (hab : a ≤ b) (hD : 0 ≤ D)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (ha : 0 < exponentialBudget terms A B D weight rate a)
    (hb : 0 < exponentialBudget terms A B D weight rate b)
    (hx : x ∈ Icc a b) :
    0 < exponentialBudget terms A B D weight rate x := by
  apply positive_of_concave_endpoints hab _ ha hb hx
  exact (concaveOn_exponentialBudget terms A B D weight rate hD hweight).subset
    (subset_univ _) (convex_Icc a b)

/-- A one-sided second derivative bound gives the sharp quadratic loss from
a common endpoint lower bound. Only differentiability inside the interval and
continuity at the endpoints are needed. -/
theorem lower_of_second_derivative_upper
    {f f' f'' : ℝ → ℝ} {a b Z L x : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo a b, HasDerivAt f' (f'' t) t)
    (hupper : ∀ t ∈ Ioo a b, f'' t ≤ Z)
    (ha : L ≤ f a) (hb : L ≤ f b) (hx : x ∈ Icc a b) :
    L - Z / 2 * (x - a) * (b - x) ≤ f x := by
  let g : ℝ → ℝ := fun t => f t + Z / 2 * ((t - a) * (b - t))
  let g' : ℝ → ℝ := fun t => f' t + Z / 2 * (a + b - 2 * t)
  let g'' : ℝ → ℝ := fun t => f'' t - Z
  have hg : ContinuousOn g (Icc a b) := hf.add
    ((continuous_const.mul ((continuous_id.sub continuous_const).mul
      (continuous_const.sub continuous_id))).continuousOn)
  have hg' : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t := by
    intro t ht
    convert (hf' t ht).add
      ((((hasDerivAt_id t).sub_const a).mul
        ((hasDerivAt_const t b).sub (hasDerivAt_id t))).const_mul (Z / 2)) using 1 <;>
      first | rfl | (dsimp [g, g']; ring)
  have hg'' : ∀ t ∈ Ioo a b, HasDerivAt g' (g'' t) t := by
    intro t ht
    convert (hf'' t ht).add
      (((hasDerivAt_const t (a + b)).sub
        ((hasDerivAt_id t).const_mul 2)).const_mul (Z / 2)) using 1 <;>
      first | rfl | (dsimp [g', g'']; ring)
  have hconcave : ConcaveOn ℝ (Icc a b) g := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b) hg
      (f' := g') (f'' := g'')
    · intro t ht
      exact (hg' t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact (hg'' t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      exact sub_nonpos.mpr (hupper t (by simpa only [interior_Icc] using ht))
  have hga : L ≤ g a := by simpa [g] using ha
  have hgb : L ≤ g b := by simpa [g] using hb
  have h := lower_of_concave_endpoints hab hconcave hga hgb hx
  dsimp [g] at h
  linarith

/-- The endpoint test used by continuous activity certificates: if `f'' ≤ Z`
with `Z ≥ 0`, paying `(b-a)^2 Z / 8` at both endpoints certifies `f ≥ 0`
on the entire closed interval. This is not a grid-sampling argument. -/
theorem nonnegative_of_endpoint_curvature
    {f f' f'' : ℝ → ℝ} {a b Z x : ℝ}
    (hab : a ≤ b) (hZ : 0 ≤ Z) (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf'' : ∀ t ∈ Ioo a b, HasDerivAt f' (f'' t) t)
    (hupper : ∀ t ∈ Ioo a b, f'' t ≤ Z)
    (ha : (b - a) ^ 2 * Z / 8 ≤ f a)
    (hb : (b - a) ^ 2 * Z / 8 ≤ f b) (hx : x ∈ Icc a b) :
    0 ≤ f x := by
  have h := lower_of_second_derivative_upper hab hf hf' hf'' hupper ha hb hx
  have hsquare := mul_nonneg hZ (sq_nonneg (2 * x - a - b))
  nlinarith

#print axioms lower_of_second_derivative_upper
#print axioms nonnegative_of_endpoint_curvature
#print axioms positive_of_concave_endpoints
#print axioms concaveOn_exponentialBudget
#print axioms positive_exponentialBudget_of_endpoints

end ForestUnimodality.AnalyticInterval
