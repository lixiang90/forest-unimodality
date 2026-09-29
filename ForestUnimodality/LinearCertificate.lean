import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Soundness of finite linear upper-bound certificates.

These are original, generic algebraic lemmas. They do not establish that any
particular combinatorial row holds for forests, nor verify stored certificates.
An equality multiplier may have either sign; inequality multipliers are nonnegative.
-/

namespace ForestUnimodality.LinearCertificate

open Finset
open scoped BigOperators

variable {ι κ γ : Type*}

/-- A finite linear functional, with its variable support made explicit. -/
def linear (vars : Finset ι) (c x : ι → ℝ) : ℝ :=
  ∑ i ∈ vars, c i * x i

/-- Interchanging the two finite sums in a linear combination of rows. -/
theorem linear_combination (vars : Finset ι) (rows : Finset κ)
    (a : κ → ι → ℝ) (e r x : ι → ℝ) (w : κ → ℝ) (η : ℝ) :
    linear vars (fun i => η * e i + (∑ j ∈ rows, w j * a j i) + r i) x =
      η * linear vars e x + (∑ j ∈ rows, w j * linear vars (a j) x) +
        linear vars r x := by
  simp only [linear, add_mul, sum_add_distrib, mul_sum, sum_mul, mul_assoc]
  rw [sum_comm]

/-- Weak duality with an explicitly bounded residual linear functional. -/
theorem affine_upper_of_residual_bound
    (vars : Finset ι) (rows : Finset κ)
    (a : κ → ι → ℝ) (b w : κ → ℝ) (c e r x : ι → ℝ)
    (constant η equalityValue residualBound : ℝ)
    (hx : ∀ i ∈ vars, 0 ≤ x i)
    (hw : ∀ j ∈ rows, 0 ≤ w j)
    (hrows : ∀ j ∈ rows, linear vars (a j) x ≤ b j)
    (hequality : linear vars e x = equalityValue)
    (hcoefficient : ∀ i ∈ vars,
      c i ≤ η * e i + (∑ j ∈ rows, w j * a j i) + r i)
    (hresidual : linear vars r x ≤ residualBound) :
    constant + linear vars c x ≤
      constant + η * equalityValue + (∑ j ∈ rows, w j * b j) + residualBound := by
  have hpoint : linear vars c x ≤
      linear vars (fun i => η * e i + (∑ j ∈ rows, w j * a j i) + r i) x := by
    exact sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hcoefficient i hi) (hx i hi)
  have hweighted : (∑ j ∈ rows, w j * linear vars (a j) x) ≤
      ∑ j ∈ rows, w j * b j := by
    exact sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hrows j hj) (hw j hj)
  rw [linear_combination, hequality] at hpoint
  linarith

/-- Nonnegative per-layer residual caps, together with bounds on layer mass,
control the residual even when individual residual coefficients are negative. -/
theorem residual_upper_by_layers [DecidableEq γ]
    (vars : Finset ι) (layers : Finset γ) (layer : ι → γ)
    (r x : ι → ℝ) (cap mass : γ → ℝ)
    (hcover : ∀ i ∈ vars, layer i ∈ layers)
    (hx : ∀ i ∈ vars, 0 ≤ x i)
    (hcap : ∀ j ∈ layers, 0 ≤ cap j)
    (hresidual : ∀ i ∈ vars, r i ≤ cap (layer i))
    (hmass : ∀ j ∈ layers, (∑ i ∈ vars with layer i = j, x i) ≤ mass j) :
    linear vars r x ≤ ∑ j ∈ layers, cap j * mass j := by
  unfold linear
  rw [← sum_fiberwise_of_maps_to hcover (fun i => r i * x i)]
  apply sum_le_sum
  intro j hj
  calc
    (∑ i ∈ vars with layer i = j, r i * x i) ≤
        ∑ i ∈ vars with layer i = j, cap j * x i := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hiv, hij⟩ := mem_filter.mp hi
      exact mul_le_mul_of_nonneg_right (hij ▸ hresidual i hiv) (hx i hiv)
    _ = cap j * (∑ i ∈ vars with layer i = j, x i) := (mul_sum _ _ _).symm
    _ ≤ cap j * mass j := mul_le_mul_of_nonneg_left (hmass j hj) (hcap j hj)

/-- The maximum of zero and a finite collection of residual coefficients.
The inserted zero also handles empty layers. -/
noncomputable def positiveMax (s : Finset ι) (r : ι → ℝ) : ℝ := by
  classical
  exact (insert 0 (s.image r)).max' (by simp)

theorem positiveMax_nonneg (s : Finset ι) (r : ι → ℝ) :
    0 ≤ positiveMax s r := by
  classical
  exact Finset.le_max' _ 0 (by simp)

theorem le_positiveMax (s : Finset ι) (r : ι → ℝ) {i : ι} (hi : i ∈ s) :
    r i ≤ positiveMax s r := by
  classical
  exact Finset.le_max' _ (r i) (mem_insert_of_mem (mem_image_of_mem r hi))

/-- The residual as computed by subtracting the selected weighted rows and
the unrestricted equality multiplier from the target coefficients. -/
def residual (rows : Finset κ) (a : κ → ι → ℝ) (w : κ → ℝ)
    (c e : ι → ℝ) (η : ℝ) (i : ι) : ℝ :=
  c i - η * e i - ∑ j ∈ rows, w j * a j i

/-- Soundness of the full layer-maximum certificate used in exact finite LP
verification. The input rows and the layer mass inequalities remain explicit
mathematical hypotheses; no forest-specific claim is hidden in this theorem. -/
theorem affine_upper_by_layer_maxima [DecidableEq γ]
    (vars : Finset ι) (rows : Finset κ) (layers : Finset γ) (layer : ι → γ)
    (a : κ → ι → ℝ) (b w : κ → ℝ) (c e x : ι → ℝ)
    (constant η equalityValue : ℝ) (mass : γ → ℝ)
    (hcover : ∀ i ∈ vars, layer i ∈ layers)
    (hx : ∀ i ∈ vars, 0 ≤ x i)
    (hw : ∀ j ∈ rows, 0 ≤ w j)
    (hrows : ∀ j ∈ rows, linear vars (a j) x ≤ b j)
    (hequality : linear vars e x = equalityValue)
    (hmass : ∀ j ∈ layers, (∑ i ∈ vars with layer i = j, x i) ≤ mass j) :
    constant + linear vars c x ≤
      constant + η * equalityValue + (∑ j ∈ rows, w j * b j) +
        ∑ j ∈ layers,
          positiveMax (vars.filter fun i => layer i = j) (residual rows a w c e η) *
            mass j := by
  apply affine_upper_of_residual_bound vars rows a b w c e
    (residual rows a w c e η) x constant η equalityValue _ hx hw hrows hequality
  · intro i _
    unfold residual
    linarith
  · apply residual_upper_by_layers vars layers layer
      (residual rows a w c e η) x
      (fun j => positiveMax (vars.filter fun i => layer i = j)
        (residual rows a w c e η)) mass hcover hx
    · intro j _
      exact positiveMax_nonneg _ _
    · intro i hi
      exact le_positiveMax _ _ (mem_filter.mpr ⟨hi, rfl⟩)
    · exact hmass

/-- Clearing a common positive denominator during certificate checking is
sound: divide the resulting affine upper bound by the same scale. -/
theorem affine_upper_of_positive_scaling
    (vars : Finset ι) (c x : ι → ℝ) (constant scale bound : ℝ)
    (hscale : 0 < scale)
    (hbound : scale * constant + linear vars (fun i => scale * c i) x ≤ bound) :
    constant + linear vars c x ≤ bound / scale := by
  have hlinear : linear vars (fun i => scale * c i) x =
      scale * linear vars c x := by
    simp only [linear, mul_sum, mul_assoc]
  rw [hlinear] at hbound
  apply (le_div_iff₀ hscale).mpr
  nlinarith

#print axioms affine_upper_of_residual_bound
#print axioms residual_upper_by_layers
#print axioms affine_upper_by_layer_maxima
#print axioms affine_upper_of_positive_scaling

end ForestUnimodality.LinearCertificate
