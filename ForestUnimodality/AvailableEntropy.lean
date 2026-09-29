import ForestUnimodality.MarkedMixtureVariance
import ForestUnimodality.LaplaceRateInterval
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The size-biased logarithmic moment of the original available-count law.
Zero available count is included using 0*log 0=0. -/
namespace ForestUnimodality
open Finset

theorem mul_log_le_quadratic {x m : ℝ} (hx : 0 ≤ x) (hm : 0 < m) :
    x*Real.log x ≤ x*Real.log m+x*(x-m)/m := by
  by_cases hx0 : x=0
  · simp [hx0]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hxp hm)
    rw [Real.log_div hx0 (ne_of_gt hm)] at hlog
    have h := mul_le_mul_of_nonneg_left hlog hx
    have he : x*(x/m-1)=x*(x-m)/m := by field_simp
    rw [mul_sub, he] at h
    linarith

variable {V : Type*} [DecidableEq V]

theorem hardCoreAvailable_entropy_le (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z : ℝ} (hz : 0 ≤ z)
    (hm : 0 < hardCoreAvailableMean G S B z) :
    hardCoreLayerExpectation G S B z (fun _ M => (M : ℝ)*Real.log M) ≤
      hardCoreAvailableMean G S B z * Real.log (hardCoreAvailableMean G S B z)+
        hardCoreAvailableVariance G S B z/hardCoreAvailableMean G S B z := by
  let m := hardCoreAvailableMean G S B z
  have hs : hardCoreLayerExpectation G S B z (fun _ M => (M : ℝ)*Real.log M) ≤
      hardCoreLayerExpectation G S B z (fun _ M => (M : ℝ)*Real.log m+(M : ℝ)*((M : ℝ)-m)/m) := by
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro M _
    exact mul_le_mul_of_nonneg_left (mul_log_le_quadratic (Nat.cast_nonneg M) hm)
      (hardCoreLayerWeight_nonneg G S B hz j M)
  have hp (j M : ℕ) : hardCoreLayerWeight G S B z j M *
      ((M : ℝ)*Real.log m+(M : ℝ)*((M : ℝ)-m)/m) =
        (hardCoreLayerWeight G S B z j M*(M : ℝ))*Real.log m +
        ((hardCoreLayerWeight G S B z j M*(M : ℝ)^2)-m*(hardCoreLayerWeight G S B z j M*(M : ℝ)))/m := by
    ring
  have he : hardCoreLayerExpectation G S B z (fun _ M => (M : ℝ)*Real.log m+(M : ℝ)*((M : ℝ)-m)/m) =
      m*Real.log m+hardCoreAvailableVariance G S B z/m := by
    simp only [hardCoreLayerExpectation, hp, sum_add_distrib, ← sum_mul, ← sum_div,
      sum_sub_distrib, ← mul_sum]
    change m*Real.log m+(hardCoreLayerExpectation G S B z (fun _ M => (M : ℝ)^2)-m*m)/m = _
    rw [hardCoreAvailable_second_moment G S B hBS hB hz]
    dsimp only [m]
    ring
  exact hs.trans_eq he

theorem hardCoreAvailable_entropy_le_of_variance (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z D : ℝ} (hz : 0 ≤ z)
    (hm : 0 < hardCoreAvailableMean G S B z)
    (hvar : hardCoreAvailableVariance G S B z ≤ D*hardCoreAvailableMean G S B z) :
    hardCoreLayerExpectation G S B z (fun _ M => (M : ℝ)*Real.log M) ≤
      hardCoreAvailableMean G S B z * Real.log (hardCoreAvailableMean G S B z)+D := by
  have hv := (div_le_iff₀ hm).mpr hvar
  exact (hardCoreAvailable_entropy_le G S B hBS hB hz hm).trans (add_le_add le_rfl hv)

#print axioms mul_log_le_quadratic
#print axioms hardCoreAvailable_entropy_le
end ForestUnimodality
