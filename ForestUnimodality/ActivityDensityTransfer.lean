import ForestUnimodality.UnitActivityForestDensity
import ForestUnimodality.NonnegativeSourceData.Case07.Complete
import ForestUnimodality.SourceSelectionCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Density at every positive activity, obtained from the proved unit-density
bound and the actual 0.43 variance certificate along the whole activity path. -/
namespace ForestUnimodality
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem forest_variance_le_43_100_card (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 101 / 100) :
    hardCoreVariance G S z ≤ 43 / 100 * (S.card : ℝ) := by
  have h := NonnegativeSourceData.Case07.forest_variance G hG S (fun _ => z) (fun _ => 1)
    (fun _ _ => ⟨hz, hz1⟩) (fun _ _ => by norm_num)
  have he : markedSum (fun _ : V => (1 : ℝ)) = fun J => (J.card : ℝ) := by
    funext J
    simp [markedSum]
  rw [he, heterogeneousVariance_common_card] at h
  simpa using h

theorem forest_mean_unit_log_transfer (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    hardCoreMean G S 1 + (43 / 100) * (S.card : ℝ) * Real.log z ≤ hardCoreMean G S z := by
  let f : ℝ → ℝ := fun t => hardCoreMean G S t - (43 / 100) * (S.card : ℝ) * Real.log t
  have hd : ∀ t ∈ Icc z 1, HasDerivAt f
      (hardCoreVariance G S t / t - (43 / 100) * (S.card : ℝ) / t) t := by
    intro t ht
    have ht0 : 0 < t := hz.trans_le ht.1
    convert (hasDerivAt_hardCoreMean G S ht0).sub
      ((Real.hasDerivAt_log ht0.ne').const_mul ((43 / 100) * (S.card : ℝ))) using 1
    all_goals rfl
  have hmono : AntitoneOn f (Icc z 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc z 1)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have htc : t ∈ Icc z 1 := interior_subset ht
      have ht0 : 0 < t := hz.trans_le htc.1
      rw [(hd t htc).deriv]
      exact sub_nonpos.mpr (div_le_div_of_nonneg_right
        (forest_variance_le_43_100_card G hG S ht0.le (by linarith [htc.2])) ht0.le)
  have hm := hmono (left_mem_Icc.mpr hz1) (right_mem_Icc.mpr hz1) hz1
  dsimp [f] at hm
  rw [Real.log_one, mul_zero, sub_zero] at hm
  linarith

theorem forest_mean_density_lower_below_one (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (276393 / 1000000 + (43 / 100) * Real.log z) * (S.card : ℝ) ≤ hardCoreMean G S z := by
  have h0 := UnitActivityForestDensity.mean_density_lower G hG S
  have h1 := forest_mean_unit_log_transfer G hG S hz hz1
  nlinarith

theorem forest_mean_density_lower_above_one (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z : ℝ} (hz : 1 ≤ z) :
    276393 / 1000000 * (S.card : ℝ) ≤ hardCoreMean G S z := by
  by_cases hS : S.Nonempty
  · exact (UnitActivityForestDensity.mean_density_lower G hG S).trans
      ((hardCoreMean_strictMonoOn G S hS).monotoneOn (by norm_num)
        (show z ∈ Set.Ioi 0 from by change 0 < z; linarith) hz)
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [hardCoreMean, hardCoreMomentNumerator, independentSubsets_empty_eq_singleton]

/-- A rational lower enclosure for log(min(activity,1)) supplies the density
used by later support-size and tail budgets, with no density assumption. -/
theorem forest_mean_density_lower_of_log_enclosure (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z L ρ : ℝ} (hz : 0 < z) (hL0 : L ≤ 0)
    (hL : L ≤ Real.log z) (hρ : ρ ≤ 276393 / 1000000 + (43 / 100) * L) :
    ρ * (S.card : ℝ) ≤ hardCoreMean G S z := by
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  by_cases hz1 : z ≤ 1
  · apply (mul_le_mul_of_nonneg_right (show ρ ≤ 276393 / 1000000 + (43 / 100) * Real.log z by
      linarith) hn).trans
    exact forest_mean_density_lower_below_one G hG S hz hz1
  · apply (mul_le_mul_of_nonneg_right (show ρ ≤ 276393 / 1000000 by linarith) hn).trans
    exact forest_mean_density_lower_above_one G hG S (le_of_not_ge hz1)

#print axioms forest_variance_le_43_100_card
#print axioms forest_mean_unit_log_transfer
#print axioms forest_mean_density_lower_of_log_enclosure
end ForestUnimodality
