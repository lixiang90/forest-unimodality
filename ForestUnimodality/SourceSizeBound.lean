import ForestUnimodality.MarkedMixtureVariance

/-! Size and variance bounds for the same maximum-marginal independent set.
The mean-density lower bound is explicit and is never inferred from a
different activity or from a maximum-cardinality independent set. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem hardCoreOccupiedMass_le_activity_card (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) {z : ℝ} (hz : 0 < z) :
    hardCoreOccupiedMass G S B z ≤ (z/(1+z))*(B.card : ℝ) := by
  have h := sum_le_sum (s := B) (f := hardCoreVertexMarginal G S z)
    (g := fun _ => z/(1+z)) (fun v hv => hardCoreVertexMarginal_le_activity G S (hBS hv) hz)
  simpa only [hardCoreOccupiedMass, sum_const, nsmul_eq_mul, mul_comm] using h

theorem IsMaximumMarginalIndependentOn.card_le_available_of_density
    {G : SimpleGraph V} {S B : Finset V} {z ρ : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hρ : 0 < ρ) (hρq : ρ ≤ z/(1+z))
    (hdensity : ρ*(S.card : ℝ) ≤ hardCoreMean G S z) :
    (B.card : ℝ) ≤ (2*(z/(1+z))/ρ-1)*hardCoreAvailableMean G S B z := by
  let q := z/(1+z)
  have hq : 0 < q := by dsimp [q]; positivity
  have hcomp := hardCoreOccupiedMass_le_activity_card G S (S \ B) sdiff_subset hz
  have hcard : ((S \ B).card : ℝ) = (S.card : ℝ)-(B.card : ℝ) := by
    rw [card_sdiff_of_subset hB.subset, Nat.cast_sub (card_le_card hB.subset)]
  rw [hcard] at hcomp
  have hadd := hardCoreOccupiedMass_add_complement G S B hB.subset z
  have hmass := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hhalf := hB.half_mean hG.isBipartite
  have h1 := mul_le_mul_of_nonneg_left hcomp hρ.le
  have h2 := mul_le_mul_of_nonneg_left hdensity hq.le
  have h3 := mul_le_mul_of_nonneg_left hhalf (sub_nonneg.mpr hρq)
  have hclear : ρ*q*(B.card : ℝ) ≤
      q*(2*q-ρ)*hardCoreAvailableMean G S B z := by
    dsimp [q] at h1 h2 h3 ⊢
    nlinarith
  apply (mul_le_mul_iff_right₀ (mul_pos hρ hq)).mp
  calc
    ρ*q*(B.card : ℝ) ≤ q*(2*q-ρ)*hardCoreAvailableMean G S B z := hclear
    _ = ρ*q*((2*(z/(1+z))/ρ-1)*hardCoreAvailableMean G S B z) := by
      dsimp [q]
      field_simp

/-- The affine support-size source bound gives the original stage-500
coefficient, before taking the maximum over an activity interval. -/
theorem IsMaximumMarginalIndependentOn.available_variance_le_affine_density
    {G : SimpleGraph V} {S B : Finset V} {z ρ A C : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0 < z) (hρ : 0 < ρ) (hρq : ρ ≤ z/(1+z)) (hA : 0 ≤ A)
    (hdensity : ρ*(S.card : ℝ) ≤ hardCoreMean G S z)
    (hsource : hardCoreMarkedVariance G S B z ≤
      A*(B.card : ℝ)+C*hardCoreOccupiedMass G S B z) :
    hardCoreAvailableVariance G S B z ≤
      (1+(2*A/ρ+C-1)/(z/(1+z))-A/(z/(1+z))^2)*hardCoreAvailableMean G S B z := by
  have hb := mul_le_mul_of_nonneg_left (hB.card_le_available_of_density hG hz hρ hρq hdensity) hA
  have hv := hardCoreMarkedVariance_eq_available_variance G S B hB.subset hB.independent hz
  have hm := hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hq : 0 < z/(1+z) := by positivity
  have hbound : (z/(1+z))^2*hardCoreAvailableVariance G S B z ≤
      (A*(2*(z/(1+z))/ρ-1)+C*(z/(1+z))-(z/(1+z))*(1-z/(1+z)))*
        hardCoreAvailableMean G S B z := by
    rw [hm] at hsource
    nlinarith
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hq)).mp
  calc
    (z/(1+z))^2*hardCoreAvailableVariance G S B z ≤ _ := hbound
    _ = (z/(1+z))^2*((1+(2*A/ρ+C-1)/(z/(1+z))-A/(z/(1+z))^2)*
        hardCoreAvailableMean G S B z) := by
      field_simp
      ring

#print axioms IsMaximumMarginalIndependentOn.card_le_available_of_density
#print axioms IsMaximumMarginalIndependentOn.available_variance_le_affine_density
end ForestUnimodality
