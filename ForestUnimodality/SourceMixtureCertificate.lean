import ForestUnimodality.ForestSourceCertificate
import ForestUnimodality.MarkedMixtureVariance

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem heterogeneousMean_common_card (G : SimpleGraph V) (S : Finset V) (z : ℝ) :
    heterogeneousMean G S (fun _ => z) (fun J => (J.card : ℝ)) = hardCoreMean G S z := by
  simp only [heterogeneousMean, FiniteTilt.mean, FiniteTilt.numerator, FiniteTilt.total,
    heterogeneousWeight, prod_const, hardCoreMean, hardCoreMomentNumerator,
    pow_one, partitionFunction, mul_comm]

theorem heterogeneousMean_common_intersection (G : SimpleGraph V) (S B : Finset V) (z : ℝ) :
    heterogeneousMean G S (fun _ => z) (fun J => ((J ∩ B).card : ℝ)) =
      hardCoreOccupiedMass G S B z := by
  rw [hardCoreOccupiedMass_eq_intersection_expectation]
  simp only [heterogeneousMean, FiniteTilt.mean, FiniteTilt.numerator, FiniteTilt.total,
    heterogeneousWeight, prod_const, partitionFunction, mul_comm]

/-- The actual common-activity specialization; B is fixed. -/
theorem hardCoreMarkedVariance_le_of_source_certificate
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hB : G.IsIndepSet (B : Set V)) {lower b z : ℝ} (hlower : 0 < lower)
    (hzlo : lower ≤ z) (hzhi : z ≤ b) (P : SourceRowParameters)
    (hP : P.Admissible) (hvalid : SourceRowValid P lower b) :
    hardCoreMarkedVariance G S B z ≤
      P.A * hardCoreMean G S z + P.C * hardCoreOccupiedMass G S B z := by
  have h := forest_independent_count_variance_of_scalar_certificate G hG S B hB
    (fun _ => z) hlower (fun _ _ => ⟨hzlo, hzhi⟩) P hP hvalid
  simpa only [hardCoreMarkedVariance, heterogeneousMean_common_card,
    heterogeneousMean_common_intersection] using h

/-- Complete forest-to-availability assembly of any valid scalar certificate.
The numerical continuous scalar certificate is the only remaining input. -/
theorem IsMaximumMarginalIndependentOn.available_variance_le_of_source_certificate
    {G : SimpleGraph V} {S B : Finset V} {lower b z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hlower : 0 < lower) (hzlo : lower ≤ z) (hzhi : z ≤ b)
    (P : SourceRowParameters) (hP : P.Admissible) (hA : 0 ≤ P.A)
    (hvalid : SourceRowValid P lower b) :
    hardCoreAvailableVariance G S B z ≤
      (1 + (2*P.A+P.C-1)/(z/(1+z))) * hardCoreAvailableMean G S B z := by
  exact hB.available_variance_le_of_marked hG (hlower.trans_le hzlo) hA
    (hardCoreMarkedVariance_le_of_source_certificate G hG S B hB.independent
      hlower hzlo hzhi P hP hvalid)

#print axioms hardCoreMarkedVariance_le_of_source_certificate
#print axioms IsMaximumMarginalIndependentOn.available_variance_le_of_source_certificate
end ForestUnimodality
