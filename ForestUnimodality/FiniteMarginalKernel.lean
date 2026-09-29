import ForestUnimodality.FiniteMarginalSupport
import ForestUnimodality.FiniteKernelSupportGraphBudget

/-! Actual-forest interpretation of a finite certificate with exact matching
counts. Both the support restriction and the fixed-shift charges are
discharged from a complete finite list of graph-order/rank parameters. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate
open Finset FiniteKernelCurvatureCertificate FiniteMarginalSupport
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem RationalRow.marginalBudget_le_averaged (r : RationalRow ι) (w : IntervalWitness)
    (hr : r.signCheck = true) (N : ℕ) (pairs : List (ℕ × ℕ))
    (hcertificate : ∀ m ≤ N, ∀ j : ℤ, supportCheck pairs m j = true →
      ∀ q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ), 0 ≤ r.toReal.residual m j q)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hN : S.card ≤ N) (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ))
    (k : ℕ) (hmean : hardCoreMean G S z = k) (hpairs : (S.card, k) ∈ pairs)
    (a b : ℚ) (ha : 0 ≤ a) (hlo : (a : ℝ) ≤ z) (hhi : z ≤ (b : ℝ))
    (α β D : ℝ) (rate : ι → ℝ) (bound : ℤ → ℚ)
    (hvarK : hardCoreVariance G S z ≤
      (z / (1 + z) * (1 - z / (1 + z)) + α) * hardCoreAvailableMean G S B z + β)
    (hvarM : hardCoreAvailableVariance G S B z ≤ D * hardCoreAvailableMean G S B z)
    (hlap : ∀ i ∈ r.terms, hardCoreLayerLaplace G S B z (r.retention i) ≤
      Real.exp (-rate i * hardCoreAvailableMean G S B z))
    (hcounts : ∀ j ∈ r.fixedIndices, jointCountBound a b j pairs ≤ bound j) :
    r.graphBudgetWithCounts rate (fun j => (bound j : ℝ)) α β D
      (hardCoreAvailableMean G S B z) ≤
      (r.scale : ℝ) * averagedBinomialKernel G S B z r.wL r.wR r.wC k := by
  apply r.supportBudget_le_averaged w hr N (fun m j => supportCheck pairs m j = true)
    hcertificate G S B hB.subset hB.independent hN hz hq k hmean
    (fun _ _ _ _ hw => actual_support hG hB hz k pairs hpairs hw)
    α β D rate (fun j => (bound j : ℝ)) hvarK hvarM hlap
  intro j hj
  apply (actual_joint_count_bound hG hB hz ha hlo hhi k j pairs hpairs).trans
  exact_mod_cast hcounts j hj

theorem RationalRow.no_weak_valley_of_positive_averaged (r : RationalRow ι)
    (hr : r.signCheck = true) {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : B ⊆ S) (hind : G.IsIndepSet (B : Set V)) (hz : 0 < z) (k : ℕ) (hk : 1 ≤ k)
    (hpositive : 0 < averagedBinomialKernel G S B z r.wL r.wR r.wC k) :
    ¬ (countIndependent G S k ≤ countIndependent G S (k-1) ∧
      countIndependent G S k ≤ countIndependent G S (k+1)) := by
  have hs := of_decide_eq_true hr
  rw [averagedBinomialKernel_eq G S B hB hind hz _ _ _ hk] at hpositive
  exact no_weak_valley_of_positive_tilted_kernel (countIndependent G S)
    hz (partitionFunction_pos G S hz.le)
    (by exact_mod_cast hs.1.2.1) (by exact_mod_cast hs.1.2.2.1)
    (by exact_mod_cast hs.1.2.2.2.1) hk hpositive

#print axioms RationalRow.marginalBudget_le_averaged
#print axioms RationalRow.no_weak_valley_of_positive_averaged
end ForestUnimodality.FiniteKernelRationalCertificate

