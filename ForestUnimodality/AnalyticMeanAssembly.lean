import ForestUnimodality.AnalyticForestAssembly
import ForestUnimodality.AdjustedMeanForest

/-! The real central activity window and the unimodality assembly now use
the proved all-order forest mean bound. Only actual kernel positivity is
left as an analytic premise. -/
namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem IsMaximumIndependentOn.activity_two_mean_lower
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) :
    (I.card : ℝ) + (29 / 60 : ℝ) * S.card ≤ 3 * hardCoreMean G S 2 := by
  have h := hI.adjustedMean_nonneg_of_isAcyclic hG
  unfold adjustedMeanPotential at h
  linarith

theorem IsMaximumIndependentOn.existsUnique_central_activity
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (k : ℕ) (hkL : (S.card + 3) / 4 ≤ k)
    (hkU : k < (S.card + 2 * I.card) / 6 + 1) (hkpos : 1 ≤ k) :
    ∃! z : ℝ, z ∈ Set.Ico (1 / 3) (9 / 4) ∧ hardCoreMean G S z = k :=
  hI.existsUnique_central_activity_of_adjusted_mean hG (hI.activity_two_mean_lower hG)
    k hkL hkU hkpos

theorem IsMaximumIndependentOn.countIndependent_unimodal_of_mean_matched_kernel
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic)
    (hpositive : ∀ k, (S.card + 3) / 4 ≤ k →
      k < (S.card + 2 * I.card) / 6 + 1 → 1 ≤ k →
      ∀ z : ℝ, z ∈ Set.Ico (1 / 3) (9 / 4) → hardCoreMean G S z = k →
      ∃ (B : Finset V) (wL wR wC : ℝ),
        B ⊆ S ∧ G.IsIndepSet (B : Set V) ∧
        0 ≤ wL ∧ 0 ≤ wR ∧ 0 ≤ wC ∧
        0 < averagedBinomialKernel G S B z wL wR wC k) :
    WeaklyUnimodal (countIndependent G S) :=
  hI.countIndependent_unimodal_of_adjusted_mean_kernel hG (hI.activity_two_mean_lower hG) hpositive

#print axioms IsMaximumIndependentOn.activity_two_mean_lower
#print axioms IsMaximumIndependentOn.existsUnique_central_activity
#print axioms IsMaximumIndependentOn.countIndependent_unimodal_of_mean_matched_kernel
end ForestUnimodality
