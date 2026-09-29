import ForestUnimodality.AffineSourceLaplaceRate

/-! Order-theoretic transfer of a proved Laplace bound.  These results quantify
over whole real parameter intervals and never unfold a numerical flow table. -/
namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem hardCoreLayerLaplace_rate_mono (G : SimpleGraph V) (S B : Finset V)
    {z t u r R : ℝ} (hz : 0 ≤ z) (ht : 0 ≤ t) (htu : t ≤ u) (hr : r ≤ R)
    (h : hardCoreLayerLaplace G S B z u ≤
      Real.exp (-R * hardCoreAvailableMean G S B z)) :
    hardCoreLayerLaplace G S B z t ≤
      Real.exp (-r * hardCoreAvailableMean G S B z) := by
  apply (hardCoreLayerLaplace_mono G S B hz ht htu).trans
  apply h.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hr)
    (hardCoreAvailableMean_nonneg G S B hz)

/-- A stronger density hypothesis, smaller activity interval, smaller retention
and weaker rate all preserve a certified bound, independently of its proof. -/
theorem hardCoreLayerLaplace_restrict (G : SimpleGraph V) (S B : Finset V)
    {z a b A D ρ σ t u r R : ℝ}
    (hz : 0 ≤ z) (ht : 0 ≤ t) (htu : t ≤ u) (hr : r ≤ R)
    (ha : A ≤ a) (hb : b ≤ D) (hρ : σ ≤ ρ)
    (hsource : z/(1+z) ∈ Set.Icc A D →
      σ*(S.card:ℝ) ≤ hardCoreMean G S z →
      hardCoreLayerLaplace G S B z u ≤
        Real.exp (-R * hardCoreAvailableMean G S B z))
    (hq : z/(1+z) ∈ Set.Icc a b)
    (hdensity : ρ*(S.card:ℝ) ≤ hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z t ≤
      Real.exp (-r * hardCoreAvailableMean G S B z) := by
  apply hardCoreLayerLaplace_rate_mono G S B hz ht htu hr
  exact hsource ⟨ha.trans hq.1, hq.2.trans hb⟩
    ((mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg S.card)).trans hdensity)

#print axioms hardCoreLayerLaplace_rate_mono
#print axioms hardCoreLayerLaplace_restrict
end ForestUnimodality
