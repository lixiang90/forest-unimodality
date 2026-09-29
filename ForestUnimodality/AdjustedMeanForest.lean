import ForestUnimodality.PenultimateFanConstruction

/-! The full activity-two adjusted-mean inequality for every finite forest.
Strong induction quantifies over all vertex types in the same universe,
so genuinely fresh path contexts satisfy the induction hypothesis. -/
namespace ForestUnimodality
universe u
variable {V : Type u} [DecidableEq V]

theorem adjustedMeanPotential_nonneg_of_isAcyclic
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    0 ≤ adjustedMeanPotential G S (independenceNumberOn G S) := by
  have hmain : ∀ n : ℕ, ∀ (W : Type u) [DecidableEq W]
      (F : SimpleGraph W) (A : Finset W), A.card = n → F.IsAcyclic →
      0 ≤ adjustedMeanPotential F A (independenceNumberOn F A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W inst F A hcard hF
      by_contra! hbad
      have hsmaller : GlobalSmallerMeanHyp.{u} A.card := by
        intro U instU Q D hD hQ
        exact ih D.card (by omega) U Q D rfl hQ
      have hconn := induce_connected_of_minimal_adjustedMean_neg F A hbad
        (fun D _ hD => hsmaller W F D hD hF)
      obtain ⟨r, v, c, H, T, hseed⟩ :=
        exists_penultimate_seed_of_minimal_neg F hF A hsmaller hbad
      have hpos := hseed.adjustedMean_pos hF hconn hsmaller hbad.le
      exact (not_lt_of_ge hbad.le) hpos
  exact hmain S.card V G S rfl hG

/-- Input M, now proved for all finite forests, including empty and
disconnected forests and arbitrarily many branching vertices. -/
theorem forest_activity_two_mean_lower (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) :
    (independenceNumberOn G S : ℝ) + 29 * (S.card : ℝ) / 60 ≤ 3 * hardCoreMean G S 2 := by
  have h := adjustedMeanPotential_nonneg_of_isAcyclic G hG S
  unfold adjustedMeanPotential at h
  linarith

theorem IsMaximumIndependentOn.adjustedMean_nonneg_of_isAcyclic
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) : 0 ≤ adjustedMeanPotential G S I.card := by
  rw [hI.card_eq_independenceNumberOn]
  exact adjustedMeanPotential_nonneg_of_isAcyclic G hG S

#print axioms adjustedMeanPotential_nonneg_of_isAcyclic
#print axioms forest_activity_two_mean_lower
#print axioms IsMaximumIndependentOn.adjustedMean_nonneg_of_isAcyclic
end ForestUnimodality
