import ForestUnimodality.BinomialKernel
import ForestUnimodality.InitialForestGrowth
import ForestUnimodality.ForestMatchingRank
import ForestUnimodality.HardCoreActivityGrowth

/-! Forest assembly with the initial and terminal coefficient inequalities
proved, rather than assumed. The adjusted mean inequality M and positivity
of the actual central mixed kernel remain explicit analytic obligations. -/

namespace ForestUnimodality

open Finset
variable {V : Type*} [DecidableEq V]

/-- Every necessary positive central rank has its unique actual activity.
The upper endpoint is strict. Empty vertex sets have no such rank. -/
theorem IsMaximumIndependentOn.existsUnique_central_activity_of_adjusted_mean
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic)
    (hM : (I.card : ℝ) + (29 / 60 : ℝ) * S.card ≤ 3 * hardCoreMean G S 2)
    (k : ℕ) (hkL : (S.card + 3) / 4 ≤ k)
    (hkU : k < (S.card + 2 * I.card) / 6 + 1) (hkpos : 1 ≤ k) :
    ∃! z : ℝ, z ∈ Set.Ico (1 / 3) (9 / 4) ∧ hardCoreMean G S z = k := by
  have hcard : I.card ≤ S.card := card_le_card hI.subset
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hlo : (S.card : ℝ) / 4 ≤ (k : ℝ) := by
    have h : (S.card : ℝ) ≤ 4 * (k : ℝ) := by
      exact_mod_cast (show S.card ≤ 4 * k by omega)
    linarith
  have hhi : (k : ℝ) ≤ ((S.card : ℝ) + 2 * (I.card : ℝ)) / 6 := by
    have h : 6 * (k : ℝ) ≤ (S.card : ℝ) + 2 * (I.card : ℝ) := by
      exact_mod_cast (show 6 * k ≤ S.card + 2 * I.card by omega)
    linarith
  obtain ⟨z, ⟨hz, hmean⟩, huniq⟩ :=
    hI.existsUnique_activity_window_of_adjusted_mean hG hS hM k hlo hhi
  have hzlt : z < (9 / 4 : ℝ) := by
    rcases lt_or_eq_of_le hz.2 with hlt | heq
    · exact hlt
    · have hupper := hI.hardCoreMean_nine_quarters_gt_rank_of_adjusted_mean hG hS hM
      rw [heq] at hmean
      linarith
  refine ⟨z, ⟨⟨hz.1, hzlt⟩, hmean⟩, ?_⟩
  intro w hw
  exact huniq w ⟨⟨hw.1.1, hw.1.2.le⟩, hw.2⟩

/-- With the forest E window supplied by proved structure, only positivity
of an actual nonnegative mixed kernel remains in this assembly interface. -/
theorem IsMaximumIndependentOn.countIndependent_unimodal_of_central_kernel
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic)
    (hpositive : ∀ k, (S.card + 3) / 4 ≤ k →
      k < (S.card + 2 * I.card) / 6 + 1 → 1 ≤ k →
      ∃ (B : Finset V) (z wL wR wC : ℝ),
        B ⊆ S ∧ G.IsIndepSet (B : Set V) ∧ 0 < z ∧
        0 ≤ wL ∧ 0 ≤ wR ∧ 0 ≤ wC ∧
        0 < averagedBinomialKernel G S B z wL wR wC k) :
    WeaklyUnimodal (countIndependent G S) := by
  apply countIndependent_unimodal_of_binomial_kernel_bounds G S
    ((S.card + 3) / 4) ((S.card + 2 * I.card) / 6 + 1)
  · exact countIndependent_le_succ_of_quarter G hG S
  · exact hI.countIndependent_succ_le_of_matching_tail hG
  · exact hpositive

/-- The remaining two analytic conditions are stated on the real graph:
M at activity two, and central kernel positivity at its unique mean-matching
activity. The mixture set B may depend on the activity and need not be the
maximum-cardinality set I. No E or activity-bracketing assumption remains. -/
theorem IsMaximumIndependentOn.countIndependent_unimodal_of_adjusted_mean_kernel
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic)
    (hM : (I.card : ℝ) + (29 / 60 : ℝ) * S.card ≤ 3 * hardCoreMean G S 2)
    (hpositive : ∀ k, (S.card + 3) / 4 ≤ k →
      k < (S.card + 2 * I.card) / 6 + 1 → 1 ≤ k →
      ∀ z : ℝ, z ∈ Set.Ico (1 / 3) (9 / 4) → hardCoreMean G S z = k →
      ∃ (B : Finset V) (wL wR wC : ℝ),
        B ⊆ S ∧ G.IsIndepSet (B : Set V) ∧
        0 ≤ wL ∧ 0 ≤ wR ∧ 0 ≤ wC ∧
        0 < averagedBinomialKernel G S B z wL wR wC k) :
    WeaklyUnimodal (countIndependent G S) := by
  apply hI.countIndependent_unimodal_of_central_kernel hG
  intro k hkL hkU hkpos
  obtain ⟨z, ⟨hz, hmean⟩, _⟩ :=
    hI.existsUnique_central_activity_of_adjusted_mean hG hM k hkL hkU hkpos
  obtain ⟨B, wL, wR, wC, hBS, hB, hwL, hwR, hwC, hpos⟩ :=
    hpositive k hkL hkU hkpos z hz hmean
  exact ⟨B, z, wL, wR, wC, hBS, hB, lt_of_lt_of_le (by norm_num) hz.1,
    hwL, hwR, hwC, hpos⟩

#print axioms IsMaximumIndependentOn.existsUnique_central_activity_of_adjusted_mean
#print axioms IsMaximumIndependentOn.countIndependent_unimodal_of_central_kernel
#print axioms IsMaximumIndependentOn.countIndependent_unimodal_of_adjusted_mean_kernel

end ForestUnimodality
