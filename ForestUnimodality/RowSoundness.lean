import ForestUnimodality.RowSoundnessBasic
import ForestUnimodality.RowSoundnessAdvanced

/-! Exhaustive graph soundness for the executable row language. Conditional
rows use a supplied source-step premise; validity alone does not prove it. -/
namespace ForestUnimodality
namespace FiniteRows
variable {V : Type*} [DecidableEq V]

theorem rowHolds_of_valid {G : SimpleGraph V} {S I : Finset V}
    (hmin : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic)
    (k : ℕ) (hk : 1 ≤ k) (kind : Kind) (row : Row)
    (hvalid : Valid S.card I.card k kind row)
    (hconditional : kind = .conditional →
      countIndependent G S k ≤ countIndependent G S (k - 1)) : RowHolds G S I row := by
  have hI := hmin.1
  have hv : S.card - I.card = (S \ I).card :=
    (Finset.card_sdiff_of_subset hI.subset).symm
  cases row with
  | count r =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_count hI r (by omega) hvalid.2
  | path r => exact rowHolds_path hI hG r
  | privateRow r h =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_private hI hG r h hvalid.1 hvalid.2.1
  | hall r l =>
    simp only [Valid, hv] at hvalid
    have hrv : r < (S \ I).card :=
      lt_of_lt_of_le hvalid.2.1 (min_le_left _ _)
    exact rowHolds_hall hI hG r l hrv
  | tail r h =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_tail hI hG r h hvalid.1 hvalid.2.1
  | releaseUpper r h =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_releaseUpper hmin hG r h hvalid.1 hvalid.2.1
  | tailUpper r h =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_tailUpper hmin hG r h hvalid.1 hvalid.2.1
  | mean r =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_mean hI hG r hvalid.1 hvalid.2
  | unionRow r =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_union hI r (by omega) hvalid.2
  | edgeLower r =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_edgeLower hI r hvalid.1 hvalid.2
  | edgeUpper r =>
    simp only [Valid, hv] at hvalid
    exact rowHolds_edgeUpper hmin hG r hvalid.1 hvalid.2
  | assumptionRow r =>
    obtain ⟨hkind, hrk⟩ := hvalid
    subst r
    apply (hI.assumptionRow_iff k hk).mpr
    have hcast : (countIndependent G S k : ℝ) ≤
        (countIndependent G S (k - 1) : ℝ) := by
      exact_mod_cast hconditional hkind
    exact sub_nonpos.mpr hcast

#print axioms rowHolds_of_valid
end FiniteRows
end ForestUnimodality
