import ForestUnimodality.SpiderClosure
import ForestUnimodality.ShortLegGraphs

/-! Exhaustive exclusion of an actual spider in the minimal-counterexample
induction for the forest adjusted-mean bound. Large branch counts use a
proved infinite inequality; small counts use all 203 short same-parity
length multisets, after a proved parameter conversion. -/
namespace ForestUnimodality
open Finset
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem IsSpiderOn.adjustedMean_pos_of_small_short_same_parity
    {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hm : s.card ≤ 3)
    (hshort : ∀ i ∈ s, length i ≤ 13) (odd : Bool)
    (hparity : ∀ i ∈ s, length i % 2 = if odd then 1 else 0) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  let index := fun i => if odd then length i / 2 else (length i - 2) / 2
  let fan := s.toList.map index
  have hlen : fan.length ≤ 3 := by simpa [fan] using hm
  have hbound : ∀ k ∈ fan, k < ShortLegData.legBound odd := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    have hiS := mem_toList.mp hi
    have hp := h.length_pos i hiS
    have hs := hshort i hiS
    have hpa := hparity i hiS
    cases odd <;> dsimp [ShortLegData.legBound, index] at hpa ⊢ <;> omega
  have heq : ShortLegData.legsOf odd fan = s.toList.map length := by
    simp only [ShortLegData.legsOf, fan, List.map_map]
    apply List.map_congr_left
    intro i hi
    have hiS := mem_toList.mp hi
    have hp := h.length_pos i hiS
    have hpa := hparity i hiS
    cases odd <;> dsimp [index, ShortLegData.legLength] at hpa ⊢ <;> omega
  have hnum := ShortLegData.small_spider_positive odd fan hlen hbound
  rw [heq] at hnum
  exact ShortLegData.spider_graph_positive_of_numerator h hnum

/-- An actual spider cannot be a minimal nonpositive counterexample once
every strictly smaller induced forest has nonnegative potential. No bound
on the original number or lengths of legs is assumed. -/
theorem IsSpiderOn.not_minimal_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) (hI : IsMaximumIndependentOn G S I)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card) :
    ¬ adjustedMeanPotential G S I.card ≤ 0 := by
  intro hbad
  have hm := h.card_le_three_of_minimal_adjustedMean_nonpos hI hbad hsmaller
  have hshort := fun i hi => h.leg_length_le_thirteen_of_minimal_adjustedMean_nonpos
    hI hbad hsmaller (i := i) hi
  have hpar := h.same_parity_of_minimal_adjustedMean_nonpos hI hbad hsmaller
  have hpos : 0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
    by_cases hne : s.Nonempty
    · obtain ⟨i, hi⟩ := hne
      have hmod := Nat.mod_lt (length i) (by decide : 0 < 2)
      by_cases he : length i % 2 = 0
      · apply h.adjustedMean_pos_of_small_short_same_parity hm hshort false
        intro j hj
        exact (hpar j hj i hi).trans he
      · have ho : length i % 2 = 1 := by omega
        apply h.adjustedMean_pos_of_small_short_same_parity hm hshort true
        intro j hj
        exact (hpar j hj i hi).trans ho
    · apply h.adjustedMean_pos_of_small_short_same_parity hm hshort false
      intro i hi
      exact (hne ⟨i, hi⟩).elim
  rw [← hI.card_eq_independenceNumberOn] at hpos
  exact (not_lt_of_ge hbad) hpos

#print axioms IsSpiderOn.adjustedMean_pos_of_small_short_same_parity
#print axioms IsSpiderOn.not_minimal_adjustedMean_nonpos
end ForestUnimodality
