import ForestUnimodality.ForestMatching
import ForestUnimodality.MatchingExclusion
import ForestUnimodality.HereditaryRank
import ForestUnimodality.BlockRankEncoding
import ForestUnimodality.SmallIndependence
import Mathlib.Data.List.Nodup

/-! A saturating matching partitions the actual graph vertices into disjoint
edge blocks and singleton blocks. The order of these blocks realizes exactly
the two-color and one-color reference product. -/

namespace ForestUnimodality

open Finset
open HereditaryRank

variable {V : Type*} [DecidableEq V]

/-- An actual partition into edge and singleton blocks, with no arbitrary
family-size or normalized-rank assumption. -/
theorem IsMaximumIndependentOn.exists_matching_blocks
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) :
    ∃ Bs : List (Finset V),
      Bs.Pairwise Disjoint ∧
      (∀ B ∈ Bs, ∀ u ∈ B, ∀ w ∈ B, u ≠ w → G.Adj u w) ∧
      (∀ x, x ∈ S ↔ ∃ B ∈ Bs, x ∈ B) ∧
      Bs.map Finset.card = matchingColors I.card (S \ I).card := by
  classical
  obtain ⟨f, hf, hadj⟩ := hI.exists_injective_adj_of_isAcyclic hG
  let Y := S \ I
  let pair : (↑Y : Set V) → Finset V := fun y => {y.val, (f y).val}
  let R : Finset V := univ.image (fun y : (↑Y : Set V) => (f y).val)
  let L : Finset V := I \ R
  let A : List (Finset V) := (univ : Finset (↑Y : Set V)).toList.map pair
  let B : List (Finset V) := L.toList.map (fun x => {x})
  have hyI (y : (↑Y : Set V)) : y.val ∉ I := (mem_sdiff.mp y.property).2
  have hfyI (y : (↑Y : Set V)) : (f y).val ∈ I := (f y).property
  have hne (y : (↑Y : Set V)) : y.val ≠ (f y).val := by
    intro h
    exact hyI y (h ▸ hfyI y)
  have hpaircard (y : (↑Y : Set V)) : (pair y).card = 2 := by
    exact card_pair (hne y)
  have hRsub : R ⊆ I := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact hfyI y
  have hRcard : R.card = Y.card := by
    have hinj : Function.Injective (fun y : (↑Y : Set V) => (f y).val) := by
      intro y z h
      exact hf (Subtype.ext h)
    rw [show R = univ.image (fun y : (↑Y : Set V) => (f y).val) from rfl,
      card_image_of_injective _ hinj, card_univ]
    exact Fintype.card_coe Y
  have hLcard : L.card = I.card - Y.card := by
    rw [show L = I \ R from rfl, card_sdiff_of_subset hRsub, hRcard]
  have hpairdis (y z : (↑Y : Set V)) (hyz : y ≠ z) : Disjoint (pair y) (pair z) := by
    apply disjoint_left.mpr
    intro x hx hy
    simp only [pair, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | hx <;> rcases hy with hy | hy
    · exact hyz (Subtype.ext hy)
    · exact hyI y (hy ▸ hfyI z)
    · exact hyI z (hy.symm ▸ hx ▸ hfyI y)
    · apply hyz
      apply hf
      apply Subtype.ext
      exact hx.symm.trans hy
  have hAdis : A.Pairwise Disjoint := by
    rw [show A = (univ : Finset (↑Y : Set V)).toList.map pair from rfl, List.pairwise_map]
    exact (nodup_toList _).pairwise_of_forall_ne (fun y _ z _ hyz => hpairdis y z hyz)
  have hBdis : B.Pairwise Disjoint := by
    rw [show B = L.toList.map (fun x => {x}) from rfl, List.pairwise_map]
    apply (nodup_toList _).pairwise_of_forall_ne
    intro x _ y _ hxy
    simpa using hxy
  have hABdis : ∀ C ∈ A, ∀ D ∈ B, Disjoint C D := by
    intro C hC D hD
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hC
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hD
    have hxL : x ∈ L := mem_toList.mp hx
    obtain ⟨hxI, hxR⟩ := mem_sdiff.mp hxL
    apply disjoint_left.mpr
    intro z hz hz'
    have hzx : z = x := mem_singleton.mp hz'
    subst z
    simp only [pair, mem_insert, mem_singleton] at hz
    rcases hz with rfl | hx
    · exact hyI y hxI
    · exact hxR (mem_image.mpr ⟨y, mem_univ _, hx.symm⟩)
  refine ⟨A ++ B, List.pairwise_append.mpr ⟨hAdis, hBdis, hABdis⟩, ?_, ?_, ?_⟩
  · intro C hC u hu w hw huw
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hC
      simp only [pair, mem_insert, mem_singleton] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact False.elim (huw rfl)
      · exact hadj y
      · exact (hadj y).symm
      · exact False.elim (huw rfl)
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hC
      have hu' := mem_singleton.mp hu
      have hw' := mem_singleton.mp hw
      exact False.elim (huw (hu'.trans hw'.symm))
  · intro x
    constructor
    · intro hxS
      by_cases hxI : x ∈ I
      · by_cases hxR : x ∈ R
        · obtain ⟨y, _, hy⟩ := mem_image.mp hxR
          refine ⟨pair y, List.mem_append.mpr (Or.inl ?_), ?_⟩
          · exact List.mem_map.mpr ⟨y, mem_toList.mpr (mem_univ _), rfl⟩
          · simp only [pair, mem_insert, mem_singleton]
            exact Or.inr hy.symm
        · refine ⟨{x}, List.mem_append.mpr (Or.inr ?_), mem_singleton_self x⟩
          exact List.mem_map.mpr ⟨x, mem_toList.mpr (mem_sdiff.mpr ⟨hxI, hxR⟩), rfl⟩
      · let y : (↑Y : Set V) := ⟨x, mem_sdiff.mpr ⟨hxS, hxI⟩⟩
        refine ⟨pair y, List.mem_append.mpr (Or.inl ?_), ?_⟩
        · exact List.mem_map.mpr ⟨y, mem_toList.mpr (mem_univ _), rfl⟩
        · exact mem_insert_self _ _
    · rintro ⟨C, hC, hx⟩
      rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨y, _, rfl⟩ := List.mem_map.mp hC
        simp only [pair, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (mem_sdiff.mp y.property).1
        · exact hI.subset (hfyI y)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hC
        rw [mem_singleton] at hx
        subst x
        exact hI.subset (mem_sdiff.mp (mem_toList.mp hy)).1
  · have hAcards : A.map Finset.card = List.replicate Y.card 2 := by
      simp only [A, List.map_map, Function.comp_def, hpaircard,
        List.map_const', length_toList, card_univ]
      congr 1
      exact Fintype.card_coe Y
    have hBcards : B.map Finset.card = List.replicate L.card 1 := by
      simp only [B, List.map_map, Function.comp_def, card_singleton,
        List.map_const', length_toList]
    rw [List.map_append, hAcards, hBcards, hLcard]
    rfl

/-- The actual graph coefficients satisfy the normalized adjacent-rank
inequality for the matching reference. -/
theorem IsMaximumIndependentOn.countIndependent_normalized_matching
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (k : ℕ) :
    (countIndependent G S (k + 1) : ℝ) *
        (matchingUpperCount I.card (S \ I).card k : ℝ) ≤
      (countIndependent G S k : ℝ) *
        (matchingUpperCount I.card (S \ I).card (k + 1) : ℝ) := by
  obtain ⟨Bs, hdis, hclique, hcover, hcards⟩ := hI.exists_matching_blocks hG
  have hpos : ∀ B ∈ Bs, 0 < B.card := by
    intro B hB
    apply matchingColors_pos I.card (S \ I).card B.card
    rw [← hcards]
    exact List.mem_map.mpr ⟨B, hB, rfl⟩
  have h := BlockRankEncoding.normalized_countIndependent_of_blocks
    G S Bs hdis hclique hcover hpos k
  rw [hcards, matchingColors_weights, referenceRank_matching_eq,
    referenceRank_matching_eq] at h
  exact h

/-- The upper half of the analytic coefficient window holds for the actual
forest at every order. The cutoff is floor((n+2*alpha)/6)+1. -/
theorem IsMaximumIndependentOn.countIndependent_succ_le_of_matching_tail
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (k : ℕ)
    (hk : (S.card + 2 * I.card) / 6 + 1 ≤ k) :
    countIndependent G S (k + 1) ≤ countIndependent G S k := by
  have hva := hI.complement_card_le_of_isAcyclic hG
  have hcard := card_sdiff_add_card_eq_card hI.subset
  have hcut : (3 * I.card + (S \ I).card) / 6 + 1 ≤ k := by omega
  by_cases hka : k ≤ I.card
  · have hq : (0 : ℝ) < matchingUpperCount I.card (S \ I).card k := by
      exact_mod_cast (matchingUpperCount_pos_iff I.card (S \ I).card k hva).mpr hka
    have htail : (matchingUpperCount I.card (S \ I).card (k + 1) : ℝ) ≤
        matchingUpperCount I.card (S \ I).card k := by
      exact_mod_cast matchingUpperCount_tail I.card (S \ I).card k hva hcut
    have h := (hI.countIndependent_normalized_matching hG k).trans
      (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg (countIndependent G S k)))
    have hc := le_of_mul_le_mul_right h hq
    exact_mod_cast hc
  · rw [hI.countIndependent_eq_zero_of_card_lt (show I.card < k + 1 by omega)]
    exact Nat.zero_le _

#print axioms IsMaximumIndependentOn.exists_matching_blocks
#print axioms IsMaximumIndependentOn.countIndependent_normalized_matching
#print axioms IsMaximumIndependentOn.countIndependent_succ_le_of_matching_tail

end ForestUnimodality
