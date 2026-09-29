import ForestUnimodality.MarginalComplementMatching
import ForestUnimodality.BlockRankEncoding
import ForestUnimodality.FixedShiftMass
import Mathlib.Data.List.Nodup

/-!
The complement of a maximum marginal-weight independent set has a concrete
matching. Retaining only these matching edges gives a coefficient envelope;
additional graph edges can only remove configurations. This module connects
that actual-graph envelope to the fixed-shift mass identity.
-/

namespace ForestUnimodality

open Finset HereditaryRank
open MarginalComplementMatching

variable {V : Type*} [DecidableEq V]

/-- The coefficient of `(1 + 2 X)^r (1 + X)^(c - 2 r)`. The shift is guarded:
choosing more than `y` matching edges contributes zero. -/
def complementMatchingEnvelope (c r y : ℕ) : ℕ :=
  ∑ j ∈ range (r + 1), r.choose j * 2 ^ j * shiftedChoose (c - 2 * r) j y

theorem complementMatchingEnvelope_eq_matchingUpperCount (c r y : ℕ) :
    complementMatchingEnvelope c r y = matchingUpperCount (c - r) r y := by
  simp only [complementMatchingEnvelope, matchingUpperCount, Nat.sub_sub, two_mul]

theorem complementMatchingEnvelope_eq_coeff (c r y : ℕ) :
    complementMatchingEnvelope c r y =
      (((1 + 2 * Polynomial.X) ^ r * (1 + Polynomial.X) ^ (c - 2 * r) :
        Polynomial ℕ).coeff y) := by
  rw [complementMatchingEnvelope_eq_matchingUpperCount, ← coeff_matching_polynomial]
  simp only [Nat.sub_sub, two_mul]

theorem complementMatchingEnvelope_eq_sum_min (c r y : ℕ) :
    complementMatchingEnvelope c r y =
      ∑ j ∈ range (min r y + 1), r.choose j * 2 ^ j * (c - 2 * r).choose (y - j) := by
  unfold complementMatchingEnvelope
  symm
  calc
    _ = ∑ j ∈ range (min r y + 1), r.choose j * 2 ^ j * shiftedChoose (c - 2 * r) j y := by
      apply sum_congr rfl
      intro j hj
      have hjy : j ≤ y := (Nat.le_of_lt_succ (mem_range.mp hj)).trans (min_le_right r y)
      simp [shiftedChoose, hjy]
    _ = _ := sum_subset (range_mono (by omega)) (by
      intro j hj hnot
      have hjy : y < j := by
        have hjr := mem_range.mp hj
        have hjmin := mt mem_range.mpr hnot
        omega
      simp [shiftedChoose, Nat.not_le.mpr hjy])

/-- The source envelope `A^(m)_(n,y)`: maximum over all feasible selected-set
sizes. The inequality `n ≤ 3*h` is exactly `ceil(n/3) ≤ h`. Empty maxima are
zero by the natural-number supremum convention. -/
def marginalCountEnvelope (n m y : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun h => n ≤ 3 * h ∧ m ≤ h)).sup
    (fun h => complementMatchingEnvelope (n - h) (n - 2 * h) y)

theorem complementMatchingEnvelope_le_marginalCountEnvelope
    {n m h : ℕ} (hhn : h ≤ n) (hnh : n ≤ 3 * h) (hmh : m ≤ h) (y : ℕ) :
    complementMatchingEnvelope (n - h) (n - 2 * h) y ≤ marginalCountEnvelope n m y := by
  unfold marginalCountEnvelope
  apply Finset.le_sup (b := h) (f := fun t => complementMatchingEnvelope (n - t) (n - 2 * t) y)
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hhn), hnh, hmh⟩

theorem marginalCountEnvelope_antitone (n y : ℕ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    marginalCountEnvelope n m₂ y ≤ marginalCountEnvelope n m₁ y := by
  apply Finset.sup_le
  intro h hh
  obtain ⟨hhr, hnh, hmh⟩ := mem_filter.mp hh
  exact complementMatchingEnvelope_le_marginalCountEnvelope
    (Nat.le_of_lt_succ (mem_range.mp hhr)) hnh (hm.trans hmh) y

namespace MarginalComplementMatching

theorem EdgeMatchingOn.card_biUnion {G : SimpleGraph V} {C : Finset V}
    {M : Finset (Finset V)} (hM : EdgeMatchingOn G C M) :
    (M.biUnion id).card = 2 * M.card := by
  classical
  rw [Finset.card_biUnion]
  · calc
      (∑ E ∈ M, E.card) = ∑ _E ∈ M, 2 := by
        apply sum_congr rfl
        intro E hE
        exact (mem_edgePairsOn.mp (hM.edges hE)).2.1
      _ = 2 * M.card := by simp [mul_comm]
  · exact hM.disjoint

theorem EdgeMatchingOn.biUnion_subset {G : SimpleGraph V} {C : Finset V}
    {M : Finset (Finset V)} (hM : EdgeMatchingOn G C M) : M.biUnion id ⊆ C := by
  intro x hx
  obtain ⟨E, hE, hxE⟩ := mem_biUnion.mp hx
  exact (mem_edgePairsOn.mp (hM.edges hE)).1 hxE

theorem EdgeMatchingOn.two_mul_card_le {G : SimpleGraph V} {C : Finset V}
    {M : Finset (Finset V)} (hM : EdgeMatchingOn G C M) :
    2 * M.card ≤ C.card := by
  rw [← hM.card_biUnion]
  exact card_le_card hM.biUnion_subset

/-- A matching, even one that does not saturate a maximum independent set,
partitions the vertex set into edge blocks and the remaining singleton blocks. -/
theorem EdgeMatchingOn.exists_blocks {G : SimpleGraph V} {C : Finset V}
    {M : Finset (Finset V)} (hM : EdgeMatchingOn G C M) :
    ∃ Bs : List (Finset V),
      Bs.Pairwise Disjoint ∧
      (∀ B ∈ Bs, ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v) ∧
      (∀ x, x ∈ C ↔ ∃ B ∈ Bs, x ∈ B) ∧
      Bs.map Finset.card = matchingColors (C.card - M.card) M.card := by
  classical
  let U := M.biUnion id
  let L := C \ U
  let A := M.toList
  let B := L.toList.map (fun x => ({x} : Finset V))
  have hAdis : A.Pairwise Disjoint := by
    exact (nodup_toList M).pairwise_of_forall_ne
      (fun E hE F hF hEF => hM.disjoint E (mem_toList.mp hE) F (mem_toList.mp hF) hEF)
  have hBdis : B.Pairwise Disjoint := by
    rw [show B = L.toList.map (fun x => ({x} : Finset V)) from rfl, List.pairwise_map]
    apply (nodup_toList L).pairwise_of_forall_ne
    intro x _ y _ hxy
    simpa using hxy
  have hABdis : ∀ E ∈ A, ∀ F ∈ B, Disjoint E F := by
    intro E hE F hF
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hF
    have hxU : x ∉ U := (mem_sdiff.mp (mem_toList.mp hx)).2
    apply disjoint_left.mpr
    intro y hy hyx
    have hyx' := mem_singleton.mp hyx
    subst y
    exact hxU (mem_biUnion.mpr ⟨E, mem_toList.mp hE, hy⟩)
  refine ⟨A ++ B, List.pairwise_append.mpr ⟨hAdis, hBdis, hABdis⟩, ?_, ?_, ?_⟩
  · intro E hE u hu v hv huv
    rcases List.mem_append.mp hE with hE | hE
    · obtain ⟨x, _, y, _, hxy, he⟩ :=
        edgePairsOn_exists_adj_pair (hM.edges (mem_toList.mp hE))
      rw [he] at hu hv
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact False.elim (huv rfl)
      · exact hxy
      · exact hxy.symm
      · exact False.elim (huv rfl)
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hE
      exact False.elim (huv ((mem_singleton.mp hu).trans (mem_singleton.mp hv).symm))
  · intro x
    constructor
    · intro hxC
      by_cases hxU : x ∈ U
      · obtain ⟨E, hE, hxE⟩ := mem_biUnion.mp hxU
        exact ⟨E, List.mem_append.mpr (Or.inl (mem_toList.mpr hE)), hxE⟩
      · refine ⟨{x}, List.mem_append.mpr (Or.inr ?_), mem_singleton_self x⟩
        exact List.mem_map.mpr ⟨x, mem_toList.mpr (mem_sdiff.mpr ⟨hxC, hxU⟩), rfl⟩
    · rintro ⟨E, hE, hxE⟩
      rcases List.mem_append.mp hE with hE | hE
      · exact (mem_edgePairsOn.mp (hM.edges (mem_toList.mp hE))).1 hxE
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hE
        have hxy := mem_singleton.mp hxE
        subst x
        exact (mem_sdiff.mp (mem_toList.mp hy)).1
  · have hAcards : A.map Finset.card = List.replicate M.card 2 := by
      have he : A.map Finset.card = A.map (fun _ => 2) := by
        apply List.map_congr_left
        intro E hE
        exact (mem_edgePairsOn.mp (hM.edges (mem_toList.mp hE))).2.1
      rw [he]
      simp [A]
    have hBcards : B.map Finset.card = List.replicate L.card 1 := by
      simp only [B, List.map_map, Function.comp_def, card_singleton,
        List.map_const', length_toList]
    have hLcard : L.card = C.card - 2 * M.card := by
      rw [show L = C \ U from rfl, card_sdiff_of_subset hM.biUnion_subset, hM.card_biUnion]
    rw [List.map_append, hAcards, hBcards, hLcard, matchingColors]
    congr 2
    omega

/-- True independent sets form a subfamily of all colored matching-block
configurations. No assumption is made about the edges between different blocks. -/
theorem EdgeMatchingOn.countIndependent_le_envelope {G : SimpleGraph V}
    {C : Finset V} {M : Finset (Finset V)} (hM : EdgeMatchingOn G C M) (y : ℕ) :
    countIndependent G C y ≤ complementMatchingEnvelope C.card M.card y := by
  obtain ⟨Bs, hdis, hclique, hcover, hcards⟩ := hM.exists_blocks
  have h := rankCount_le_reference (BlockRankEncoding.independentFamily G Bs) (y : ℤ)
  rw [BlockRankEncoding.rankCount_independentFamily G C Bs hdis hclique hcover,
    hcards, matchingColors_weights, referenceRank_matching_eq,
    ← complementMatchingEnvelope_eq_matchingUpperCount] at h
  exact_mod_cast h

end MarginalComplementMatching

theorem IsMaximumMarginalIndependentOn.countIndependent_complement_le_envelope
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) (y : ℕ) :
    countIndependent G (S \ B) y ≤
      complementMatchingEnvelope (S.card - B.card) (S.card - 2 * B.card) y := by
  obtain ⟨M, hM, hcard⟩ := exists_complement_matching_exact hG hB hz
  have h := hM.countIndependent_le_envelope y
  rwa [hcard, card_sdiff_of_subset hB.subset] at h

theorem IsMaximumMarginalIndependentOn.fixedShiftMass_le_matching_path_bound
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) (k y : ℕ) :
    hardCoreFixedShiftMass G S B z k ((k : ℤ) - y) ≤
      (complementMatchingEnvelope (S.card - B.card) (S.card - 2 * B.card) y : ℝ) *
        z ^ y / pathPartitionLower S.card z := by
  apply hardCoreFixedShiftMass_le_path_bound G hG S B hz k y
  exact_mod_cast hB.countIndependent_complement_le_envelope hG hz y

theorem IsMaximumMarginalIndependentOn.countIndependent_complement_le_marginalEnvelope
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    {m : ℕ} (hm : m ≤ B.card) (y : ℕ) :
    countIndependent G (S \ B) y ≤ marginalCountEnvelope S.card m y :=
  (hB.countIndependent_complement_le_envelope hG hz y).trans
    (complementMatchingEnvelope_le_marginalCountEnvelope (card_le_card hB.subset)
      (order_le_three_mul_selected hG hB hz) hm y)

/-- Every actual positive layer has positive restricted envelope. This is a
support consequence, with the available-vertex bound proved from the layer. -/
theorem IsMaximumMarginalIndependentOn.marginalEnvelope_pos_of_layerCount_pos
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z)
    {y m : ℕ} (hpos : 0 < layerCount G B (S \ B) y m) :
    0 < marginalCountEnvelope S.card m y := by
  classical
  have hc : layerCount G B (S \ B) y m ≤ countIndependent G (S \ B) y := by
    apply card_le_card
    intro J hJ
    obtain ⟨hJ, hcard, _⟩ := mem_filter.mp hJ
    exact mem_filter.mpr ⟨hJ, hcard⟩
  obtain ⟨J, hJ⟩ := card_pos.mp hpos
  have hcard := (mem_filter.mp hJ).2.2
  have hm : m ≤ B.card := by
    rw [← hcard]
    exact card_le_card (available_subset G B J)
  exact hpos.trans_le (hc.trans (hB.countIndependent_complement_le_marginalEnvelope hG hz hm y))

theorem IsMaximumMarginalIndependentOn.fixedShiftMass_le_marginal_path_bound
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) (k y : ℕ) :
    hardCoreFixedShiftMass G S B z k ((k : ℤ) - y) ≤
      (marginalCountEnvelope S.card 0 y : ℝ) * z ^ y / pathPartitionLower S.card z := by
  apply hardCoreFixedShiftMass_le_path_bound G hG S B hz k y
  exact_mod_cast hB.countIndependent_complement_le_marginalEnvelope hG hz (Nat.zero_le _) y

/-- Signed shifts above `k` are impossible; the conversion to a natural
outside size is made only on the branch where it is nonnegative. -/
theorem IsMaximumMarginalIndependentOn.fixedShiftMass_le_guarded_marginal_path_bound
    {G : SimpleGraph V} (hG : G.IsAcyclic) {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hz : 0 < z) (k : ℕ) (r : ℤ) :
    hardCoreFixedShiftMass G S B z k r ≤
      if r ≤ (k : ℤ) then
        (marginalCountEnvelope S.card 0 ((k : ℤ) - r).toNat : ℝ) *
          z ^ ((k : ℤ) - r).toNat / pathPartitionLower S.card z else 0 := by
  by_cases hr : r ≤ (k : ℤ)
  · rw [if_pos hr]
    have he : (k : ℤ) - (((k : ℤ) - r).toNat : ℤ) = r := by omega
    simpa only [he] using hB.fixedShiftMass_le_marginal_path_bound hG hz k ((k : ℤ) - r).toNat
  · rw [if_neg hr, hardCoreFixedShiftMass_eq_zero_of_lt G S B z k r (lt_of_not_ge hr)]

#print axioms MarginalComplementMatching.EdgeMatchingOn.exists_blocks
#print axioms MarginalComplementMatching.EdgeMatchingOn.countIndependent_le_envelope
#print axioms IsMaximumMarginalIndependentOn.countIndependent_complement_le_envelope
#print axioms IsMaximumMarginalIndependentOn.fixedShiftMass_le_matching_path_bound
#print axioms complementMatchingEnvelope_eq_sum_min
#print axioms complementMatchingEnvelope_eq_coeff
#print axioms IsMaximumMarginalIndependentOn.marginalEnvelope_pos_of_layerCount_pos
#print axioms IsMaximumMarginalIndependentOn.fixedShiftMass_le_guarded_marginal_path_bound

end ForestUnimodality
