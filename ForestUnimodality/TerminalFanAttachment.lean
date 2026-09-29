import ForestUnimodality.TerminalFanAttachmentHelpers

/-! The eight actual rooted branch parameter types imply strict positivity
for a fan attached at a degree-at-most-one, state-one host root. Structural
classification into this configuration is a separate obligation. -/

namespace ForestUnimodality
open Finset
universe u v
variable {V : Type u} [DecidableEq V]

/-- A leaf or isolated host root has the stronger deletion ratio required
by the terminal-fan closure. The isolated case includes a singleton host. -/
theorem partitionFunction_leaf_root_ratio_bounds (G : SimpleGraph V) (K : Finset V)
    {u : V} (hu : u ∈ K) (hdegree : degreeOn G K u ≤ 1) :
    (5 / 3 : ℝ) ≤ partitionFunction G K 2 / partitionFunction G (K.erase u) 2 ∧
      partitionFunction G K (2 : ℝ) / partitionFunction G (K.erase u) 2 ≤ 3 := by
  classical
  have hJ := partitionFunction_pos G (K.erase u) (by norm_num : (0 : ℝ) ≤ 2)
  have hz := partitionFunction_delete_vertex G K hu (2 : ℝ)
  refine ⟨?_, ?_⟩
  · apply (le_div_iff₀ hJ).mpr
    by_cases hex : ∃ v ∈ K, G.Adj u v
    · obtain ⟨v, hv, huv⟩ := hex
      have huniq := adj_eq_of_degreeOn_le_one G K hv huv hdegree
      have hc := sdiff_closedNeighborhoodIn_of_unique_neighbor G K huv
        (fun w hw hadj => (huniq w hw).mp hadj)
      rw [hc] at hz
      have hvJ : v ∈ K.erase u := mem_erase.mpr ⟨huv.ne.symm, hv⟩
      have hD := partitionFunction_pos G ((K.erase u).erase v) (by norm_num : (0 : ℝ) ≤ 2)
      have hr := (partitionFunction_delete_ratio_bounds G (K.erase u) hvJ
        (by norm_num : (0 : ℝ) ≤ 2)).2
      have hjd : partitionFunction G (K.erase u) (2 : ℝ) ≤
          3 * partitionFunction G ((K.erase u).erase v) 2 := by
        apply (div_le_iff₀ hD).mp
        simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hr
      linarith
    · have hc : K \ closedNeighborhoodIn G K u = K.erase u := by
        ext x
        simp only [mem_sdiff_closedNeighborhoodIn, mem_erase]
        constructor
        · exact fun h => ⟨h.2.1, h.1⟩
        · exact fun h => ⟨h.2, h.1, fun hx => hex ⟨x, h.2, hx⟩⟩
      rw [hc] at hz
      linarith
  · simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
      (partitionFunction_delete_ratio_bounds G K hu (by norm_num : (0 : ℝ) ≤ 2)).2

variable {ι : Type v} [DecidableEq ι]

namespace IsRootedFanAttachment

variable {G : SimpleGraph V} {S K : Finset V} {u : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanAttachment G S K u s B root)

include h

theorem deleted_order_ge_nine (kind : ι → Fin 8)
    (hp : ∀ i ∈ s, InducedIso.BranchParameters G (B i) (root i) (kind i))
    (hm : 2 ≤ s.card) (ht : ∃ i ∈ s, (kind i).val < 2) :
    9 ≤ (s.biUnion B).card := by
  have htwo (j : ι) (hj : j ∈ s) : 2 ≤ (B j).card := by
    rw [(hp j hj).order_eq]
    generalize kind j = k
    fin_cases k <;> norm_num [MeanTerminalGraphs.branchOrder]
  obtain ⟨i, hi, hit⟩ := ht
  have hseven : 7 ≤ (B i).card := by
    rw [(hp i hi).order_eq]
    have he : (kind i).val = 0 ∨ (kind i).val = 1 := by omega
    rcases he with he | he <;> simp [MeanTerminalGraphs.branchOrder, he]
  have hsum : 2 * (s.erase i).card ≤ ∑ j ∈ s.erase i, (B j).card := by
    calc
      _ = ∑ _j ∈ s.erase i, 2 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun j hj => htwo j (mem_of_mem_erase hj))
  have he := sum_erase_add s (fun j => (B j).card) hi
  have hc := card_erase_add_one hi
  rw [h.separated.card_biUnion]
  omega

/-- All numerical parameters of the actual union are the products and sums
of the already established branch parameters. -/
theorem union_parameters (kind : ι → Fin 8)
    (hp : ∀ i ∈ s, InducedIso.BranchParameters G (B i) (root i) (kind i)) :
    let fan := s.toList.map (fun i => (kind i).val)
    let U := s.biUnion B
    let D := s.biUnion (fun i => (B i).erase (root i))
    partitionFunction G U (2 : ℝ) / partitionFunction G D 2 =
      ((fan.map MeanTerminalClosure.branchRatio).prod : ℝ) ∧
    adjustedMeanPotential G U (independenceNumberOn G U) =
      ((fan.map MeanTerminalClosure.branchExcess).sum : ℝ) ∧
    3 * hardCoreMean G D 2 - (independenceNumberOn G U : ℝ) -
        (29 / 60 : ℝ) * U.card =
      ((fan.map MeanTerminalClosure.branchDeletedExcess).sum : ℝ) := by
  dsimp only
  have hsep := h.separated.subsets (fun i _ => erase_subset (root i) (B i))
  constructor
  · rw [h.separated.partitionFunction_biUnion, hsep.partitionFunction_biUnion,
      ← prod_div_distrib]
    simp only [List.map_map, Function.comp_def, prod_map_toList, Rat.cast_prod]
    exact prod_congr rfl (fun i hi => (hp i hi).ratio_eq)
  constructor
  · unfold adjustedMeanPotential
    rw [h.separated.mean_biUnion (by norm_num : (0 : ℝ) ≤ 2),
      h.separated.independenceNumber_biUnion, h.separated.card_biUnion]
    simp only [List.map_map, Function.comp_def, sum_map_toList, Rat.cast_sum, Nat.cast_sum,
      mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    exact (hp i hi).excess_eq
  · rw [hsep.mean_biUnion (by norm_num : (0 : ℝ) ≤ 2),
      h.separated.independenceNumber_biUnion, h.separated.card_biUnion]
    simp only [List.map_map, Function.comp_def, sum_map_toList, Rat.cast_sum, Nat.cast_sum,
      mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    have he := (hp i hi).deleted_excess_eq
    convert he using 1
    ring

/-- The actual host, actual smaller fresh path, and actual eight branch
types discharge every premise of the finite-plus-unbounded fan closure. -/
theorem adjustedMean_pos_of_eight_types (hG : G.IsAcyclic)
    (hsmaller : GlobalSmallerMeanHyp.{u} S.card) (kind : ι → Fin 8)
    (hp : ∀ i ∈ s, InducedIso.BranchParameters G (B i) (root i) (kind i))
    (hm : 2 ≤ s.card) (ht : ∃ i ∈ s, (kind i).val < 2)
    (hstate : rootDefect G K u = 1) (hdegree : degreeOn G K u ≤ 1) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  let fan := s.toList.map (fun i => (kind i).val)
  let U := s.biUnion B
  let D := s.biUnion (fun i => (B i).erase (root i))
  let A := partitionFunction G D (2 : ℝ)
  let r := partitionFunction G K (2 : ℝ) / partitionFunction G (K.erase u) 2
  let X := r * adjustedMeanPotential G K (independenceNumberOn G K)
  let Y := adjustedMeanPotential G (K.erase u) (independenceNumberOn G (K.erase u))
  have hN := h.deleted_order_ge_nine kind hp hm ht
  have hcard := h.card
  have hKsmall : K.card < S.card := by omega
  have hJsmall : (K.erase u).card < S.card :=
    (card_le_card (erase_subset _ _)).trans_lt hKsmall
  have hr := partitionFunction_leaf_root_ratio_bounds G K h.host_root_mem hdegree
  have hA : 0 < A := partitionFunction_pos G D (by norm_num : (0 : ℝ) ≤ 2)
  have hJ : 0 < partitionFunction G (K.erase u) (2 : ℝ) :=
    partitionFunction_pos G (K.erase u) (by norm_num : (0 : ℝ) ≤ 2)
  have hX : 0 ≤ X := mul_nonneg (by dsimp only [r]; linarith [hr.1])
    (hsmaller V G K hKsmall hG)
  have hY : 0 ≤ Y := hsmaller V G (K.erase u) hJsmall hG
  have hpath : 0 ≤ 180 * X + 120 * Y + 6 * r - 54 := by
    have he := FreshPathContext.path_residual_nonneg hsmaller G hG K h.host_root_mem
      2 (by decide) (by omega)
    dsimp only at he
    rw [hstate] at he
    simp only [Nat.cast_one] at he
    change 0 ≤ TerminalBlockRecurrence.E
      (TerminalBlockRecurrence.castState (TerminalContextCertificate.pathState 2)) (1 : ℝ) X Y r at he
    norm_num [TerminalContextCertificate.pathState, TerminalBlockRecurrence.iterate,
      TerminalBlockRecurrence.extend, TerminalBlockRecurrence.castState,
      TerminalBlockRecurrence.E] at he
    nlinarith
  have hfanlen : 2 ≤ fan.length := by simpa [fan] using hm
  have hfanbound : ∀ j ∈ fan, j < 8 := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    exact (kind i).isLt
  have hfanterm : MeanTerminalClosure.hasTerminal fan = true := by
    simp only [MeanTerminalClosure.hasTerminal, List.any_eq_true, decide_eq_true_eq]
    obtain ⟨i, hi, hit⟩ := ht
    exact ⟨(kind i).val, List.mem_map.mpr ⟨i, mem_toList.mpr hi, rfl⟩, hit⟩
  have hclose := MeanTerminalClosure.fan_closure fan hfanlen hfanbound hfanterm
    A X Y r hA hX hY hr.1 hr.2 hpath
  have he := h.adjustedMean_identity (fun i hi => (hp i hi).root_state_zero) hstate
  obtain ⟨hR, ha, hb⟩ := h.union_parameters kind hp
  dsimp only at he hR ha hb
  rw [hR, ha, hb] at he
  change 60 * partitionFunction G S (2 : ℝ) *
      adjustedMeanPotential G S (independenceNumberOn G S) =
    partitionFunction G (K.erase u) 2 * (60 * A *
      (X + (((fan.map MeanTerminalClosure.branchRatio).prod : ℝ) - 1) * Y +
        ((fan.map MeanTerminalClosure.branchRatio).prod : ℝ) *
          (((fan.map MeanTerminalClosure.branchExcess).sum : ℝ) - 89 / 60) +
        (r - 1) * ((fan.map MeanTerminalClosure.branchDeletedExcess).sum : ℝ) + 89 / 60)) at he
  have hpos : 0 < 60 * partitionFunction G S (2 : ℝ) *
      adjustedMeanPotential G S (independenceNumberOn G S) := by
    rw [he]
    exact mul_pos hJ hclose
  exact pos_of_mul_pos_right hpos (mul_nonneg (by norm_num)
    (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2)).le)

end IsRootedFanAttachment

#print axioms partitionFunction_leaf_root_ratio_bounds
#print axioms IsRootedFanAttachment.deleted_order_ge_nine
#print axioms IsRootedFanAttachment.union_parameters
#print axioms IsRootedFanAttachment.adjustedMean_pos_of_eight_types
end ForestUnimodality
