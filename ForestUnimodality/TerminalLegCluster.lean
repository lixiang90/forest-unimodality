import ForestUnimodality.TreeTerminalDecomposition
import ForestUnimodality.SpiderClosure
import ForestUnimodality.ShortLegReal

/-! Exact short-leg cluster residual for a terminal spider with an actual
external host. The center is absorbed into the smaller host. -/
namespace ForestUnimodality
open Finset
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
variable {G : SimpleGraph V} {S H T : Finset V} {c p : V}
  {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}

theorem IsTerminalSpiderOn.center_host_path
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    PendantPathExtension G H p 1 (insert c H) c := by
  apply (PendantPathExtension.zero h.attachment.host_root_mem).succ c
    h.attachment.block_root_not_host
  intro x hx
  constructor
  · intro hadj
    exact ((h.attachment.cross x hx c h.attachment.block_root_mem).mp hadj.symm).1
  · intro he
    exact ((h.attachment.cross x hx c h.attachment.block_root_mem).mpr ⟨he, rfl⟩).symm

theorem IsTerminalSpiderOn.center_host_statistics
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    partitionFunction G (insert c H) (2 : ℝ) = partitionFunction G H 2 +
        2 * partitionFunction G (H.erase p) 2 ∧
    hardCoreMomentNumerator G (insert c H) 1 (2 : ℝ) = hardCoreMomentNumerator G H 1 2 +
        2 * (hardCoreMomentNumerator G (H.erase p) 1 2 + partitionFunction G (H.erase p) 2) := by
  have ht := h.center_host_path.moment_transfer 2
  norm_num only [pathMomentTransfer] at ht
  exact ⟨congrArg Prod.fst ht, congrArg (fun q => q.2.1) ht⟩

theorem IsTerminalSpiderOn.center_host_alpha
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    independenceNumberOn G (insert c H) = independenceNumberOn G (H.erase p) + 1 := by
  have ht := h.center_host_path.card_transfer
  simp only [pathCardTransfer] at ht
  have ha := congrArg Prod.fst ht
  dsimp only at ha
  rw [max_eq_right (independenceNumberOn_erase_bounds G H p).2] at ha
  exact ha

theorem IsTerminalSpiderOn.center_host_defects
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    rootDefect G (insert c H) c + rootDefect G H p = 1 := by
  have ha := h.center_host_alpha
  have hb := independenceNumberOn_erase_bounds G H p
  unfold rootDefect
  rw [erase_insert h.attachment.block_root_not_host]
  omega

theorem IsTerminalSpiderOn.alpha_sameParity
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (odd : Bool)
    (hpar : ∀ i ∈ s, length i % 2 = if odd then 1 else 0) :
    independenceNumberOn G S = independenceNumberOn G H +
      (∑ i ∈ s, independenceNumberOn G (B i)) +
      (if odd then 0 else rootDefect G (insert c H) c) := by
  have hsum : independenceNumberOn G (T.erase c) = ∑ i ∈ s, independenceNumberOn G (B i) := by
    rw [h.spider.erase_center, h.spider.separated.independenceNumber_biUnion]
  have ha := h.attachment.independenceNumber_add_defects
  rw [← h.vertices] at ha
  have hd := h.center_host_defects
  cases odd with
  | false =>
    have ht := h.spider.toIsRootedFanOn.alpha_of_root_state_zero (by
      intro i hi
      have hp := h.spider.branch_alpha_pair hi
      have hp1 := congrArg Prod.fst hp
      have hp2 := congrArg Prod.snd hp
      have hmod := hpar i hi
      dsimp only at hp1 hp2
      simp only [Bool.false_eq_true, ↓reduceIte] at hmod
      omega)
    have hdt : rootDefect G T c = 1 := by unfold rootDefect; rw [ht, hsum]; omega
    rw [hdt, mul_one, ht] at ha
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    have ht := h.spider.toIsRootedFanOn.alpha_of_root_state_one
      (card_pos.mp (by have := h.branches; omega)) (by
        intro i hi
        have hp := h.spider.branch_alpha_pair hi
        have hp1 := congrArg Prod.fst hp
        have hp2 := congrArg Prod.snd hp
        have hmod := hpar i hi
        dsimp only at hp1 hp2
        simp only [↓reduceIte] at hmod
        omega)
    have hdt : rootDefect G T c = 0 := by unfold rootDefect; rw [ht, hsum]; omega
    rw [hdt, mul_zero, add_zero, ht] at ha
    simpa only [↓reduceIte, add_zero] using ha

theorem IsTerminalSpiderOn.leg_partition
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    partitionFunction G S (2 : ℝ) =
      (∏ i ∈ s, partitionFunction G (B i) 2) * partitionFunction G H 2 +
      (∏ i ∈ s, partitionFunction G ((B i).erase (root i)) 2) *
        (partitionFunction G (insert c H) 2 - partitionFunction G H 2) := by
  have hz := h.attachment.partitionFunction_eq (2 : ℝ)
  rw [← h.vertices, h.spider.toIsRootedFanOn.partitionFunction_eq G (2 : ℝ),
    h.spider.erase_center, h.spider.separated.partitionFunction_biUnion] at hz
  rw [hz, h.center_host_statistics.1]
  ring

theorem IsTerminalSpiderOn.leg_firstMoment
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    hardCoreMomentNumerator G S 1 (2 : ℝ) =
      (∏ i ∈ s, partitionFunction G (B i) 2) * hardCoreMomentNumerator G H 1 2 +
      ((∑ i ∈ s, hardCoreMean G (B i) 2) * (∏ i ∈ s, partitionFunction G (B i) 2)) *
        partitionFunction G H 2 +
      (∏ i ∈ s, partitionFunction G ((B i).erase (root i)) 2) *
        (hardCoreMomentNumerator G (insert c H) 1 2 - hardCoreMomentNumerator G H 1 2) +
      ((∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) 2) *
        (∏ i ∈ s, partitionFunction G ((B i).erase (root i)) 2)) *
        (partitionFunction G (insert c H) 2 - partitionFunction G H 2) := by
  have hm := h.attachment.firstMoment_eq (2 : ℝ)
  have hmd : hardCoreMomentNumerator G (T.erase c) 1 (2 : ℝ) =
      (∑ i ∈ s, hardCoreMean G (B i) 2) * (∏ i ∈ s, partitionFunction G (B i) 2) := by
    rw [hardCore_first_moment_eq_mean_mul_partition G _ (by norm_num : (0 : ℝ) ≤ 2),
      h.spider.erase_center, h.spider.separated.mean_biUnion (by norm_num : (0 : ℝ) ≤ 2),
      h.spider.separated.partitionFunction_biUnion]
  rw [← h.vertices, hmd,
    h.spider.toIsRootedFanOn.firstMoment (by norm_num : (0 : ℝ) ≤ 2),
    h.spider.toIsRootedFanOn.partitionFunction_eq G (2 : ℝ),
    h.spider.erase_center, h.spider.separated.partitionFunction_biUnion] at hm
  rw [hm, h.center_host_statistics.1, h.center_host_statistics.2]
  ring

set_option maxHeartbeats 1600000 in
theorem IsTerminalSpiderOn.leg_adjustedMean_identity
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (odd : Bool)
    (hpar : ∀ i ∈ s, length i % 2 = if odd then 1 else 0) :
    let K := insert c H
    let r := partitionFunction G K (2 : ℝ) / partitionFunction G H 2
    let d : ℝ := rootDefect G K c
    let cost : ℝ := 29 / 60 + if odd then 0 else d
    let R := fun i => partitionFunction G (B i) (2 : ℝ) /
      partitionFunction G ((B i).erase (root i)) 2
    let a := fun i => adjustedMeanPotential G (B i) (independenceNumberOn G (B i))
    let b := fun i => deletedRootExcess G (B i) (root i)
    let D := ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ)
    partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S (independenceNumberOn G S) =
      partitionFunction G H (2 : ℝ) * D *
        (r * adjustedMeanPotential G K (independenceNumberOn G K) +
          ((∏ i ∈ s, R i) - 1) * adjustedMeanPotential G H (independenceNumberOn G H) +
          (∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - cost) +
          (r - 1) * (∑ i ∈ s, b i) + cost + if odd then r * d else 0) := by
  have hzS := partitionFunction_pos G S (z := (2 : ℝ)) (by norm_num)
  have hzH := partitionFunction_pos G H (z := (2 : ℝ)) (by norm_num)
  have hzK := partitionFunction_pos G (insert c H) (z := (2 : ℝ)) (by norm_num)
  have hzD : 0 < ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ) :=
    prod_pos (fun i _ => partitionFunction_pos G _ (by norm_num : (0 : ℝ) ≤ 2))
  have halpha : (independenceNumberOn G S : ℝ) = (independenceNumberOn G H : ℝ) +
      (∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) +
      (if odd then 0 else (rootDefect G (insert c H) c : ℝ)) := by
    exact_mod_cast h.alpha_sameParity odd hpar
  have halphaK : (independenceNumberOn G (insert c H) : ℝ) =
      (independenceNumberOn G H : ℝ) + (rootDefect G (insert c H) c : ℝ) := by
    rw [rootDefect_cast, erase_insert h.attachment.block_root_not_host]
    ring
  have hcard : (S.card : ℝ) = (H.card : ℝ) +
      (∑ i ∈ s, ((B i).card : ℝ)) + 1 := by
    have hc : S.card = H.card + (∑ i ∈ s, (B i).card) + 1 := by
      rw [h.vertices, card_union_of_disjoint h.attachment.disjoint, h.spider.toIsRootedFanOn.card]
      omega
    exact_mod_cast hc
  have hcardK : ((insert c H).card : ℝ) = (H.card : ℝ) + 1 := by
    exact_mod_cast card_insert_of_notMem h.attachment.block_root_not_host
  have ha : (∑ i ∈ s, adjustedMeanPotential G (B i) (independenceNumberOn G (B i))) =
      3 * (∑ i ∈ s, hardCoreMean G (B i) 2) -
      (∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) -
      (29 / 60 : ℝ) * (∑ i ∈ s, ((B i).card : ℝ)) := by
    simp only [adjustedMeanPotential, sum_sub_distrib, ← mul_sum]
  have hb : (∑ i ∈ s, deletedRootExcess G (B i) (root i)) =
      3 * (∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) 2) -
      (∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) -
      (29 / 60 : ℝ) * (∑ i ∈ s, ((B i).card : ℝ)) := by
    simp only [deletedRootExcess, sum_sub_distrib, ← mul_sum]
  have hZ := h.leg_partition
  have hM := h.leg_firstMoment
  dsimp only
  rw [prod_div_distrib, ha, hb]
  unfold adjustedMeanPotential hardCoreMean
  unfold hardCoreMean at hM
  rw [halpha, halphaK, hcard, hcardK]
  cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    field_simp [ne_of_gt hzS, ne_of_gt hzH, ne_of_gt hzK, ne_of_gt hzD] <;>
    rw [hM, hZ] <;> ring

omit [DecidableEq ι] in
theorem IsSpiderOn.residualReal_eq
    (h : IsSpiderOn G T c s B root tip length) (odd : Bool) (delta : ℕ) (r : ℝ) :
    ShortLegData.residualReal odd (s.toList.map length) delta r =
      let cost : ℝ := 29 / 60 + if odd then 0 else delta
      (∏ i ∈ s, partitionFunction G (B i) (2 : ℝ) /
        partitionFunction G ((B i).erase (root i)) 2) *
        ((∑ i ∈ s, adjustedMeanPotential G (B i) (independenceNumberOn G (B i))) - cost) +
      (r - 1) * (∑ i ∈ s, deletedRootExcess G (B i) (root i)) + cost +
        if odd then r * delta else 0 := by
  unfold ShortLegData.residualReal
  push_cast
  simp only [List.map_map, Function.comp_def, prod_map_toList, sum_map_toList]
  rw [prod_congr rfl (fun i hi => (h.branch_parameters hi).1.symm),
    sum_congr rfl (fun i hi => (h.branch_parameters hi).2.1.symm)]
  have hb : (∑ i ∈ s, (ShortLegData.deletedExcess (length i) : ℝ)) =
      ∑ i ∈ s, deletedRootExcess G (B i) (root i) := by
    apply sum_congr rfl
    intro i hi
    simpa only [deletedRootExcess, div_eq_mul_inv, mul_assoc] using
      (h.branch_parameters hi).2.2.symm
  rw [hb]

theorem IsTerminalSpiderOn.center_ratio_bounds
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) :
    1 ≤ partitionFunction G (insert c H) (2 : ℝ) / partitionFunction G H 2 ∧
      partitionFunction G (insert c H) (2 : ℝ) / partitionFunction G H 2 ≤ 3 := by
  have hr := partitionFunction_delete_ratio_bounds G (insert c H) (mem_insert_self c H)
    (z := (2 : ℝ)) (by norm_num)
  simpa only [erase_insert h.attachment.block_root_not_host,
    show (1 : ℝ) + 2 = 3 by norm_num] using hr

theorem IsTerminalSpiderOn.adjustedMean_pos_of_leg_residual
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (odd : Bool)
    (hpar : ∀ i ∈ s, length i % 2 = if odd then 1 else 0)
    (hK : 0 ≤ adjustedMeanPotential G (insert c H) (independenceNumberOn G (insert c H)))
    (hH : 0 ≤ adjustedMeanPotential G H (independenceNumberOn G H))
    (hres : 0 < ShortLegData.residualReal odd (s.toList.map length)
      (rootDefect G (insert c H) c)
      (partitionFunction G (insert c H) (2 : ℝ) / partitionFunction G H 2)) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  have hR : (1 : ℝ) ≤ ∏ i ∈ s, partitionFunction G (B i) (2 : ℝ) /
      partitionFunction G ((B i).erase (root i)) 2 := by
    calc
      (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => by norm_num) (fun i hi =>
        (partitionFunction_delete_ratio_bounds G (B i) (h.spider.root_mem i hi)
          (z := (2 : ℝ)) (by norm_num)).1)
  have hr := h.center_ratio_bounds.1
  have hX := mul_nonneg (show 0 ≤ partitionFunction G (insert c H) (2 : ℝ) /
      partitionFunction G H 2 by linarith) hK
  have hY := mul_nonneg (sub_nonneg.mpr hR) hH
  rw [h.spider.residualReal_eq] at hres
  dsimp only at hres
  have hid := h.leg_adjustedMean_identity odd hpar
  dsimp only at hid
  have hZH := partitionFunction_pos G H (z := (2 : ℝ)) (by norm_num)
  have hD : 0 < ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ) :=
    prod_pos (fun _ _ => partitionFunction_pos G _ (by norm_num : (0 : ℝ) ≤ 2))
  have hsum := add_pos_of_nonneg_of_pos (add_nonneg hX hY) hres
  have hpos := mul_pos (mul_pos hZH hD) hsum
  have he : partitionFunction G S (2 : ℝ) *
      adjustedMeanPotential G S (independenceNumberOn G S) > 0 := by
    rw [hid]
    cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero] at hpos ⊢ <;>
      nlinarith only [hpos]
  exact (mul_pos_iff_of_pos_left (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2))).mp he

/-- At least four same-parity short legs close for every actual host ratio
and deletion state; there is no upper bound on the number of legs. -/
theorem IsTerminalSpiderOn.leg_residual_pos_of_four_short_legs
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hm : 4 ≤ s.card)
    (hshort : ∀ i ∈ s, length i ≤ 13) (odd : Bool)
    (hpar : ∀ i ∈ s, length i % 2 = if odd then 1 else 0) :
    0 < ShortLegData.residualReal odd (s.toList.map length)
      (rootDefect G (insert c H) c)
      (partitionFunction G (insert c H) (2 : ℝ) / partitionFunction G H 2) := by
  let R := fun i => partitionFunction G (B i) (2 : ℝ) /
    partitionFunction G ((B i).erase (root i)) 2
  let a := fun i => adjustedMeanPotential G (B i) (independenceNumberOn G (B i))
  let b := fun i => deletedRootExcess G (B i) (root i)
  let r := partitionFunction G (insert c H) (2 : ℝ) / partitionFunction G H 2
  have hr := h.center_ratio_bounds
  have hd : rootDefect G (insert c H) c ≤ 1 := by
    rcases rootDefect_zero_or_one G (insert c H) c with he | he <;> omega
  have hdR : (rootDefect G (insert c H) c : ℝ) ≤ 1 := by exact_mod_cast hd
  rw [h.spider.residualReal_eq]
  cases odd with
  | false =>
    have hbds := fun i hi => h.spider.short_even_bounds hi (hshort i hi)
      (by simpa using hpar i hi)
    have hh := ShortLegClosure.even_cluster_positive s R a b r
      (29 / 60 + (rootDefect G (insert c H) c : ℝ)) hm
      (fun i hi => (hbds i hi).1) (fun i hi => (hbds i hi).2.1)
      (fun i hi => (hbds i hi).2.2) hr.1 hr.2 (by linarith)
    simpa only [R, a, b, r, Bool.false_eq_true, ↓reduceIte, add_zero] using hh
  | true =>
    have hbds := fun i hi => h.spider.short_odd_bounds hi (hshort i hi)
      (by simpa using hpar i hi)
    have hh := ShortLegClosure.odd_cluster_positive s R a b r hm
      (fun i hi => (hbds i hi).1) (fun i hi => (hbds i hi).2.1)
      (fun i hi => (hbds i hi).2.2) hr.1 hr.2
    have hdelta : 0 ≤ r * (rootDefect G (insert c H) c : ℝ) :=
      mul_nonneg (by dsimp only [r]; linarith [hr.1]) (Nat.cast_nonneg _)
    dsimp only [R, a, b, r] at hh hdelta
    simp only [↓reduceIte, Nat.cast_zero, add_zero]
    linarith

theorem IsTerminalSpiderOn.adjustedMean_pos_of_four_short_legs
    (h : IsTerminalSpiderOn G S c H T p s B root tip length) (hm : 4 ≤ s.card)
    (hshort : ∀ i ∈ s, length i ≤ 13) (odd : Bool)
    (hpar : ∀ i ∈ s, length i % 2 = if odd then 1 else 0)
    (hK : 0 ≤ adjustedMeanPotential G (insert c H) (independenceNumberOn G (insert c H)))
    (hH : 0 ≤ adjustedMeanPotential G H (independenceNumberOn G H)) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) :=
  h.adjustedMean_pos_of_leg_residual odd hpar hK hH
    (h.leg_residual_pos_of_four_short_legs hm hshort odd hpar)

theorem IsTerminalSpiderOn.card_le_three_of_short_sameParity_nonpos
    (h : IsTerminalSpiderOn G S c H T p s B root tip length)
    (hshort : ∀ i ∈ s, length i ≤ 13) (odd : Bool)
    (hpar : ∀ i ∈ s, length i % 2 = if odd then 1 else 0)
    (hK : 0 ≤ adjustedMeanPotential G (insert c H) (independenceNumberOn G (insert c H)))
    (hH : 0 ≤ adjustedMeanPotential G H (independenceNumberOn G H))
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) ≤ 0) : s.card ≤ 3 := by
  by_contra hn
  exact (not_lt_of_ge hbad)
    (h.adjustedMean_pos_of_four_short_legs (by omega) hshort odd hpar hK hH)

#print axioms IsTerminalSpiderOn.alpha_sameParity
#print axioms IsTerminalSpiderOn.leg_firstMoment
#print axioms IsTerminalSpiderOn.leg_adjustedMean_identity
#print axioms IsTerminalSpiderOn.adjustedMean_pos_of_leg_residual
#print axioms IsTerminalSpiderOn.adjustedMean_pos_of_four_short_legs
end ForestUnimodality
