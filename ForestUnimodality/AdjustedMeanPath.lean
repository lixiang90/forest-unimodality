import ForestUnimodality.AdjustedMeanLeaf
import Mathlib.Data.Finset.Lattice.Fold

/-! Exact transfers for an actual pendant path, expressed by repeatedly
adjoining a fresh vertex with precisely one neighbor in the previous set.
The hypotheses describe the induced graph, rather than numerical messages. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def independenceNumberOn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (independentSubsets G S).sup Finset.card

theorem IsMaximumIndependentOn.card_eq_independenceNumberOn
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I) :
    I.card = independenceNumberOn G S := by
  apply le_antisymm
  · exact Finset.le_sup hI.1
  · exact Finset.sup_le hI.2

theorem independenceNumberOn_mono (G : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) : independenceNumberOn G S ≤ independenceNumberOn G T := by
  apply Finset.sup_le
  intro I hI
  exact Finset.le_sup (independentSubsets_mono G hST hI)

theorem independenceNumberOn_delete_vertex (G : SimpleGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) :
    independenceNumberOn G S = max (independenceNumberOn G (S.erase v))
      (independenceNumberOn G (S \ closedNeighborhoodIn G S v) + 1) := by
  classical
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  obtain ⟨J, hJ⟩ := exists_maximumIndependentOn G (S \ closedNeighborhoodIn G S v)
  apply le_antisymm
  · rw [← hI.card_eq_independenceNumberOn]
    by_cases hvi : v ∈ I
    · have he := erase_mem_independentSubsets_sdiff_closedNeighborhoodIn hI.1 hvi
      have hb : (I.erase v).card ≤ independenceNumberOn G
          (S \ closedNeighborhoodIn G S v) := Finset.le_sup he
      have hc := card_erase_add_one hvi
      exact le_trans (by omega) (le_max_right _ _)
    · exact le_trans (Finset.le_sup (hI.erase_ambient_of_not_mem hvi).1)
        (le_max_left _ _)
  · apply max_le
    · exact independenceNumberOn_mono G (erase_subset _ _)
    · rw [← hJ.card_eq_independenceNumberOn]
      have hj := insert_mem_independentSubsets_of_sdiff_closedNeighborhoodIn hv hJ.1
      have hc : (insert v J).card = J.card + 1 :=
        card_insert_of_notMem (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ.1)
      rw [← hc]
      exact Finset.le_sup hj

theorem independenceNumberOn_erase_bounds (G : SimpleGraph V) (S : Finset V)
    (v : V) : independenceNumberOn G (S.erase v) ≤ independenceNumberOn G S ∧
      independenceNumberOn G S ≤ independenceNumberOn G (S.erase v) + 1 := by
  refine ⟨independenceNumberOn_mono G (erase_subset _ _), ?_⟩
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  have hmem : I.erase v ∈ independentSubsets G (S.erase v) := by
    apply mem_independentSubsets.mpr
    exact ⟨erase_subset_erase v hI.subset,
      hI.independent.mono (coe_subset.mpr (erase_subset _ _))⟩
  have hb : (I.erase v).card ≤ independenceNumberOn G (S.erase v) := Finset.le_sup hmem
  rw [← hI.card_eq_independenceNumberOn]
  by_cases hv : v ∈ I
  · have hc := card_erase_add_one hv
    omega
  · rw [erase_eq_of_notMem hv] at hb
    omega

/-- A genuine path extension. At every step the fresh endpoint has exactly
the previous endpoint as its neighbor inside the preceding ambient set. -/
inductive PendantPathExtension (G : SimpleGraph V) (H : Finset V) (v : V) :
    ℕ → Finset V → V → Prop
  | zero (hv : v ∈ H) : PendantPathExtension G H v 0 H v
  | succ {n S u} (h : PendantPathExtension G H v n S u) (w : V)
      (hw : w ∉ S) (hadj : ∀ x ∈ S, G.Adj w x ↔ x = u) :
      PendantPathExtension G H v (n + 1) (insert w S) w

theorem PendantPathExtension.endpoint_mem {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) : u ∈ S := by
  cases h with
  | zero hv => exact hv
  | succ => exact mem_insert_self _ _

theorem PendantPathExtension.card_eq {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) : S.card = H.card + n := by
  induction h with
  | zero _ => omega
  | succ h w hw hadj ih => rw [card_insert_of_notMem hw, ih]; omega

theorem PendantPathExtension.root_mem {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) : v ∈ H := by
  induction h with
  | zero hv => exact hv
  | succ _ _ _ _ ih => exact ih

theorem PendantPathExtension.host_subset {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) : H ⊆ S := by
  induction h with
  | zero _ => exact Subset.refl _
  | succ _ _ _ _ ih => exact ih.trans (subset_insert _ _)

theorem sdiff_closedNeighborhoodIn_insert_leaf (G : SimpleGraph V) (S : Finset V)
    {u w : V} (_hu : u ∈ S) (hw : w ∉ S)
    (hadj : ∀ x ∈ S, G.Adj w x ↔ x = u) :
    insert w S \ closedNeighborhoodIn G (insert w S) w = S.erase u := by
  ext x
  simp only [mem_sdiff_closedNeighborhoodIn, mem_insert, mem_erase]
  constructor
  · rintro ⟨hx | hx, hxw, hn⟩
    · exact False.elim (hxw hx)
    · exact ⟨fun hxu => hn ((hadj x hx).mpr hxu), hx⟩
  · rintro ⟨hxu, hx⟩
    exact ⟨Or.inr hx, fun hxw => hw (hxw ▸ hx), fun h => hxu ((hadj x hx).mp h)⟩

/-- Four coordinates: Z, first moment, and the same two quantities after
deleting the current endpoint. This transfer is valid at every real activity. -/
def pathMomentTransfer (z : ℝ) : ℕ → (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ)
  | 0, x => x
  | n + 1, x =>
    let y := pathMomentTransfer z n x
    (y.1 + z * y.2.2.1, y.2.1 + z * (y.2.2.2 + y.2.2.1), y.1, y.2.1)

def pathCardTransfer : ℕ → (ℕ × ℕ) → (ℕ × ℕ)
  | 0, x => x
  | n + 1, x => let y := pathCardTransfer n x; (max y.1 (y.2 + 1), y.1)

theorem PendantPathExtension.moment_transfer {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) (z : ℝ) :
    (partitionFunction G S z, hardCoreMomentNumerator G S 1 z,
      partitionFunction G (S.erase u) z, hardCoreMomentNumerator G (S.erase u) 1 z) =
    pathMomentTransfer z n
      (partitionFunction G H z, hardCoreMomentNumerator G H 1 z,
        partitionFunction G (H.erase v) z, hardCoreMomentNumerator G (H.erase v) 1 z) := by
  classical
  induction h with
  | zero hv => rfl
  | @succ n S u h w hw hadj ih =>
    have hc := sdiff_closedNeighborhoodIn_insert_leaf G S h.endpoint_mem hw hadj
    have he : (insert w S).erase w = S := erase_insert hw
    have hz := partitionFunction_delete_vertex G (insert w S) (mem_insert_self w S) z
    have hm := hardCore_first_moment_delete_vertex G (insert w S) (mem_insert_self w S) z
    rw [hc, he] at hz hm
    simp only [pathMomentTransfer]
    rw [← ih, he, hz, hm]

theorem PendantPathExtension.card_transfer {G : SimpleGraph V} {H S : Finset V}
    {v u : V} {n : ℕ} (h : PendantPathExtension G H v n S u) :
    (independenceNumberOn G S, independenceNumberOn G (S.erase u)) =
    pathCardTransfer n (independenceNumberOn G H, independenceNumberOn G (H.erase v)) := by
  classical
  induction h with
  | zero hv => rfl
  | @succ n S u h w hw hadj ih =>
    have hc := sdiff_closedNeighborhoodIn_insert_leaf G S h.endpoint_mem hw hadj
    have he : (insert w S).erase w = S := erase_insert hw
    have ha := independenceNumberOn_delete_vertex G (insert w S) (mem_insert_self w S)
    rw [hc, he] at ha
    simp only [pathCardTransfer]
    rw [← ih, he, ha]

theorem pathCardTransfer_even (a b m : ℕ) (hba : b ≤ a) (hab : a ≤ b + 1) :
    pathCardTransfer (2 * m) (a, b) = (a + m, b + m) := by
  induction m with
  | zero => simp [pathCardTransfer]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
    simp only [pathCardTransfer, ih]
    rw [max_eq_right (by omega : a + m ≤ b + m + 1),
      max_eq_right (by omega : b + m + 1 ≤ a + m + 1)]
    congr 1

theorem PendantPathExtension.independenceNumber_fourteen
    {G : SimpleGraph V} {H S : Finset V} {v u : V}
    (h : PendantPathExtension G H v 14 S u) :
    independenceNumberOn G S = independenceNumberOn G H + 7 := by
  have hb := independenceNumberOn_erase_bounds G H v
  have ht := h.card_transfer
  rw [show 14 = 2 * 7 by norm_num, pathCardTransfer_even _ _ _ hb.1 hb.2] at ht
  exact congrArg Prod.fst ht

theorem pathMomentTransfer_fourteen (Z M D N : ℝ) :
    pathMomentTransfer 2 14 (Z, M, D, N) =
      (10923 * Z + 10922 * D,
        10923 * M + 10922 * N + 49762 * Z + 57034 * D,
        5461 * Z + 5462 * D,
        5461 * M + 5462 * N + 23056 * Z + 26706 * D) := by
  norm_num [pathMomentTransfer]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem PendantPathExtension.partitionFunction_fourteen
    {G : SimpleGraph V} {H S : Finset V} {v u : V}
    (h : PendantPathExtension G H v 14 S u) :
    partitionFunction G S (2 : ℝ) = 10923 * partitionFunction G H (2 : ℝ) +
      10922 * partitionFunction G (H.erase v) (2 : ℝ) := by
  have ht := h.moment_transfer 2
  rw [pathMomentTransfer_fourteen] at ht
  exact congrArg Prod.fst ht

theorem PendantPathExtension.firstMoment_fourteen
    {G : SimpleGraph V} {H S : Finset V} {v u : V}
    (h : PendantPathExtension G H v 14 S u) :
    hardCoreMomentNumerator G S 1 (2 : ℝ) =
      10923 * hardCoreMomentNumerator G H 1 (2 : ℝ) +
      10922 * hardCoreMomentNumerator G (H.erase v) 1 (2 : ℝ) +
      49762 * partitionFunction G H (2 : ℝ) +
      57034 * partitionFunction G (H.erase v) (2 : ℝ) := by
  have ht := h.moment_transfer 2
  rw [pathMomentTransfer_fourteen] at ht
  exact congrArg (fun x => x.2.1) ht

/-- Exact potential identity; the maximum-cardinality defect of deleting
the host root is left explicit, and is subsequently bounded by one. -/
theorem PendantPathExtension.adjustedMean_fourteen_identity
    {G : SimpleGraph V} {H S : Finset V} {v u : V}
    (h : PendantPathExtension G H v 14 S u) :
    60 * partitionFunction G S (2 : ℝ) *
        adjustedMeanPotential G S (independenceNumberOn G S) =
      655380 * partitionFunction G H (2 : ℝ) *
        adjustedMeanPotential G H (independenceNumberOn G H) +
      655320 * partitionFunction G (H.erase v) (2 : ℝ) *
        adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v)) -
      65238 * partitionFunction G H (2 : ℝ) +
      (927810 - 655320 * ((independenceNumberOn G H : ℝ) -
        (independenceNumberOn G (H.erase v) : ℝ))) *
        partitionFunction G (H.erase v) (2 : ℝ) := by
  have hZ := h.partitionFunction_fourteen
  have hM := h.firstMoment_fourteen
  have ha := h.independenceNumber_fourteen
  have hn := h.card_eq
  have hnH : H.card = (H.erase v).card + 1 := (card_erase_add_one h.root_mem).symm
  have hnS : S.card = (H.erase v).card + 15 := by omega
  have hZH := ne_of_gt (partitionFunction_pos G H (by norm_num : (0 : ℝ) ≤ 2))
  have hZJ := ne_of_gt (partitionFunction_pos G (H.erase v) (by norm_num : (0 : ℝ) ≤ 2))
  have hZF := ne_of_gt (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2))
  have hden : 10923 * partitionFunction G H (2 : ℝ) +
      10922 * partitionFunction G (H.erase v) (2 : ℝ) ≠ 0 := by rw [← hZ]; exact hZF
  unfold adjustedMeanPotential hardCoreMean
  rw [hZ, hM, ha, hnS, hnH]
  push_cast
  field_simp
  ring

/-- Fourteen actual pendant vertices have a uniformly positive remainder,
provided the two actual smaller host graphs satisfy the adjusted bound. -/
theorem PendantPathExtension.adjustedMean_fourteen_lower
    {G : SimpleGraph V} {H S : Finset V} {v u : V}
    (h : PendantPathExtension G H v 14 S u)
    (hH : 0 ≤ adjustedMeanPotential G H (independenceNumberOn G H))
    (hJ : 0 ≤ adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))) :
    (6398 / 218455 : ℝ) ≤ adjustedMeanPotential G S (independenceNumberOn G S) := by
  have hA := partitionFunction_pos G H (by norm_num : (0 : ℝ) ≤ 2)
  have hB := partitionFunction_pos G (H.erase v) (by norm_num : (0 : ℝ) ≤ 2)
  have hF := partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2)
  have hratio := (partitionFunction_delete_ratio_bounds G H h.root_mem
    (by norm_num : (0 : ℝ) ≤ 2)).2
  have hAB : partitionFunction G H (2 : ℝ) ≤
      3 * partitionFunction G (H.erase v) (2 : ℝ) := by
    apply (div_le_iff₀ hB).mp
    simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hratio
  have hd : (independenceNumberOn G H : ℝ) ≤
      (independenceNumberOn G (H.erase v) : ℝ) + 1 := by
    exact_mod_cast (independenceNumberOn_erase_bounds G H v).2
  have hdef : 272490 ≤ 927810 - 655320 * ((independenceNumberOn G H : ℝ) -
      (independenceNumberOn G (H.erase v) : ℝ)) := by linarith
  have hprod := mul_le_mul_of_nonneg_right hdef hB.le
  have hid := h.adjustedMean_fourteen_identity
  have hres : 76776 * partitionFunction G (H.erase v) (2 : ℝ) ≤
      60 * partitionFunction G S (2 : ℝ) *
        adjustedMeanPotential G S (independenceNumberOn G S) := by
    nlinarith [mul_nonneg hA.le hH, mul_nonneg hB.le hJ]
  have hZF : partitionFunction G S (2 : ℝ) ≤
      43691 * partitionFunction G (H.erase v) (2 : ℝ) := by
    rw [h.partitionFunction_fourteen]
    linarith
  by_contra hn
  have hh : adjustedMeanPotential G S (independenceNumberOn G S) < (6398 / 218455 : ℝ) :=
    lt_of_not_ge hn
  have hp := mul_lt_mul_of_pos_left hh
    (show 0 < 60 * partitionFunction G S (2 : ℝ) by positivity)
  nlinarith

/-- Thus an actual minimal nonpositive counterexample cannot contain any
pendant extension of length fourteen. No tree-decomposition coverage is
assumed or claimed by this pruning lemma. -/
theorem no_pendantPath_fourteen_of_adjustedMean_nonpos
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card ≤ 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card)
    {H : Finset V} {v u : V} : ¬ PendantPathExtension G H v 14 S u := by
  intro h
  obtain ⟨J, hJ⟩ := exists_maximumIndependentOn G H
  obtain ⟨K, hK⟩ := exists_maximumIndependentOn G (H.erase v)
  have hlt : H.card < S.card := by have := h.card_eq; omega
  have hltJ : (H.erase v).card < S.card := (card_le_card (erase_subset _ _)).trans_lt hlt
  have hH := hsmaller H h.host_subset hlt J hJ
  have hD := hsmaller (H.erase v) ((erase_subset _ _).trans h.host_subset) hltJ K hK
  rw [hJ.card_eq_independenceNumberOn] at hH
  rw [hK.card_eq_independenceNumberOn] at hD
  rw [hI.card_eq_independenceNumberOn] at hbad
  have hpos := h.adjustedMean_fourteen_lower hH hD
  norm_num at hpos ⊢
  linarith

#print axioms PendantPathExtension.moment_transfer
#print axioms PendantPathExtension.card_transfer
#print axioms PendantPathExtension.independenceNumber_fourteen
#print axioms PendantPathExtension.partitionFunction_fourteen
#print axioms PendantPathExtension.firstMoment_fourteen
#print axioms PendantPathExtension.adjustedMean_fourteen_lower
#print axioms no_pendantPath_fourteen_of_adjustedMean_nonpos
end ForestUnimodality
