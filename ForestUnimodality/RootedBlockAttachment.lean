import ForestUnimodality.ForestComponentsMean
import ForestUnimodality.TerminalBlockRecurrence

/-! An actual host and actual rooted block joined by precisely one edge.
Their graph statistics are identified with the numerical BlockState and E
used by the terminal certificates. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

structure IsRootedBlockAttachment (G : SimpleGraph V) (H : Finset V) (v : V)
    (T : Finset V) (w : V) : Prop where
  host_root_mem : v ∈ H
  block_root_mem : w ∈ T
  disjoint : Disjoint H T
  cross : ∀ x ∈ H, ∀ y ∈ T, G.Adj x y ↔ x = v ∧ y = w

omit [DecidableEq V] in
theorem IsRootedBlockAttachment.block_root_not_host
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) : w ∉ H :=
  fun hwH => disjoint_left.mp h.disjoint hwH h.block_root_mem

theorem IsRootedBlockAttachment.erase_block_root
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) : (H ∪ T).erase w = H ∪ T.erase w := by
  ext x
  simp only [mem_erase, mem_union]
  constructor
  · rintro ⟨hxw, hxH | hxT⟩
    · exact Or.inl hxH
    · exact Or.inr ⟨hxw, hxT⟩
  · rintro (hxH | ⟨hxw, hxT⟩)
    · exact ⟨fun hxw => h.block_root_not_host (hxw ▸ hxH), Or.inl hxH⟩
    · exact ⟨hxw, Or.inr hxT⟩

theorem IsRootedBlockAttachment.delete_closed_block_root
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    (H ∪ T) \ closedNeighborhoodIn G (H ∪ T) w =
      H.erase v ∪ (T \ closedNeighborhoodIn G T w) := by
  ext x
  simp only [mem_sdiff_closedNeighborhoodIn, mem_union, mem_erase]
  constructor
  · rintro ⟨hxH | hxT, hxw, hn⟩
    · refine Or.inl ⟨?_, hxH⟩
      intro hxv
      exact hn (((h.cross x hxH w h.block_root_mem).mpr ⟨hxv, rfl⟩).symm)
    · exact Or.inr ⟨hxT, hxw, hn⟩
  · rintro (⟨hxv, hxH⟩ | ⟨hxT, hxw, hn⟩)
    · refine ⟨Or.inl hxH, fun hxw => h.block_root_not_host (hxw ▸ hxH), ?_⟩
      intro hwx
      exact hxv ((h.cross x hxH w h.block_root_mem).mp hwx.symm).1
    · exact ⟨Or.inr hxT, hxw, hn⟩

theorem IsRootedBlockAttachment.no_edges_deleted_block
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    ∀ x ∈ H, ∀ y ∈ T.erase w, ¬ G.Adj x y := by
  intro x hx y hy hadj
  exact (mem_erase.mp hy).1 ((h.cross x hx y (mem_erase.mp hy).2).mp hadj).2

theorem IsRootedBlockAttachment.no_edges_deleted_host
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    ∀ x ∈ H.erase v, ∀ y ∈ T \ closedNeighborhoodIn G T w, ¬ G.Adj x y := by
  intro x hx y hy hadj
  exact (mem_erase.mp hx).1
    ((h.cross x (mem_erase.mp hx).2 y (mem_sdiff.mp hy).1).mp hadj).1

theorem IsRootedBlockAttachment.partitionFunction_eq
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) {R : Type*} [CommRing R] (z : R) :
    partitionFunction G (H ∪ T) z =
      partitionFunction G (T.erase w) z * partitionFunction G H z +
      (partitionFunction G T z - partitionFunction G (T.erase w) z) *
        partitionFunction G (H.erase v) z := by
  have hF := partitionFunction_delete_vertex G (H ∪ T)
    (v := w) (mem_union_right _ h.block_root_mem) z
  have hT := partitionFunction_delete_vertex G T h.block_root_mem z
  rw [h.erase_block_root, h.delete_closed_block_root,
    partitionFunction_disjoint_union G H (T.erase w)
      (h.disjoint.mono (Subset.refl _) (erase_subset _ _)) h.no_edges_deleted_block,
    partitionFunction_disjoint_union G (H.erase v) (T \ closedNeighborhoodIn G T w)
      (h.disjoint.mono (erase_subset _ _) sdiff_subset) h.no_edges_deleted_host] at hF
  rw [hF, hT]
  ring

theorem IsRootedBlockAttachment.firstMoment_eq
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) (z : ℝ) :
    hardCoreMomentNumerator G (H ∪ T) 1 z =
      hardCoreMomentNumerator G (T.erase w) 1 z * partitionFunction G H z +
      partitionFunction G (T.erase w) z * hardCoreMomentNumerator G H 1 z +
      (hardCoreMomentNumerator G T 1 z - hardCoreMomentNumerator G (T.erase w) 1 z) *
        partitionFunction G (H.erase v) z +
      (partitionFunction G T z - partitionFunction G (T.erase w) z) *
        hardCoreMomentNumerator G (H.erase v) 1 z := by
  have hF := hardCore_first_moment_delete_vertex G (H ∪ T)
    (v := w) (mem_union_right _ h.block_root_mem) z
  have hT := hardCore_first_moment_delete_vertex G T h.block_root_mem z
  have hZT := partitionFunction_delete_vertex G T h.block_root_mem z
  rw [h.erase_block_root, h.delete_closed_block_root,
    hardCore_first_moment_disjoint_union G H (T.erase w)
      (h.disjoint.mono (Subset.refl _) (erase_subset _ _)) h.no_edges_deleted_block,
    hardCore_first_moment_disjoint_union G (H.erase v) (T \ closedNeighborhoodIn G T w)
      (h.disjoint.mono (erase_subset _ _) sdiff_subset) h.no_edges_deleted_host,
    partitionFunction_disjoint_union G (H.erase v) (T \ closedNeighborhoodIn G T w)
      (h.disjoint.mono (erase_subset _ _) sdiff_subset) h.no_edges_deleted_host] at hF
  rw [hF, hT, hZT]
  ring

noncomputable def rootDefect (G : SimpleGraph V) (H : Finset V) (v : V) : ℕ :=
  independenceNumberOn G H - independenceNumberOn G (H.erase v)

theorem rootDefect_zero_or_one (G : SimpleGraph V) (H : Finset V) (v : V) :
    rootDefect G H v = 0 ∨ rootDefect G H v = 1 := by
  have hb := independenceNumberOn_erase_bounds G H v
  unfold rootDefect
  omega

theorem rootDefect_cast (G : SimpleGraph V) (H : Finset V) (v : V) :
    (rootDefect G H v : ℝ) = (independenceNumberOn G H : ℝ) -
      (independenceNumberOn G (H.erase v) : ℝ) :=
  Nat.cast_sub (independenceNumberOn_erase_bounds G H v).1

theorem IsRootedBlockAttachment.independenceNumber_add_defects
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    independenceNumberOn G (H ∪ T) + rootDefect G H v * rootDefect G T w =
      independenceNumberOn G H + independenceNumberOn G T := by
  have hF := independenceNumberOn_delete_vertex G (H ∪ T)
    (v := w) (mem_union_right _ h.block_root_mem)
  have hT := independenceNumberOn_delete_vertex G T h.block_root_mem
  rw [h.erase_block_root, h.delete_closed_block_root,
    independenceNumberOn_disjoint_union G H (T.erase w)
      (h.disjoint.mono (Subset.refl _) (erase_subset _ _)) h.no_edges_deleted_block,
    independenceNumberOn_disjoint_union G (H.erase v) (T \ closedNeighborhoodIn G T w)
      (h.disjoint.mono (erase_subset _ _) sdiff_subset) h.no_edges_deleted_host] at hF
  have hcsub : T \ closedNeighborhoodIn G T w ⊆ T.erase w := by
    intro x hx
    obtain ⟨hxT, hxw, _⟩ := mem_sdiff_closedNeighborhoodIn.mp hx
    exact mem_erase.mpr ⟨hxw, hxT⟩
  have hc := independenceNumberOn_mono G hcsub
  have hbH := independenceNumberOn_erase_bounds G H v
  have hbT := independenceNumberOn_erase_bounds G T w
  rcases rootDefect_zero_or_one G H v with hd | hd
  · rw [hd, zero_mul, Nat.add_zero]
    unfold rootDefect at hd
    omega
  · rw [hd, one_mul]
    unfold rootDefect at hd ⊢
    omega

theorem IsRootedBlockAttachment.independenceNumber_eq
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    independenceNumberOn G (H ∪ T) = independenceNumberOn G H + independenceNumberOn G T -
      rootDefect G H v * rootDefect G T w := by
  have he := h.independenceNumber_add_defects
  omega

/-- The numerical block state is extracted from actual induced graph
statistics, including the actual 0-or-1 root deletion defect. -/
noncomputable def actualBlockState (G : SimpleGraph V) (T : Finset V) (w : V) :
    TerminalBlockRecurrence.BlockState ℝ :=
  ⟨partitionFunction G (T.erase w) 2,
    partitionFunction G T 2 - partitionFunction G (T.erase w) 2,
    hardCoreMomentNumerator G (T.erase w) 1 2,
    hardCoreMomentNumerator G T 1 2 - hardCoreMomentNumerator G (T.erase w) 1 2,
    T.card, independenceNumberOn G T, rootDefect G T w⟩

set_option maxHeartbeats 1600000 in
/-- The certificate residual is exactly the positive mass multiplier times
the adjusted mean of the actual attached graph. -/
theorem IsRootedBlockAttachment.adjustedMean_identity
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    let s := actualBlockState G T w
    let r := partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2
    60 * (s.A * r + s.B) *
        adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) =
      TerminalBlockRecurrence.E s (rootDefect G H v : ℝ)
        (r * adjustedMeanPotential G H (independenceNumberOn G H))
        (adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))) r := by
  have hZF := partitionFunction_pos G (H ∪ T) (z := (2 : ℝ)) (by norm_num)
  have hZH := partitionFunction_pos G H (z := (2 : ℝ)) (by norm_num)
  have hZJ := partitionFunction_pos G (H.erase v) (z := (2 : ℝ)) (by norm_num)
  have hZ := h.partitionFunction_eq (2 : ℝ)
  have hM := h.firstMoment_eq (2 : ℝ)
  have ha : (independenceNumberOn G (H ∪ T) : ℝ) =
      independenceNumberOn G H + independenceNumberOn G T -
        (rootDefect G H v : ℝ) * rootDefect G T w := by
    have he : (independenceNumberOn G (H ∪ T) : ℝ) +
        (rootDefect G H v : ℝ) * rootDefect G T w =
        independenceNumberOn G H + independenceNumberOn G T := by
      exact_mod_cast h.independenceNumber_add_defects
    linarith
  have hc : ((H ∪ T).card : ℝ) = (H.card : ℝ) + T.card := by
    exact_mod_cast card_union_of_disjoint h.disjoint
  have hcH : (H.card : ℝ) = ((H.erase v).card : ℝ) + 1 := by
    exact_mod_cast (card_erase_add_one h.host_root_mem).symm
  dsimp [actualBlockState, TerminalBlockRecurrence.E]
  rw [show partitionFunction G (T.erase w) (2 : ℝ) *
      (partitionFunction G H 2 / partitionFunction G (H.erase v) 2) +
      (partitionFunction G T 2 - partitionFunction G (T.erase w) 2) =
      partitionFunction G (H ∪ T) 2 / partitionFunction G (H.erase v) 2 by
    rw [hZ]; field_simp]
  unfold adjustedMeanPotential hardCoreMean
  rw [ha, hc, rootDefect_cast, hcH]
  field_simp [ne_of_gt hZF, ne_of_gt hZH, ne_of_gt hZJ]
  rw [hM, hZ]
  ring

theorem actualBlockState_extend (G : SimpleGraph V) (T : Finset V) {w u : V}
    (hw : w ∈ T) (hu : u ∉ T) (hadj : ∀ x ∈ T, G.Adj u x ↔ x = w) :
    actualBlockState G (insert u T) u =
      TerminalBlockRecurrence.extend (actualBlockState G T w) := by
  have hc := sdiff_closedNeighborhoodIn_insert_leaf G T hw hu hadj
  have he : (insert u T).erase u = T := erase_insert hu
  have hZ := partitionFunction_delete_vertex G (insert u T) (mem_insert_self u T) (2 : ℝ)
  have hM := hardCore_first_moment_delete_vertex G (insert u T)
    (mem_insert_self u T) (2 : ℝ)
  have ha := independenceNumberOn_delete_vertex G (insert u T) (mem_insert_self u T)
  rw [he, hc] at hZ hM ha
  have hb := independenceNumberOn_erase_bounds G T w
  rw [max_eq_right hb.2] at ha
  have har : (independenceNumberOn G (insert u T) : ℝ) =
      (independenceNumberOn G (T.erase w) : ℝ) + 1 := by exact_mod_cast ha
  have hdr := rootDefect_cast G T w
  have hdnew := rootDefect_cast G (insert u T) u
  rw [he] at hdnew
  dsimp [actualBlockState, TerminalBlockRecurrence.extend]
  rw [he, hZ, hM, card_insert_of_notMem hu, Nat.cast_add, Nat.cast_one]
  congr 1 <;> linarith

/-- Every actual successive leaf attachment has the numerical bridge state,
including its changing maximum-independent-set root defect. -/
theorem PendantPathExtension.actualBlockState_eq
    {G : SimpleGraph V} {H S : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G H v n S u) :
    actualBlockState G S u =
      TerminalBlockRecurrence.iterate n (actualBlockState G H v) := by
  induction h with
  | zero _ => rfl
  | @succ n S u h w hw hadj ih =>
    rw [actualBlockState_extend G S h.endpoint_mem hw hadj, ih]
    rfl

theorem actualBlockState_singleton (G : SimpleGraph V) (v : V) :
    actualBlockState G {v} v =
      (⟨1, 2, 0, 2, 1, 1, 1⟩ : TerminalBlockRecurrence.BlockState ℝ) := by
  have hs := hardCore_singleton_statistics G v (2 : ℝ)
  have hZ := congrArg Prod.fst hs
  have hM := congrArg (fun q => q.2.1) hs
  have hA := congrArg (fun q => q.2.2.1) hs
  have hMA := congrArg (fun q => q.2.2.2) hs
  dsimp only at hZ hM hA hMA
  have ha := independenceNumberOn_singleton G v
  have hae : independenceNumberOn G (({v} : Finset V).erase v) = 0 := by
    simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
  simp only [actualBlockState, hZ, hM, hA, hMA, Finset.card_singleton,
    rootDefect, ha, hae]
  norm_num

theorem PendantPathExtension.actualBlockState_path
    {G : SimpleGraph V} {S : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G {v} v n S u) :
    actualBlockState G S u = TerminalBlockRecurrence.iterate n
      (⟨1, 2, 0, 2, 1, 1, 1⟩ : TerminalBlockRecurrence.BlockState ℝ) := by
  rw [h.actualBlockState_eq, actualBlockState_singleton]

theorem IsRootedBlockAttachment.mass_factor_pos
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    0 < (actualBlockState G T w).A *
      (partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2) +
        (actualBlockState G T w).B := by
  have hJ := partitionFunction_pos G (H.erase v) (z := (2 : ℝ)) (by norm_num)
  have hF := partitionFunction_pos G (H ∪ T) (z := (2 : ℝ)) (by norm_num)
  have he : (actualBlockState G T w).A *
      (partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2) +
        (actualBlockState G T w).B =
      partitionFunction G (H ∪ T) 2 / partitionFunction G (H.erase v) 2 := by
    dsimp [actualBlockState]
    rw [h.partitionFunction_eq (2 : ℝ)]
    field_simp
  rw [he]
  exact div_pos hF hJ

theorem IsRootedBlockAttachment.adjustedMean_pos_iff
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    let r := partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2
    0 < adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ↔
      0 < TerminalBlockRecurrence.E (actualBlockState G T w) (rootDefect G H v : ℝ)
        (r * adjustedMeanPotential G H (independenceNumberOn G H))
        (adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))) r := by
  dsimp only
  rw [← h.adjustedMean_identity]
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) h.mass_factor_pos)).symm

theorem IsRootedBlockAttachment.adjustedMean_nonneg_iff
    {G : SimpleGraph V} {H T : Finset V} {v w : V}
    (h : IsRootedBlockAttachment G H v T w) :
    let r := partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2
    0 ≤ adjustedMeanPotential G (H ∪ T) (independenceNumberOn G (H ∪ T)) ↔
      0 ≤ TerminalBlockRecurrence.E (actualBlockState G T w) (rootDefect G H v : ℝ)
        (r * adjustedMeanPotential G H (independenceNumberOn G H))
        (adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))) r := by
  dsimp only
  rw [← h.adjustedMean_identity]
  exact (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) h.mass_factor_pos)).symm

#print axioms IsRootedBlockAttachment.partitionFunction_eq
#print axioms IsRootedBlockAttachment.firstMoment_eq
#print axioms IsRootedBlockAttachment.independenceNumber_eq
#print axioms IsRootedBlockAttachment.adjustedMean_identity
#print axioms PendantPathExtension.actualBlockState_eq
#print axioms PendantPathExtension.actualBlockState_path
#print axioms IsRootedBlockAttachment.adjustedMean_pos_iff
end ForestUnimodality
