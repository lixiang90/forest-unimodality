import ForestUnimodality.ForestComponentsMean

/-! Actual separated branches at a common center. A spider is represented
by real vertex sets and actual path-extension witnesses, not by a tuple of
numerical messages. Classification of arbitrary one-branching-point trees
is a separate structural obligation. -/
namespace ForestUnimodality
open Finset
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

structure IsSeparatedFamily (G : SimpleGraph V) (s : Finset ι) (B : ι → Finset V) : Prop where
  disjoint : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j)
  no_edges : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, ¬ G.Adj x y

omit [DecidableEq V] [DecidableEq ι] in
theorem IsSeparatedFamily.mono {G : SimpleGraph V} {s t : Finset ι} {B : ι → Finset V}
    (h : IsSeparatedFamily G s B) (ht : t ⊆ s) : IsSeparatedFamily G t B :=
  ⟨fun i hi j hj hij => h.disjoint i (ht hi) j (ht hj) hij,
    fun i hi j hj hij => h.no_edges i (ht hi) j (ht hj) hij⟩

omit [DecidableEq V] [DecidableEq ι] in
theorem IsSeparatedFamily.subsets {G : SimpleGraph V} {s : Finset ι}
    {B C : ι → Finset V} (h : IsSeparatedFamily G s B) (hCB : ∀ i ∈ s, C i ⊆ B i) :
    IsSeparatedFamily G s C := by
  refine ⟨?_, ?_⟩
  · intro i hi j hj hij
    exact (h.disjoint i hi j hj hij).mono (hCB i hi) (hCB j hj)
  · intro i hi j hj hij x hx y hy
    exact h.no_edges i hi j hj hij x (hCB i hi hx) y (hCB j hj hy)

theorem IsSeparatedFamily.disjoint_biUnion {G : SimpleGraph V} {s : Finset ι}
    {B : ι → Finset V} {i : ι} (h : IsSeparatedFamily G (insert i s) B) (hi : i ∉ s) :
    Disjoint (B i) (s.biUnion B) := by
  apply disjoint_left.mpr
  intro x hx hu
  obtain ⟨j, hj, hxj⟩ := mem_biUnion.mp hu
  exact disjoint_left.mp (h.disjoint i (mem_insert_self _ _) j (mem_insert_of_mem hj)
    (fun hij => hi (hij ▸ hj))) hx hxj

theorem IsSeparatedFamily.no_edges_biUnion {G : SimpleGraph V} {s : Finset ι}
    {B : ι → Finset V} {i : ι} (h : IsSeparatedFamily G (insert i s) B) (hi : i ∉ s) :
    ∀ x ∈ B i, ∀ y ∈ s.biUnion B, ¬ G.Adj x y := by
  intro x hx y hy
  obtain ⟨j, hj, hyj⟩ := mem_biUnion.mp hy
  exact h.no_edges i (mem_insert_self _ _) j (mem_insert_of_mem hj)
    (fun hij => hi (hij ▸ hj)) x hx y hyj

theorem independentSubsets_empty_eq_singleton (G : SimpleGraph V) :
    independentSubsets G (∅ : Finset V) = {∅} := by
  classical
  ext J
  simp only [mem_independentSubsets, subset_empty, mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, by simp [SimpleGraph.IsIndepSet, Set.Pairwise]⟩

theorem IsSeparatedFamily.partitionFunction_biUnion {R : Type*} [CommSemiring R]
    {G : SimpleGraph V} {s : Finset ι} {B : ι → Finset V}
    (h : IsSeparatedFamily G s B) (z : R) :
    partitionFunction G (s.biUnion B) z = ∏ i ∈ s, partitionFunction G (B i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [partitionFunction, independentSubsets_empty_eq_singleton]
  | @insert i s hi ih =>
    rw [biUnion_insert, prod_insert hi,
      partitionFunction_disjoint_union G (B i) (s.biUnion B)
        (h.disjoint_biUnion hi) (h.no_edges_biUnion hi)]
    rw [ih (h.mono (subset_insert _ _))]

theorem IsSeparatedFamily.mean_biUnion
    {G : SimpleGraph V} {s : Finset ι} {B : ι → Finset V}
    (h : IsSeparatedFamily G s B) {z : ℝ} (hz : 0 ≤ z) :
    hardCoreMean G (s.biUnion B) z = ∑ i ∈ s, hardCoreMean G (B i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hardCoreMean, hardCoreMomentNumerator, independentSubsets_empty_eq_singleton]
  | @insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi,
      hardCoreMean_disjoint_union G (B i) (s.biUnion B)
        (h.disjoint_biUnion hi) (h.no_edges_biUnion hi) hz]
    rw [ih (h.mono (subset_insert _ _))]

theorem IsSeparatedFamily.independenceNumber_biUnion
    {G : SimpleGraph V} {s : Finset ι} {B : ι → Finset V}
    (h : IsSeparatedFamily G s B) :
    independenceNumberOn G (s.biUnion B) = ∑ i ∈ s, independenceNumberOn G (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
  | @insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi,
      independenceNumberOn_disjoint_union G (B i) (s.biUnion B)
        (h.disjoint_biUnion hi) (h.no_edges_biUnion hi)]
    rw [ih (h.mono (subset_insert _ _))]

theorem IsSeparatedFamily.card_biUnion
    {G : SimpleGraph V} {s : Finset ι} {B : ι → Finset V}
    (h : IsSeparatedFamily G s B) : (s.biUnion B).card = ∑ i ∈ s, (B i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi, card_union_of_disjoint (h.disjoint_biUnion hi)]
    rw [ih (h.mono (subset_insert _ _))]

/-- An actual common-center graph with separated rooted branches. Each
branch may itself be an arbitrary graph at this level. -/
structure IsRootedFanOn (G : SimpleGraph V) (S : Finset V) (c : V)
    (s : Finset ι) (B : ι → Finset V) (root : ι → V) : Prop where
  vertices : S = insert c (s.biUnion B)
  separated : IsSeparatedFamily G s B
  root_mem : ∀ i ∈ s, root i ∈ B i
  center_not_mem : ∀ i ∈ s, c ∉ B i
  center_adj : ∀ i ∈ s, ∀ x ∈ B i, G.Adj c x ↔ x = root i

/-- A spider in actual graph terms. Every branch is a nonempty path
constructed on precisely its vertex set, attached to the common center at
an endpoint. A later classification must produce these witnesses. -/
structure IsSpiderOn (G : SimpleGraph V) (S : Finset V) (c : V)
    (s : Finset ι) (B : ι → Finset V) (root tip : ι → V) (length : ι → ℕ) : Prop
    extends IsRootedFanOn G S c s B root where
  length_pos : ∀ i ∈ s, 0 < length i
  paths : ∀ i ∈ s, PendantPathExtension G {tip i} (tip i)
    (length i - 1) (B i) (root i)

omit [DecidableEq ι] in
theorem IsRootedFanOn.center_mem {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) : c ∈ S := by
  rw [h.vertices]
  exact mem_insert_self _ _

omit [DecidableEq ι] in
theorem IsRootedFanOn.erase_center {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) : S.erase c = s.biUnion B := by
  rw [h.vertices, erase_insert]
  intro hc
  obtain ⟨i, hi, hci⟩ := mem_biUnion.mp hc
  exact h.center_not_mem i hi hci

omit [DecidableEq ι] in
theorem IsRootedFanOn.delete_closed_center {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) :
    S \ closedNeighborhoodIn G S c = s.biUnion fun i => (B i).erase (root i) := by
  ext x
  rw [mem_sdiff_closedNeighborhoodIn, h.vertices]
  simp only [mem_insert, mem_biUnion, mem_erase]
  constructor
  · rintro ⟨rfl | ⟨i, hi, hxi⟩, hxc, hn⟩
    · exact (hxc rfl).elim
    · exact ⟨i, hi, fun he => hn ((h.center_adj i hi x hxi).mpr he), hxi⟩
  · rintro ⟨i, hi, hxr, hxi⟩
    refine ⟨Or.inr ⟨i, hi, hxi⟩, ?_, ?_⟩
    · intro hxc
      exact h.center_not_mem i hi (hxc ▸ hxi)
    · intro hadj
      exact hxr ((h.center_adj i hi x hxi).mp hadj)

theorem IsRootedFanOn.partitionFunction_eq (G : SimpleGraph V) {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) {R : Type*} [CommSemiring R] (z : R) :
    partitionFunction G S z = (∏ i ∈ s, partitionFunction G (B i) z) +
      z * ∏ i ∈ s, partitionFunction G ((B i).erase (root i)) z := by
  rw [partitionFunction_delete_vertex G S h.center_mem z, h.erase_center, h.delete_closed_center,
    h.separated.partitionFunction_biUnion z,
    (h.separated.subsets (fun i _ => erase_subset _ _)).partitionFunction_biUnion z]

theorem IsRootedFanOn.independenceNumber {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) :
    independenceNumberOn G S = max (∑ i ∈ s, independenceNumberOn G (B i))
      ((∑ i ∈ s, independenceNumberOn G ((B i).erase (root i))) + 1) := by
  rw [independenceNumberOn_delete_vertex G S h.center_mem,
    h.erase_center, h.delete_closed_center, h.separated.independenceNumber_biUnion,
    (h.separated.subsets (fun i _ => erase_subset _ _)).independenceNumber_biUnion]

theorem hardCore_first_moment_eq_mean_mul_partition (G : SimpleGraph V)
    (S : Finset V) {z : ℝ} (hz : 0 ≤ z) :
    hardCoreMomentNumerator G S 1 z = hardCoreMean G S z * partitionFunction G S z := by
  have hZ := ne_of_gt (partitionFunction_pos G S hz)
  simp [hardCoreMean, hZ]

theorem IsRootedFanOn.firstMoment {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) {z : ℝ} (hz : 0 ≤ z) :
    hardCoreMomentNumerator G S 1 z =
      (∑ i ∈ s, hardCoreMean G (B i) z) * (∏ i ∈ s, partitionFunction G (B i) z) +
      z * ((∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) z) + 1) *
        (∏ i ∈ s, partitionFunction G ((B i).erase (root i)) z) := by
  rw [hardCore_first_moment_delete_vertex G S h.center_mem z,
    h.erase_center, h.delete_closed_center,
    hardCore_first_moment_eq_mean_mul_partition G _ hz,
    hardCore_first_moment_eq_mean_mul_partition G _ hz,
    h.separated.mean_biUnion hz, h.separated.partitionFunction_biUnion z,
    (h.separated.subsets (fun i _ => erase_subset _ _)).mean_biUnion hz,
    (h.separated.subsets (fun i _ => erase_subset _ _)).partitionFunction_biUnion z]
  ring

theorem IsRootedFanOn.card {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) : S.card = (∑ i ∈ s, (B i).card) + 1 := by
  have hc := card_erase_add_one h.center_mem
  rw [h.erase_center, h.separated.card_biUnion] at hc
  exact hc.symm

/-- First and deleted-first statistics of any actual one-vertex path. -/
theorem hardCore_singleton_statistics (G : SimpleGraph V) (v : V) (z : ℝ) :
    (partitionFunction G {v} z, hardCoreMomentNumerator G {v} 1 z,
      partitionFunction G (({v} : Finset V).erase v) z,
      hardCoreMomentNumerator G (({v} : Finset V).erase v) 1 z) = (1 + z, z, 1, 0) := by
  have hc : ({v} : Finset V) \ closedNeighborhoodIn G {v} v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := mem_sdiff_closedNeighborhoodIn.mp hx
    exact hx'.2.1 (mem_singleton.mp hx'.1)
  have hZ := partitionFunction_delete_vertex G {v} (v := v) (by simp) z
  have hM := hardCore_first_moment_delete_vertex G {v} (v := v) (by simp) z
  rw [hc] at hZ hM
  simp only [erase_singleton, partitionFunction, hardCoreMomentNumerator,
    independentSubsets_empty_eq_singleton, sum_singleton, card_empty,
    Nat.cast_zero, zero_pow (by decide : 1 ≠ 0), pow_zero, mul_one] at hZ hM ⊢
  exact Prod.ext hZ (Prod.ext (by simpa only [zero_add, mul_one] using hM) rfl)

theorem independenceNumberOn_singleton (G : SimpleGraph V) (v : V) :
    independenceNumberOn G {v} = 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro J hJ
    simpa using card_le_card (mem_independentSubsets.mp hJ).1
  · have hmem : ({v} : Finset V) ∈ independentSubsets G {v} := by
      simp [mem_independentSubsets, SimpleGraph.IsIndepSet, Set.Pairwise]
    change 1 ≤ (independentSubsets G {v}).sup Finset.card
    calc
      1 = ({v} : Finset V).card := by simp
      _ ≤ _ := Finset.le_sup hmem

/-- Computable path statistics, obtained from the actual deletion recurrence.
The tuple is Z, M, deleted-root Z, deleted-root M at activity two. -/
def pathBranchStatistics (n : ℕ) : ℝ × ℝ × ℝ × ℝ :=
  pathMomentTransfer 2 (n - 1) (3, 2, 1, 0)

omit [DecidableEq ι] in
theorem IsSpiderOn.branch_statistics {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    (partitionFunction G (B i) (2 : ℝ), hardCoreMomentNumerator G (B i) 1 (2 : ℝ),
      partitionFunction G ((B i).erase (root i)) (2 : ℝ),
      hardCoreMomentNumerator G ((B i).erase (root i)) 1 (2 : ℝ)) =
      pathBranchStatistics (length i) := by
  have ht := (h.paths i hi).moment_transfer 2
  rw [hardCore_singleton_statistics] at ht
  norm_num only at ht
  exact ht

omit [DecidableEq ι] in
theorem IsSpiderOn.branch_card {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    (B i).card = length i := by
  have ht := (h.paths i hi).card_eq
  have hp := h.length_pos i hi
  simp only [card_singleton] at ht
  omega

omit [DecidableEq ι] in
theorem IsSpiderOn.branch_independenceNumbers {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    (independenceNumberOn G (B i), independenceNumberOn G ((B i).erase (root i))) =
      pathCardTransfer (length i - 1) (1, 0) := by
  have ht := (h.paths i hi).card_transfer
  rw [independenceNumberOn_singleton] at ht
  have he : independenceNumberOn G ∅ = 0 := by
    simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
  simpa only [erase_singleton, he] using ht

theorem pathCardTransfer_from_singleton (n : ℕ) :
    pathCardTransfer n (1, 0) = ((n + 2) / 2, (n + 1) / 2) := by
  induction n with
  | zero => norm_num [pathCardTransfer]
  | succ n ih =>
    simp only [pathCardTransfer, ih]
    apply Prod.ext
    · dsimp
      rw [max_eq_right (by omega : (n + 2) / 2 ≤ (n + 1) / 2 + 1)]
      omega
    · dsimp

omit [DecidableEq ι] in
theorem IsSpiderOn.branch_alpha_pair {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) {i : ι} (hi : i ∈ s) :
    (independenceNumberOn G (B i), independenceNumberOn G ((B i).erase (root i))) =
      ((length i + 1) / 2, length i / 2) := by
  have ht := h.branch_independenceNumbers hi
  have hp := h.length_pos i hi
  rw [pathCardTransfer_from_singleton] at ht
  convert ht using 2 <;> omega

theorem IsRootedFanOn.alpha_of_root_state_zero {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root)
    (hstate : ∀ i ∈ s, independenceNumberOn G (B i) =
      independenceNumberOn G ((B i).erase (root i))) :
    independenceNumberOn G S = (∑ i ∈ s, independenceNumberOn G (B i)) + 1 := by
  have hs : (∑ i ∈ s, independenceNumberOn G ((B i).erase (root i))) =
      ∑ i ∈ s, independenceNumberOn G (B i) := sum_congr rfl (fun i hi => (hstate i hi).symm)
  rw [h.independenceNumber, hs, max_eq_right (by omega)]

theorem IsRootedFanOn.alpha_of_root_state_one {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) (hne : s.Nonempty)
    (hstate : ∀ i ∈ s, independenceNumberOn G (B i) =
      independenceNumberOn G ((B i).erase (root i)) + 1) :
    independenceNumberOn G S = ∑ i ∈ s, independenceNumberOn G (B i) := by
  have hs : (∑ i ∈ s, independenceNumberOn G (B i)) =
      (∑ i ∈ s, independenceNumberOn G ((B i).erase (root i))) + s.card := by
    calc
      _ = ∑ i ∈ s, (independenceNumberOn G ((B i).erase (root i)) + 1) :=
        sum_congr rfl hstate
      _ = _ := by rw [sum_add_distrib]; simp
  have hc := card_pos.mpr hne
  rw [h.independenceNumber, max_eq_left (by omega)]

/-- The deleted-root excess keeps the original branch's cardinality and
independence number, as required by the source's short-leg identity. -/
noncomputable def deletedRootExcess (G : SimpleGraph V) (B : Finset V) (v : V) : ℝ :=
  3 * hardCoreMean G (B.erase v) 2 - (independenceNumberOn G B : ℝ) -
    (29 / 60 : ℝ) * B.card

theorem IsRootedFanOn.adjustedMean_identity {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root : ι → V}
    (h : IsRootedFanOn G S c s B root) :
    partitionFunction G S (2 : ℝ) * adjustedMeanPotential G S (independenceNumberOn G S) =
      (∏ i ∈ s, partitionFunction G (B i) (2 : ℝ)) *
        ((∑ i ∈ s, adjustedMeanPotential G (B i) (independenceNumberOn G (B i))) -
          ((independenceNumberOn G S : ℝ) - ∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) -
          29 / 60) +
      2 * (∏ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ)) *
        ((∑ i ∈ s, deletedRootExcess G (B i) (root i)) + 3 -
          ((independenceNumberOn G S : ℝ) - ∑ i ∈ s, (independenceNumberOn G (B i) : ℝ)) -
          29 / 60) := by
  have hz : partitionFunction G S (2 : ℝ) ≠ 0 :=
    ne_of_gt (partitionFunction_pos G S (by norm_num : (0 : ℝ) ≤ 2))
  have hm := h.firstMoment (by norm_num : (0 : ℝ) ≤ 2)
  have hZ := h.partitionFunction_eq G (2 : ℝ)
  have hmu : partitionFunction G S (2 : ℝ) * hardCoreMean G S 2 =
      hardCoreMomentNumerator G S 1 (2 : ℝ) := by
    unfold hardCoreMean
    field_simp
  unfold adjustedMeanPotential deletedRootExcess
  rw [h.card]
  push_cast
  simp only [sum_sub_distrib, ← mul_sum]
  calc
    _ = 3 * hardCoreMomentNumerator G S 1 (2 : ℝ) -
        partitionFunction G S (2 : ℝ) * (independenceNumberOn G S : ℝ) -
        partitionFunction G S (2 : ℝ) * (29 / 60 : ℝ) *
          ((∑ i ∈ s, ((B i).card : ℝ)) + 1) := by nlinarith [hmu]
    _ = _ := by rw [hm, hZ]; ring

/-- A length-based exact scalar, derived below from actual graph statistics.
No restriction on branch count, parity, or branch lengths is imposed here. -/
noncomputable def spiderPotentialScalar (s : Finset ι) (length : ι → ℕ) : ℝ :=
  let P := ∏ i ∈ s, (pathBranchStatistics (length i)).1
  let A := ∏ i ∈ s, (pathBranchStatistics (length i)).2.2.1
  let U := ∑ i ∈ s, (pathBranchStatistics (length i)).2.1 /
    (pathBranchStatistics (length i)).1
  let W := ∑ i ∈ s, (pathBranchStatistics (length i)).2.2.2 /
    (pathBranchStatistics (length i)).2.2.1
  3 * ((U * P + 2 * (W + 1) * A) / (P + 2 * A)) -
    (max (∑ i ∈ s, (length i + 1) / 2) ((∑ i ∈ s, length i / 2) + 1) : ℕ) -
    (29 / 60 : ℝ) * ((∑ i ∈ s, length i) + 1 : ℕ)

/-- This is the actual graph bridge used by finite spider computations.
Positive numerical scores are sufficient only after this graph witness
has been supplied; the theorem does not manufacture a classification. -/
theorem IsSpiderOn.adjustedMean_eq_scalar {G : SimpleGraph V} {S : Finset V} {c : V}
    {s : Finset ι} {B : ι → Finset V} {root tip : ι → V} {length : ι → ℕ}
    (h : IsSpiderOn G S c s B root tip length) :
    adjustedMeanPotential G S (independenceNumberOn G S) = spiderPotentialScalar s length := by
  have hZ : ∀ i ∈ s, partitionFunction G (B i) (2 : ℝ) =
      (pathBranchStatistics (length i)).1 := fun i hi => congrArg Prod.fst (h.branch_statistics hi)
  have hM : ∀ i ∈ s, hardCoreMomentNumerator G (B i) 1 (2 : ℝ) =
      (pathBranchStatistics (length i)).2.1 :=
    fun i hi => congrArg (fun p => p.2.1) (h.branch_statistics hi)
  have hA : ∀ i ∈ s, partitionFunction G ((B i).erase (root i)) (2 : ℝ) =
      (pathBranchStatistics (length i)).2.2.1 :=
    fun i hi => congrArg (fun p => p.2.2.1) (h.branch_statistics hi)
  have hN : ∀ i ∈ s, hardCoreMomentNumerator G ((B i).erase (root i)) 1 (2 : ℝ) =
      (pathBranchStatistics (length i)).2.2.2 :=
    fun i hi => congrArg (fun p => p.2.2.2) (h.branch_statistics hi)
  have hP := prod_congr rfl hZ
  have hD := prod_congr rfl hA
  have hU : (∑ i ∈ s, hardCoreMean G (B i) 2) =
      ∑ i ∈ s, (pathBranchStatistics (length i)).2.1 / (pathBranchStatistics (length i)).1 := by
    apply sum_congr rfl
    intro i hi
    unfold hardCoreMean
    rw [hM i hi, hZ i hi]
  have hW : (∑ i ∈ s, hardCoreMean G ((B i).erase (root i)) 2) =
      ∑ i ∈ s, (pathBranchStatistics (length i)).2.2.2 /
        (pathBranchStatistics (length i)).2.2.1 := by
    apply sum_congr rfl
    intro i hi
    unfold hardCoreMean
    rw [hN i hi, hA i hi]
  have hAlpha : (∑ i ∈ s, independenceNumberOn G (B i)) =
      ∑ i ∈ s, (length i + 1) / 2 :=
    sum_congr rfl (fun i hi => congrArg Prod.fst (h.branch_alpha_pair hi))
  have hAlphaD : (∑ i ∈ s, independenceNumberOn G ((B i).erase (root i))) =
      ∑ i ∈ s, length i / 2 :=
    sum_congr rfl (fun i hi => congrArg Prod.snd (h.branch_alpha_pair hi))
  have hOrder : (∑ i ∈ s, (B i).card) = ∑ i ∈ s, length i :=
    sum_congr rfl (fun _ hi => h.branch_card hi)
  unfold adjustedMeanPotential hardCoreMean spiderPotentialScalar
  rw [h.toIsRootedFanOn.firstMoment (by norm_num : (0 : ℝ) ≤ 2),
    h.toIsRootedFanOn.partitionFunction_eq G (2 : ℝ),
    h.toIsRootedFanOn.independenceNumber, h.toIsRootedFanOn.card,
    hP, hD, hU, hW, hAlpha, hAlphaD, hOrder]

#print axioms IsSeparatedFamily.partitionFunction_biUnion
#print axioms IsSeparatedFamily.mean_biUnion
#print axioms IsRootedFanOn.partitionFunction_eq
#print axioms IsRootedFanOn.independenceNumber
#print axioms IsRootedFanOn.firstMoment
#print axioms IsSpiderOn.branch_statistics
#print axioms IsSpiderOn.branch_independenceNumbers
#print axioms IsSpiderOn.branch_alpha_pair
#print axioms IsRootedFanOn.adjustedMean_identity
#print axioms IsSpiderOn.adjustedMean_eq_scalar
end ForestUnimodality
