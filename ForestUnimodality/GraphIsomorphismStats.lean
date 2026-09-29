import ForestUnimodality.MeanTerminalGraphs

/-! Statistics under isomorphisms of finite induced subgraphs. Existence of an
isomorphism is not asserted: these lemmas transfer already identified shapes. -/

namespace ForestUnimodality

open Finset
open scoped BigOperators

namespace InducedIso

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} {S : Finset V} {T : Finset W}

/-- Map a subset through an isomorphism whose domain is a finite ambient set. -/
def mapSubset (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    (I : Finset V) : Finset W :=
  (I.subtype (fun v => v ∈ S)).map
    (e.toEquiv.toEmbedding.trans (Function.Embedding.subtype _))

omit [DecidableEq W] in
theorem mem_mapSubset (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    (I : Finset V) (w : W) :
    w ∈ mapSubset e I ↔ ∃ x : (S : Set V), x.val ∈ I ∧ (e x).val = w := by
  simp [mapSubset, Finset.mem_map]

omit [DecidableEq W] in
theorem mapSubset_subset (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    (I : Finset V) : mapSubset e I ⊆ T := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := (mem_mapSubset e I w).mp hw
  exact (e x).property

omit [DecidableEq W] in
theorem card_mapSubset (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {I : Finset V} (hI : I ⊆ S) : (mapSubset e I).card = I.card := by
  rw [mapSubset, card_map, card_subtype]
  congr 1
  exact filter_eq_self.mpr hI

theorem symm_mapSubset (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {I : Finset V} (hI : I ⊆ S) : mapSubset e.symm (mapSubset e I) = I := by
  ext v
  constructor
  · intro hv
    obtain ⟨y, hy, hyv⟩ := (mem_mapSubset e.symm _ v).mp hv
    obtain ⟨x, hx, hxy⟩ := (mem_mapSubset e I y.val).mp hy
    have hexy : e x = y := Subtype.ext hxy
    subst y
    have hxv : x.val = v := by simpa using hyv
    exact hxv ▸ hx
  · intro hv
    apply (mem_mapSubset e.symm _ v).mpr
    refine ⟨e ⟨v, hI hv⟩, ?_, by simp⟩
    exact (mem_mapSubset e I _).mpr ⟨⟨v, hI hv⟩, hv, rfl⟩

theorem map_independent (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {I : Finset V} (hI : I ∈ independentSubsets G S) :
    mapSubset e I ∈ independentSubsets H T := by
  obtain ⟨hsub, hind⟩ := mem_independentSubsets.mp hI
  apply mem_independentSubsets.mpr
  refine ⟨mapSubset_subset e I, ?_⟩
  intro u hu v hv huv hadj
  obtain ⟨x, hx, rfl⟩ := (mem_mapSubset e I u).mp hu
  obtain ⟨y, hy, rfl⟩ := (mem_mapSubset e I v).mp hv
  have hxy : x.val ≠ y.val := by
    intro heq
    exact huv (congrArg (fun z => (e z).val) (Subtype.ext heq))
  exact hind hx hy hxy (e.map_rel_iff.mp hadj)

theorem mapSubset_injective_on (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) :
    Set.InjOn (mapSubset e) (independentSubsets G S : Set (Finset V)) := by
  intro I hI J hJ hEq
  have h := congrArg (mapSubset e.symm) hEq
  simpa only [symm_mapSubset e (mem_independentSubsets.mp hI).1,
    symm_mapSubset e (mem_independentSubsets.mp hJ).1] using h

theorem independentSubsets_image (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) :
    (independentSubsets G S).image (mapSubset e) = independentSubsets H T := by
  ext J
  constructor
  · rintro hJ
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hJ
    exact map_independent e hI
  · intro hJ
    exact mem_image.mpr ⟨mapSubset e.symm J, map_independent e.symm hJ,
      symm_mapSubset e.symm (mem_independentSubsets.mp hJ).1⟩

/-- A size-preserving independent-subset bijection transports any statistic
that is a finite sum depending only on cardinality. -/
theorem sum_card_eq {R : Type*} [AddCommMonoid R]
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) (f : ℕ → R) :
    (∑ I ∈ independentSubsets G S, f I.card) =
      ∑ J ∈ independentSubsets H T, f J.card := by
  rw [← independentSubsets_image e, sum_image (mapSubset_injective_on e)]
  exact sum_congr rfl fun I hI => by rw [card_mapSubset e (mem_independentSubsets.mp hI).1]

theorem partitionFunction_eq {R : Type*} [CommSemiring R]
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) (z : R) :
    partitionFunction G S z = partitionFunction H T z := sum_card_eq e (fun k => z^k)

theorem momentNumerator_eq (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    (q : ℕ) (z : ℝ) :
    hardCoreMomentNumerator G S q z = hardCoreMomentNumerator H T q z :=
  sum_card_eq e (fun k => (k : ℝ)^q * z^k)

theorem countIndependent_eq (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) (k : ℕ) :
    countIndependent G S k = countIndependent H T k := by
  have h := sum_card_eq e (fun j => if j = k then (1 : ℕ) else 0)
  simpa [countIndependent, ← sum_filter] using h

theorem independenceNumber_eq (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) :
    independenceNumberOn G S = independenceNumberOn H T := by
  unfold independenceNumberOn
  rw [← independentSubsets_image e, sup_image]
  apply sup_congr rfl
  intro I hI
  exact (card_mapSubset e (mem_independentSubsets.mp hI).1).symm

theorem map_maximum (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {I : Finset V} (hI : IsMaximumIndependentOn G S I) :
    IsMaximumIndependentOn H T (mapSubset e I) := by
  refine ⟨map_independent e hI.1, ?_⟩
  intro J hJ
  have hle := hI.2 _ (map_independent e.symm hJ)
  rwa [card_mapSubset e.symm (mem_independentSubsets.mp hJ).1,
    ← card_mapSubset e hI.subset] at hle

theorem map_maximum_iff (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {I : Finset V} (hI : I ⊆ S) :
    IsMaximumIndependentOn H T (mapSubset e I) ↔ IsMaximumIndependentOn G S I := by
  constructor
  · intro hm
    have h := map_maximum e.symm hm
    rwa [symm_mapSubset e hI] at h
  · exact map_maximum e

omit [DecidableEq V] [DecidableEq W] in
theorem card_eq (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) : S.card = T.card := by
  have h := Fintype.card_congr e.toEquiv
  simpa using h

theorem mean_eq (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) (z : ℝ) :
    hardCoreMean G S z = hardCoreMean H T z := by
  unfold hardCoreMean
  rw [momentNumerator_eq e, partitionFunction_eq e]

theorem adjustedMean_eq (e : G.induce (S : Set V) ≃g H.induce (T : Set W)) :
    adjustedMeanPotential G S (independenceNumberOn G S) =
      adjustedMeanPotential H T (independenceNumberOn H T) := by
  unfold adjustedMeanPotential
  rw [mean_eq e, independenceNumber_eq e, card_eq e]

omit [DecidableEq V] [DecidableEq W] in
private theorem image_ne_root (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) (x : (S : Set V)) (hx : x.val ≠ u) :
    (e x).val ≠ v := by
  intro heq
  have hex : e x = ⟨v, hv⟩ := Subtype.ext heq
  exact hx (congrArg Subtype.val (e.injective (hex.trans hroot.symm)))

/-- Restrict a root-preserving isomorphism after deleting the two roots. -/
def eraseRoot (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) :
    G.induce (S.erase u : Set V) ≃g H.induce (T.erase v : Set W) := by
  have hrootInv : e.symm ⟨v, hv⟩ = ⟨u, hu⟩ := by rw [← hroot]; simp
  refine {
    toFun := fun x => ⟨(e ⟨x.val, (mem_erase.mp x.property).2⟩).val,
      mem_erase.mpr ⟨image_ne_root e hu hv hroot _ (mem_erase.mp x.property).1,
        (e ⟨x.val, (mem_erase.mp x.property).2⟩).property⟩⟩
    invFun := fun y => ⟨(e.symm ⟨y.val, (mem_erase.mp y.property).2⟩).val,
      mem_erase.mpr ⟨image_ne_root e.symm hv hu hrootInv _ (mem_erase.mp y.property).1,
        (e.symm ⟨y.val, (mem_erase.mp y.property).2⟩).property⟩⟩
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_
  }
  · intro x
    apply Subtype.ext
    change (e.symm (e ⟨x.val, (mem_erase.mp x.property).2⟩)).val = x.val
    simp
  · intro y
    apply Subtype.ext
    change (e (e.symm ⟨y.val, (mem_erase.mp y.property).2⟩)).val = y.val
    simp
  · intro x y
    exact e.map_rel_iff

theorem deleted_partitionFunction_eq {R : Type*} [CommSemiring R]
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) (z : R) :
    partitionFunction G (S.erase u) z = partitionFunction H (T.erase v) z :=
  partitionFunction_eq (eraseRoot e hu hv hroot) z

theorem deleted_momentNumerator_eq
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) (q : ℕ) (z : ℝ) :
    hardCoreMomentNumerator G (S.erase u) q z =
      hardCoreMomentNumerator H (T.erase v) q z :=
  momentNumerator_eq (eraseRoot e hu hv hroot) q z

theorem deleted_independenceNumber_eq
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) :
    independenceNumberOn G (S.erase u) = independenceNumberOn H (T.erase v) :=
  independenceNumber_eq (eraseRoot e hu hv hroot)

theorem deleted_countIndependent_eq
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) (k : ℕ) :
    countIndependent G (S.erase u) k = countIndependent H (T.erase v) k :=
  countIndependent_eq (eraseRoot e hu hv hroot) k

theorem rootRatio_eq
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) (z : ℝ) :
    partitionFunction G S z / partitionFunction G (S.erase u) z =
      partitionFunction H T z / partitionFunction H (T.erase v) z := by
  rw [partitionFunction_eq e, deleted_partitionFunction_eq e hu hv hroot]

theorem deletedExcess_eq
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) :
    3 * hardCoreMean G (S.erase u) 2 - (independenceNumberOn G S : ℝ) -
        29 * (S.card : ℝ) / 60 =
      3 * hardCoreMean H (T.erase v) 2 - (independenceNumberOn H T : ℝ) -
        29 * (T.card : ℝ) / 60 := by
  rw [mean_eq (eraseRoot e hu hv hroot), independenceNumber_eq e, card_eq e]

theorem rootState_eq
    (e : G.induce (S : Set V) ≃g H.induce (T : Set W))
    {u : V} {v : W} (hu : u ∈ S) (hv : v ∈ T)
    (hroot : e ⟨u, hu⟩ = ⟨v, hv⟩) :
    independenceNumberOn G S - independenceNumberOn G (S.erase u) =
      independenceNumberOn H T - independenceNumberOn H (T.erase v) := by
  rw [independenceNumber_eq e, deleted_independenceNumber_eq e hu hv hroot]

/-- Convenience identification of a finite graph with its full induced graph. -/
def intoUniv [Fintype W] (H : SimpleGraph W) :
    H ≃g H.induce ((univ : Finset W) : Set W) where
  toFun := fun w => ⟨w, mem_univ w⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_rel_iff' := Iff.rfl

/-- The scalar interface used by the terminal-fan closure, now attached to an
actual finite rooted induced subgraph. -/
structure BranchParameters (G : SimpleGraph V) (S : Finset V) (root : V) (i : Fin 8) : Prop where
  root_mem : root ∈ S
  order_eq : S.card = MeanTerminalGraphs.branchOrder i
  ratio_eq : partitionFunction G S (2 : ℝ) /
    partitionFunction G (S.erase root) (2 : ℝ) = (MeanTerminalClosure.branchRatio i.val : ℝ)
  excess_eq : adjustedMeanPotential G S (independenceNumberOn G S) =
    (MeanTerminalClosure.branchExcess i.val : ℝ)
  deleted_excess_eq : 3 * hardCoreMean G (S.erase root) 2 -
    (independenceNumberOn G S : ℝ) - 29 * (S.card : ℝ) / 60 =
      (MeanTerminalClosure.branchDeletedExcess i.val : ℝ)
  root_state_zero : independenceNumberOn G S = independenceNumberOn G (S.erase root)

/-- A supplied root-preserving shape isomorphism gives the complete eight-type
parameter interface. This theorem does not assume or prove a classification
asserting that every branch has such an isomorphism. -/
theorem branchParameters_of_iso (i : Fin 8)
    (e : G.induce (S : Set V) ≃g MeanTerminalGraphs.branchGraph i)
    {root : V} (hroot : root ∈ S)
    (he : e ⟨root, hroot⟩ = MeanTerminalGraphs.branchRoot i) :
    BranchParameters G S root i := by
  let ei := e.trans (intoUniv (MeanTerminalGraphs.branchGraph i))
  have hr : ei ⟨root, hroot⟩ =
      ⟨MeanTerminalGraphs.branchRoot i, mem_univ _⟩ := by
    apply Subtype.ext
    exact he
  refine ⟨hroot, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using card_eq ei
  · rw [rootRatio_eq ei hroot (mem_univ _) hr]
    exact MeanTerminalGraphs.actual_branch_ratio i
  · rw [adjustedMean_eq ei]
    exact MeanTerminalGraphs.actual_branch_excess i
  · rw [deletedExcess_eq ei hroot (mem_univ _) hr]
    exact MeanTerminalGraphs.actual_branch_deleted_excess i
  · rw [independenceNumber_eq ei, deleted_independenceNumber_eq ei hroot (mem_univ _) hr]
    exact MeanTerminalGraphs.actual_branch_root_state_zero i

#print axioms independentSubsets_image
#print axioms partitionFunction_eq
#print axioms countIndependent_eq
#print axioms independenceNumber_eq
#print axioms adjustedMean_eq
#print axioms deleted_partitionFunction_eq
#print axioms map_maximum_iff
#print axioms branchParameters_of_iso

end InducedIso
end ForestUnimodality
