import ForestUnimodality.ForestMatching

/-!
Restricting a saturating matching gives an exclusion bound: outside vertices
with no neighbor in `L` must be matched to distinct vertices of `I \ L`.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Any adjacency-preserving injection from `Y` into `I` restricts to an
injection from the vertices available after `L` into `I \ L`. -/
theorem exists_injective_available_sdiff
    (G : SimpleGraph V) (Y I L : Finset V)
    (f : (↑Y : Set V) → (↑I : Set V)) (hf : Function.Injective f)
    (hadj : ∀ y, G.Adj y.val (f y).val) :
    ∃ g : (↑(available G Y L) : Set V) → (↑(I \ L) : Set V),
      Function.Injective g := by
  let g : (↑(available G Y L) : Set V) → (↑(I \ L) : Set V) := fun y =>
    ⟨(f ⟨y.val, (available_subset G Y L) y.property⟩).val, by
      apply mem_sdiff.mpr
      refine ⟨(f ⟨y.val, (available_subset G Y L) y.property⟩).property, ?_⟩
      intro hL
      exact (mem_available.mp y.property).2 _ hL
        (hadj ⟨y.val, (available_subset G Y L) y.property⟩)⟩
  refine ⟨g, ?_⟩
  intro y z hyz
  apply Subtype.ext
  have hfyz : f ⟨y.val, (available_subset G Y L) y.property⟩ =
      f ⟨z.val, (available_subset G Y L) z.property⟩ := by
    apply Subtype.ext
    exact congrArg (fun x : (↑(I \ L) : Set V) => x.val) hyz
  exact congrArg (fun x : (↑Y : Set V) => x.val) (hf hfyz)

/-- The fixed-set exclusion bound from a saturating adjacency injection. -/
theorem available_card_le_min_of_injective_adj
    (G : SimpleGraph V) (Y I L : Finset V) (hLI : L ⊆ I)
    (f : (↑Y : Set V) → (↑I : Set V)) (hf : Function.Injective f)
    (hadj : ∀ y, G.Adj y.val (f y).val) :
    (available G Y L).card ≤ min Y.card (I.card - L.card) := by
  obtain ⟨g, hg⟩ := exists_injective_available_sdiff G Y I L f hf hadj
  have hcard : (available G Y L).card ≤ (I \ L).card := by
    have h := Fintype.card_le_of_injective g hg
    rwa [Fintype.card_of_finset' (available G Y L) (fun _ => Iff.rfl),
      Fintype.card_of_finset' (I \ L) (fun _ => Iff.rfl)] at h
  rw [card_sdiff_of_subset hLI] at hcard
  exact le_min (card_le_card (available_subset G Y L)) hcard

/-- A maximum independent subset of a forest gives the exclusion bound for
every subset `L` of that independent set. -/
theorem IsMaximumIndependentOn.available_complement_card_le_min
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (L : Finset V) (hLI : L ⊆ I) :
    (available G (S \ I) L).card ≤ min (S \ I).card (I.card - L.card) := by
  obtain ⟨f, hf, hadj⟩ := hI.exists_injective_adj_of_isAcyclic hG
  exact available_card_le_min_of_injective_adj G (S \ I) I L hLI f hf hadj

/-- A forest's complement of a maximum independent subset is no larger than
that independent subset. -/
theorem IsMaximumIndependentOn.complement_card_le_of_isAcyclic
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) : (S \ I).card ≤ I.card := by
  obtain ⟨f, hf, _⟩ := hI.exists_injective_adj_of_isAcyclic hG
  have h := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_of_finset' (S \ I) (fun _ => Iff.rfl),
    Fintype.card_of_finset' I (fun _ => Iff.rfl)] at h

/-- The same exclusion bound in the truncated form used by extension counts. -/
theorem IsMaximumIndependentOn.available_complement_card_le_truncated
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (L : Finset V) (hLI : L ⊆ I) :
    (available G (S \ I) L).card ≤
      (S \ I).card - (L.card - (I.card - (S \ I).card)) := by
  have hbound := hI.available_complement_card_le_min hG L hLI
  have hsize := hI.complement_card_le_of_isAcyclic hG
  have hLsize := card_le_card hLI
  omega

#print axioms exists_injective_available_sdiff
#print axioms available_card_le_min_of_injective_adj
#print axioms IsMaximumIndependentOn.available_complement_card_le_min
#print axioms IsMaximumIndependentOn.complement_card_le_of_isAcyclic
#print axioms IsMaximumIndependentOn.available_complement_card_le_truncated

end ForestUnimodality
