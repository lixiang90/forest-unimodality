import ForestUnimodality.AdjustedMeanPath
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Exact hard-core and independence-number additivity across actual
edge-disconnected vertex sets. The counterexample reduction uses strict
negativity, since a sum of nonnegative component potentials may be zero. -/
namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

theorem independentSubsets_union_of_no_cross_edges {G : SimpleGraph V}
    {A B J K : Finset V}
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y)
    (hJ : J ∈ independentSubsets G A) (hK : K ∈ independentSubsets G B) :
    J ∪ K ∈ independentSubsets G (A ∪ B) := by
  obtain ⟨hJA, hJi⟩ := mem_independentSubsets.mp hJ
  obtain ⟨hKB, hKi⟩ := mem_independentSubsets.mp hK
  refine mem_independentSubsets.mpr ⟨union_subset_union hJA hKB, ?_⟩
  intro x hx y hy hne hadj
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact hJi hx hy hne hadj
  · exact hcross x (hJA hx) y (hKB hy) hadj
  · exact hcross y (hJA hy) x (hKB hx) hadj.symm
  · exact hKi hx hy hne hadj

theorem independentSubsets_inter_left {G : SimpleGraph V} {A B L : Finset V}
    (hL : L ∈ independentSubsets G (A ∪ B)) : L ∩ A ∈ independentSubsets G A := by
  exact mem_independentSubsets.mpr ⟨inter_subset_right,
    (mem_independentSubsets.mp hL).2.mono (coe_subset.mpr inter_subset_left)⟩

theorem independentSubsets_inter_right {G : SimpleGraph V} {A B L : Finset V}
    (hL : L ∈ independentSubsets G (A ∪ B)) : L ∩ B ∈ independentSubsets G B := by
  exact mem_independentSubsets.mpr ⟨inter_subset_right,
    (mem_independentSubsets.mp hL).2.mono (coe_subset.mpr inter_subset_left)⟩

theorem union_inter_split {A B L : Finset V} (hL : L ⊆ A ∪ B) :
    (L ∩ A) ∪ (L ∩ B) = L := by
  ext x
  simp only [mem_union, mem_inter]
  constructor
  · tauto
  · intro hx
    rcases mem_union.mp (hL hx) with ha | hb
    · exact Or.inl ⟨hx, ha⟩
    · exact Or.inr ⟨hx, hb⟩

theorem union_inter_left_of_disjoint {A B J K : Finset V}
    (hd : Disjoint A B) (hJA : J ⊆ A) (hKB : K ⊆ B) : (J ∪ K) ∩ A = J := by
  ext x
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨hx | hx, hA⟩
    · exact hx
    · exact (disjoint_left.mp hd hA (hKB hx)).elim
  · intro hx
    exact ⟨Or.inl hx, hJA hx⟩

theorem sum_independentSubsets_disjoint_union {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) (f : Finset V → R) :
    ∑ L ∈ independentSubsets G (A ∪ B), f L =
      ∑ J ∈ independentSubsets G A, ∑ K ∈ independentSubsets G B, f (J ∪ K) := by
  classical
  rw [← sum_product (f := fun p : Finset V × Finset V => f (p.1 ∪ p.2))]
  apply sum_bij' (fun L _ => (L ∩ A, L ∩ B)) (fun p _ => p.1 ∪ p.2)
  · intro L hL
    exact mem_product.mpr ⟨independentSubsets_inter_left hL, independentSubsets_inter_right hL⟩
  · intro p hp
    exact independentSubsets_union_of_no_cross_edges hcross
      (mem_product.mp hp).1 (mem_product.mp hp).2
  · intro L hL
    exact union_inter_split (mem_independentSubsets.mp hL).1
  · intro p hp
    obtain ⟨hJ, hK⟩ := mem_product.mp hp
    have hJA := (mem_independentSubsets.mp hJ).1
    have hKB := (mem_independentSubsets.mp hK).1
    apply Prod.ext
    · exact union_inter_left_of_disjoint hd hJA hKB
    · rw [union_comm]
      exact union_inter_left_of_disjoint hd.symm hKB hJA
  · intro L hL
    rw [union_inter_split (mem_independentSubsets.mp hL).1]

theorem partitionFunction_disjoint_union {R : Type*} [CommSemiring R]
    (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) (z : R) :
    partitionFunction G (A ∪ B) z = partitionFunction G A z * partitionFunction G B z := by
  unfold partitionFunction
  rw [sum_independentSubsets_disjoint_union G A B hd hcross, sum_mul_sum]
  apply sum_congr rfl
  intro J hJ
  apply sum_congr rfl
  intro K hK
  have hJK : Disjoint J K := hd.mono (mem_independentSubsets.mp hJ).1
    (mem_independentSubsets.mp hK).1
  rw [card_union_of_disjoint hJK, pow_add]

theorem hardCore_first_moment_disjoint_union
    (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) (z : ℝ) :
    hardCoreMomentNumerator G (A ∪ B) 1 z =
      hardCoreMomentNumerator G A 1 z * partitionFunction G B z +
      partitionFunction G A z * hardCoreMomentNumerator G B 1 z := by
  unfold hardCoreMomentNumerator partitionFunction
  simp only [pow_one]
  rw [sum_independentSubsets_disjoint_union G A B hd hcross,
    sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro J hJ
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro K hK
  have hJK : Disjoint J K := hd.mono (mem_independentSubsets.mp hJ).1
    (mem_independentSubsets.mp hK).1
  rw [card_union_of_disjoint hJK, Nat.cast_add, pow_add]
  ring

theorem hardCoreMean_disjoint_union
    (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) {z : ℝ} (hz : 0 ≤ z) :
    hardCoreMean G (A ∪ B) z = hardCoreMean G A z + hardCoreMean G B z := by
  have hZA := ne_of_gt (partitionFunction_pos G A hz)
  have hZB := ne_of_gt (partitionFunction_pos G B hz)
  unfold hardCoreMean
  rw [hardCore_first_moment_disjoint_union G A B hd hcross,
    partitionFunction_disjoint_union G A B hd hcross]
  field_simp

theorem independenceNumberOn_disjoint_union
    (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    independenceNumberOn G (A ∪ B) = independenceNumberOn G A + independenceNumberOn G B := by
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G A
  obtain ⟨J, hJ⟩ := exists_maximumIndependentOn G B
  apply le_antisymm
  · apply Finset.sup_le
    intro K hK
    have ha : (K ∩ A).card ≤ independenceNumberOn G A :=
      Finset.le_sup (independentSubsets_inter_left hK)
    have hb : (K ∩ B).card ≤ independenceNumberOn G B :=
      Finset.le_sup (independentSubsets_inter_right hK)
    have hsplit := union_inter_split (mem_independentSubsets.mp hK).1
    have hdis : Disjoint (K ∩ A) (K ∩ B) := hd.mono inter_subset_right inter_subset_right
    have hcard := card_union_of_disjoint hdis
    rw [hsplit] at hcard
    omega
  · rw [← hI.card_eq_independenceNumberOn, ← hJ.card_eq_independenceNumberOn]
    have hdis : Disjoint I J := hd.mono hI.subset hJ.subset
    rw [← card_union_of_disjoint hdis]
    exact Finset.le_sup (independentSubsets_union_of_no_cross_edges hcross hI.1 hJ.1)

theorem adjustedMeanPotential_disjoint_union
    (G : SimpleGraph V) (A B : Finset V) (hd : Disjoint A B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y) :
    adjustedMeanPotential G (A ∪ B) (independenceNumberOn G (A ∪ B)) =
      adjustedMeanPotential G A (independenceNumberOn G A) +
      adjustedMeanPotential G B (independenceNumberOn G B) := by
  unfold adjustedMeanPotential
  rw [hardCoreMean_disjoint_union G A B hd hcross (by norm_num : (0 : ℝ) ≤ 2),
    independenceNumberOn_disjoint_union G A B hd hcross, card_union_of_disjoint hd]
  push_cast
  ring

@[simp] theorem adjustedMeanPotential_empty (G : SimpleGraph V) :
    adjustedMeanPotential G ∅ (independenceNumberOn G ∅) = 0 := by
  classical
  have he : independentSubsets G (∅ : Finset V) = {∅} := by
    ext J
    simp only [mem_independentSubsets, subset_empty, mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, by simp [SimpleGraph.IsIndepSet, Set.Pairwise]⟩
  simp [adjustedMeanPotential, hardCoreMean, hardCoreMomentNumerator,
    independenceNumberOn, partitionFunction, he]

/-- Any smallest strictly negative adjusted-potential induced subgraph is
connected. Strict negativity is essential: additivity does not rule out
a disconnected graph whose component potentials are all zero. -/
theorem induce_connected_of_minimal_adjustedMean_neg
    (G : SimpleGraph V) (S : Finset V)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) < 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      0 ≤ adjustedMeanPotential G T (independenceNumberOn G T)) :
    (G.induce (S : Set V)).Connected := by
  classical
  have hne : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he, adjustedMeanPotential_empty] at hbad
    exact (lt_irrefl _ hbad)
  obtain ⟨x, hx⟩ := hne
  letI : Nonempty (S : Set V) := ⟨⟨x, hx⟩⟩
  refine { preconnected := ?_ }
  intro u v
  by_contra huv
  let A : Finset V := S.filter fun a => ∃ ha : a ∈ S,
    (G.induce (S : Set V)).Reachable u ⟨a, ha⟩
  let B : Finset V := S \ A
  have hAS : A ⊆ S := filter_subset _ _
  have hBS : B ⊆ S := sdiff_subset
  have huA : u.val ∈ A := mem_filter.mpr ⟨u.property, ⟨u.property, .rfl⟩⟩
  have hvA : v.val ∉ A := by
    intro hv
    obtain ⟨_, hvS, hr⟩ := mem_filter.mp hv
    exact huv hr
  have huB : u.val ∉ B := by
    intro hu
    exact (mem_sdiff.mp hu).2 huA
  have hltA : A.card < S.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hAS, ?_⟩
    intro he
    exact hvA (he.symm ▸ v.property)
  have hltB : B.card < S.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hBS, ?_⟩
    intro he
    exact huB (he.symm ▸ u.property)
  have hd : Disjoint A B := disjoint_sdiff_self_right
  have hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hab
    obtain ⟨haS, haS', hra⟩ := mem_filter.mp ha
    have hbS := hBS hb
    have hadj : (G.induce (S : Set V)).Adj ⟨a, haS'⟩ ⟨b, hbS⟩ := hab
    have hrb := hra.trans hadj.reachable
    exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨hbS, ⟨hbS, hrb⟩⟩)
  have hunion : A ∪ B = S := union_sdiff_of_subset hAS
  have hsum := adjustedMeanPotential_disjoint_union G A B hd hcross
  rw [hunion] at hsum
  have hA := hsmaller A hAS hltA
  have hB := hsmaller B hBS hltB
  linarith

/-- Chosen-maximum interface matching the existing leaf and path pruning
lemmas, now with the strict sign of a genuine counterexample to M. -/
theorem IsMaximumIndependentOn.induce_connected_of_minimal_adjustedMean_neg
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hbad : adjustedMeanPotential G S I.card < 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      ∀ K : Finset V, IsMaximumIndependentOn G T K → 0 ≤ adjustedMeanPotential G T K.card) :
    (G.induce (S : Set V)).Connected := by
  apply ForestUnimodality.induce_connected_of_minimal_adjustedMean_neg G S
  · rwa [← hI.card_eq_independenceNumberOn]
  · intro T hTS hlt
    obtain ⟨K, hK⟩ := exists_maximumIndependentOn G T
    rw [← hK.card_eq_independenceNumberOn]
    exact hsmaller T hTS hlt K hK

/-- A smallest genuine counterexample among induced subgraphs of a forest
is a tree. This closes the forest-to-tree reduction before local pruning. -/
theorem induce_isTree_of_minimal_adjustedMean_neg
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (hbad : adjustedMeanPotential G S (independenceNumberOn G S) < 0)
    (hsmaller : ∀ T : Finset V, T ⊆ S → T.card < S.card →
      0 ≤ adjustedMeanPotential G T (independenceNumberOn G T)) :
    (G.induce (S : Set V)).IsTree :=
  { connected := induce_connected_of_minimal_adjustedMean_neg G S hbad hsmaller
    isAcyclic := hG.induce (S : Set V) }

#print axioms partitionFunction_disjoint_union
#print axioms hardCoreMean_disjoint_union
#print axioms independenceNumberOn_disjoint_union
#print axioms adjustedMeanPotential_disjoint_union
#print axioms induce_connected_of_minimal_adjustedMean_neg
#print axioms IsMaximumIndependentOn.induce_connected_of_minimal_adjustedMean_neg
#print axioms induce_isTree_of_minimal_adjustedMean_neg
end ForestUnimodality
