import ForestUnimodality.EdgeCounting
import ForestUnimodality.PrivateNeighborBound

/-! Exact edge splitting at an independent set, and its counting consequences. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- Membership of an adjacent endpoint pair. -/
theorem pair_mem_edgePairsOn_iff (G : SimpleGraph V) (S : Finset V) (x y : V) :
    {x, y} ∈ edgePairsOn G S ↔ x ∈ S ∧ y ∈ S ∧ G.Adj x y := by
  classical
  constructor
  · intro hp
    obtain ⟨hsub, _, hbad⟩ := mem_edgePairsOn.mp hp
    refine ⟨hsub (by simp), hsub (by simp), ?_⟩
    by_contra hn
    apply hbad
    intro a ha b hb hab
    simp only [mem_coe, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hn
    · exact fun hyx => hn hyx.symm
    · exact (hab rfl).elim
  · rintro ⟨hx, hy, hxy⟩
    apply mem_edgePairsOn.mpr
    refine ⟨insert_subset hx (singleton_subset_iff.mpr hy), by simp [hxy.ne], ?_⟩
    intro hind
    exact hind (by simp) (by simp) hxy.ne hxy

/-- Every edge in I ∪ Y is either internal to Y or a uniquely oriented edge
from I to Y. This identity does not require the graph to be a forest. -/
theorem edgeCountOn_union_of_indep
    (G : SimpleGraph V) [DecidableRel G.Adj] (I Y : Finset V)
    (hdis : Disjoint I Y) (hI : G.IsIndepSet (I : Set V)) :
    edgeCountOn G (I ∪ Y) = edgeCountOn G Y +
      ∑ i ∈ I, (Y.filter (G.Adj i)).card := by
  classical
  let C := (I ×ˢ Y).filter fun p : V × V => G.Adj p.1 p.2
  let f : V × V → Finset V := fun p => {p.1, p.2}
  have hCmem {i y : V} : (i, y) ∈ C ↔ i ∈ I ∧ y ∈ Y ∧ G.Adj i y := by
    simp [C, and_assoc]
  have hfinj : Set.InjOn f C := by
    rintro ⟨i, y⟩ hp ⟨j, z⟩ hq he
    obtain ⟨hi, hy, _⟩ := hCmem.mp hp
    obtain ⟨hj, hz, _⟩ := hCmem.mp hq
    change ({i, y} : Finset V) = {j, z} at he
    have hieq : i = j ∨ i = z := by
      have h : i ∈ ({j, z} : Finset V) := he ▸ (by simp)
      simpa using h
    have hyeq : y = j ∨ y = z := by
      have h : y ∈ ({j, z} : Finset V) := he ▸ (by simp)
      simpa using h
    have hij : i = j := hieq.resolve_right fun hiz =>
      disjoint_left.mp hdis hi (hiz.symm ▸ hz)
    have hyz : y = z := hyeq.resolve_left fun hyj =>
      disjoint_left.mp hdis hj (hyj ▸ hy)
    exact Prod.ext hij hyz
  have hCcard : C.card = ∑ i ∈ I, (Y.filter (G.Adj i)).card := by
    simp only [C, card_eq_sum_ones, sum_filter, sum_product]
  have hsplit : edgePairsOn G (I ∪ Y) = edgePairsOn G Y ∪ C.image f := by
    ext E
    constructor
    · intro hE
      obtain ⟨_, hcard, _⟩ := mem_edgePairsOn.mp hE
      obtain ⟨x, y, _, rfl⟩ := card_eq_two.mp hcard
      obtain ⟨hx, hy, hxy⟩ := (pair_mem_edgePairsOn_iff G (I ∪ Y) x y).mp hE
      rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
      · exact False.elim (hI hx hy hxy.ne hxy)
      · apply mem_union_right
        exact mem_image.mpr ⟨(x, y), hCmem.mpr ⟨hx, hy, hxy⟩, rfl⟩
      · apply mem_union_right
        exact mem_image.mpr ⟨(y, x), hCmem.mpr ⟨hy, hx, hxy.symm⟩, by simp [f, pair_comm]⟩
      · exact mem_union_left _ ((pair_mem_edgePairsOn_iff G Y x y).mpr ⟨hx, hy, hxy⟩)
    · intro hE
      rcases mem_union.mp hE with hE | hE
      · exact edgePairsOn_mono G subset_union_right hE
      · obtain ⟨⟨i, y⟩, hp, rfl⟩ := mem_image.mp hE
        obtain ⟨hi, hy, hiy⟩ := hCmem.mp hp
        exact (pair_mem_edgePairsOn_iff G (I ∪ Y) i y).mpr
          ⟨mem_union_left _ hi, mem_union_right _ hy, hiy⟩
  have hd : Disjoint (edgePairsOn G Y) (C.image f) := by
    apply disjoint_left.mpr
    intro E hE hC
    obtain ⟨⟨i, y⟩, hp, rfl⟩ := mem_image.mp hC
    obtain ⟨hi, _, _⟩ := hCmem.mp hp
    have hiY := (mem_edgePairsOn.mp hE).1 (show i ∈ f (i, y) by simp [f])
    exact disjoint_left.mp hdis hi hiY
  change (edgePairsOn G (I ∪ Y)).card = _
  rw [hsplit, card_union_of_disjoint hd, card_image_of_injOn hfinj, hCcard]
  rfl

/-- The edge bound for any nonempty finite induced subgraph of a forest. -/
theorem edgeCountOn_add_one_le_card_of_isAcyclic
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hS : S.Nonempty) :
    edgeCountOn G S + 1 ≤ S.card := by
  classical
  letI : Nonempty (↑S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hb := forest_card_edges_add_one_le (G.induce (↑S : Set V))
    (hG.induce (↑S : Set V))
  rw [← edgeCountOn_eq_card_edgeFinset_induce,
    Fintype.card_of_finset' S (fun _ => Iff.rfl)] at hb
  exact hb

/-- Cross edges plus edges internal to Y are bounded by the forest edge bound. -/
theorem forest_cross_edges_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) (I Y : Finset V)
    (hdis : Disjoint I Y) (hI : G.IsIndepSet (I : Set V)) (hne : (I ∪ Y).Nonempty) :
    (∑ i ∈ I, (Y.filter (G.Adj i)).card) + edgeCountOn G Y ≤ I.card + Y.card - 1 := by
  have hb := edgeCountOn_add_one_le_card_of_isAcyclic G hG (I ∪ Y) hne
  rw [edgeCountOn_union_of_indep G I Y hdis hI, card_union_of_disjoint hdis] at hb
  omega

/-- Edges incident to an independent subset are counted only once, hence its
sum of neighbor counts cannot exceed the total number of ambient edges. -/
theorem sum_neighbors_le_edgeCountOn_of_indep
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y K : Finset V)
    (hKY : K ⊆ Y) (hK : G.IsIndepSet (K : Set V)) :
    (∑ k ∈ K, (Y.filter (G.Adj k)).card) ≤ edgeCountOn G Y := by
  classical
  have hd : Disjoint K (Y \ K) := by
    apply disjoint_left.mpr
    intro x hx hxy
    exact (mem_sdiff.mp hxy).2 hx
  have hu : K ∪ (Y \ K) = Y := by
    ext x
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact hKY hx
      · exact hx
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr ⟨hx, hxK⟩
  have hfilter : ∀ k ∈ K, Y.filter (G.Adj k) = (Y \ K).filter (G.Adj k) := by
    intro k hk
    ext y
    simp only [mem_filter, mem_sdiff]
    constructor
    · rintro ⟨hy, hky⟩
      exact ⟨⟨hy, fun hyK => hK hk hyK hky.ne hky⟩, hky⟩
    · exact fun h => ⟨h.1.1, h.2⟩
  have hb := edgeCountOn_union_of_indep G K (Y \ K) hd hK
  rw [hu] at hb
  have hsum : (∑ k ∈ K, (Y.filter (G.Adj k)).card) =
      ∑ k ∈ K, ((Y \ K).filter (G.Adj k)).card := by
    apply sum_congr rfl
    intro k hk
    rw [hfilter k hk]
  rw [hsum, hb]
  exact Nat.le_add_left _ _

#print axioms edgeCountOn_union_of_indep
#print axioms edgeCountOn_add_one_le_card_of_isAcyclic
#print axioms forest_cross_edges_bound
#print axioms sum_neighbors_le_edgeCountOn_of_indep

end ForestUnimodality
