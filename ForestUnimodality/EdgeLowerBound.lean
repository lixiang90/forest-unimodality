import ForestUnimodality.GraphBounds

/-!
Nonindependent r-subsets are covered by the families containing one of their
edges. The resulting union bound is the finite-certificate `edge_lower` row.
The lower binomial index r-2 is used only under the explicit assumption r ≥ 2.
-/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- The nonindependent r-subsets of S. -/
noncomputable def badSubsetsOn (G : SimpleGraph V) (S : Finset V) (r : ℕ) :
    Finset (Finset V) := by
  classical
  exact (S.powersetCard r).filter fun J => ¬G.IsIndepSet (J : Set V)

/-- Edges represented by their two distinct endpoints in the ambient set. -/
noncomputable def edgePairsOn (G : SimpleGraph V) (S : Finset V) : Finset (Finset V) :=
  badSubsetsOn G S 2

/-- The actual number of adjacent unordered pairs contained in S. -/
noncomputable def edgeCountOn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (edgePairsOn G S).card

@[simp] theorem mem_badSubsetsOn {G : SimpleGraph V} {S J : Finset V} {r : ℕ} :
    J ∈ badSubsetsOn G S r ↔ J ⊆ S ∧ J.card = r ∧ ¬G.IsIndepSet (J : Set V) := by
  classical
  simp [badSubsetsOn, and_assoc]

@[simp] theorem mem_edgePairsOn {G : SimpleGraph V} {S E : Finset V} :
    E ∈ edgePairsOn G S ↔ E ⊆ S ∧ E.card = 2 ∧ ¬G.IsIndepSet (E : Set V) :=
  mem_badSubsetsOn

theorem edgePairsOn_mono (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    edgePairsOn G S ⊆ edgePairsOn G T := by
  intro E hE
  obtain ⟨hES, hcard, hbad⟩ := mem_edgePairsOn.mp hE
  exact mem_edgePairsOn.mpr ⟨hES.trans hST, hcard, hbad⟩

/-- Independent and nonindependent r-subsets partition all r-subsets. -/
theorem countIndependent_add_card_badSubsetsOn
    (G : SimpleGraph V) (S : Finset V) (r : ℕ) :
    countIndependent G S r + (badSubsetsOn G S r).card = Nat.choose S.card r := by
  classical
  rw [countIndependent_eq_card_filter_powersetCard]
  simpa only [badSubsetsOn, card_powersetCard] using
    card_filter_add_card_filter_not (s := S.powersetCard r)
      (p := fun J => G.IsIndepSet (J : Set V))

/-- Each two-subset is either an edge or an independent pair. -/
theorem edgeCountOn_eq_choose_sub_countIndependent
    (G : SimpleGraph V) (S : Finset V) :
    edgeCountOn G S = Nat.choose S.card 2 - countIndependent G S 2 := by
  have h := countIndependent_add_card_badSubsetsOn G S 2
  change countIndependent G S 2 + edgeCountOn G S = Nat.choose S.card 2 at h
  omega

/-- Every nonindependent set contains an adjacent unordered pair. -/
theorem exists_edgePairsOn_of_not_indep
    (G : SimpleGraph V) (J : Finset V) (hJ : ¬G.IsIndepSet (J : Set V)) :
    (edgePairsOn G J).Nonempty := by
  classical
  have hex : ∃ x ∈ J, ∃ y ∈ J, G.Adj x y := by
    by_contra hn
    apply hJ
    intro x hx y hy _ hadj
    exact hn ⟨x, hx, y, hy, hadj⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hex
  refine ⟨{x, y}, mem_edgePairsOn.mpr ⟨?_, ?_, ?_⟩⟩
  · exact insert_subset hx (singleton_subset_iff.mpr hy)
  · simp [hxy.ne]
  · intro hind
    exact hind (by simp) (by simp) hxy.ne hxy

/-- Union bound for nonindependent r-subsets, counting the r-subsets containing
each edge pair. Multiple edges in one r-subset only increase the upper bound. -/
theorem card_badSubsetsOn_le_edgeCountOn_mul_choose
    (G : SimpleGraph V) (S : Finset V) (r : ℕ) (hr : 2 ≤ r) :
    (badSubsetsOn G S r).card ≤
      edgeCountOn G S * Nat.choose (S.card - 2) (r - 2) := by
  classical
  let family : Finset V → Finset (Finset V) :=
    fun E => (S.powersetCard r).filter (E ⊆ ·)
  have hcover : badSubsetsOn G S r ⊆ (edgePairsOn G S).biUnion family := by
    intro J hJ
    obtain ⟨hJS, hJcard, hJbad⟩ := mem_badSubsetsOn.mp hJ
    obtain ⟨E, hE⟩ := exists_edgePairsOn_of_not_indep G J hJbad
    apply mem_biUnion.mpr
    refine ⟨E, edgePairsOn_mono G hJS hE, ?_⟩
    apply mem_filter.mpr
    exact ⟨mem_powersetCard.mpr ⟨hJS, hJcard⟩, (mem_edgePairsOn.mp hE).1⟩
  have hfamily (E : Finset V) (hE : E ∈ edgePairsOn G S) :
      (family E).card = Nat.choose (S.card - 2) (r - 2) := by
    obtain ⟨hES, hEcard, _⟩ := mem_edgePairsOn.mp hE
    dsimp [family]
    rw [card_filter_powersetCard_subset E S r hES (by omega), hEcard]
  calc
    (badSubsetsOn G S r).card ≤ ((edgePairsOn G S).biUnion family).card :=
      card_le_card hcover
    _ ≤ ∑ E ∈ edgePairsOn G S, (family E).card := card_biUnion_le
    _ = ∑ _E ∈ edgePairsOn G S, Nat.choose (S.card - 2) (r - 2) :=
      sum_congr rfl hfamily
    _ = edgeCountOn G S * Nat.choose (S.card - 2) (r - 2) := by
      simp [edgeCountOn]

/-- The edge lower bound on the actual independent-set count. -/
theorem choose_le_countIndependent_add_edgeCountOn_mul_choose
    (G : SimpleGraph V) (S : Finset V) (r : ℕ) (hr : 2 ≤ r) :
    Nat.choose S.card r ≤ countIndependent G S r +
      edgeCountOn G S * Nat.choose (S.card - 2) (r - 2) := by
  rw [← countIndependent_add_card_badSubsetsOn G S r]
  exact Nat.add_le_add_left (card_badSubsetsOn_le_edgeCountOn_mul_choose G S r hr) _

/-- The same certificate row with the edge count eliminated using degree two. -/
theorem choose_le_countIndependent_add_count_difference_mul_choose
    (G : SimpleGraph V) (S : Finset V) (r : ℕ) (hr : 2 ≤ r) :
    Nat.choose S.card r ≤ countIndependent G S r +
      (Nat.choose S.card 2 - countIndependent G S 2) *
        Nat.choose (S.card - 2) (r - 2) := by
  rw [← edgeCountOn_eq_choose_sub_countIndependent]
  exact choose_le_countIndependent_add_edgeCountOn_mul_choose G S r hr

#print axioms edgeCountOn_eq_choose_sub_countIndependent
#print axioms card_badSubsetsOn_le_edgeCountOn_mul_choose
#print axioms choose_le_countIndependent_add_edgeCountOn_mul_choose
#print axioms choose_le_countIndependent_add_count_difference_mul_choose

end ForestUnimodality
