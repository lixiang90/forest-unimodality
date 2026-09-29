import ForestUnimodality.BinomialSupport
import ForestUnimodality.UnionBound
import ForestUnimodality.EdgeCounting
import ForestUnimodality.CrossEdges

/-! Counting ingredients for the mean inequality with the actual complement
edge count. Natural-number intermediate bounds are cast only with justified
subtraction hypotheses. -/

namespace ForestUnimodality

open Finset

variable {V : Type*} [DecidableEq V]

/-- The full r-subset availability sum counts, for each i, subsets avoiding
all of its neighbors in Y. Independence is not imposed on these subsets. -/
theorem sum_powersetCard_available (G : SimpleGraph V) [DecidableRel G.Adj]
    (I Y : Finset V) (r : ℕ) :
    (∑ J ∈ Y.powersetCard r, (available G I J).card) =
      ∑ i ∈ I, (Y.card - (Y.filter (G.Adj i)).card).choose r := by
  classical
  have hweight (J : Finset V) : (available G I J).card =
      ∑ i ∈ I, if (∀ u ∈ J, ¬G.Adj i u) then 1 else 0 := by
    simp only [sum_boole, Nat.cast_id]
    congr 1
    ext i
    simp only [mem_available, mem_filter]
  simp only [hweight]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have hfilter : ((Y.powersetCard r).filter (fun J => ∀ u ∈ J, ¬G.Adj i u)) =
      (Y.filter fun u => ¬G.Adj i u).powersetCard r := by
    ext J
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hJY, hJcard⟩, hJavoid⟩
      exact ⟨fun u hu => mem_filter.mpr ⟨hJY hu, hJavoid u hu⟩, hJcard⟩
    · rintro ⟨hJ, hJcard⟩
      exact ⟨⟨fun u hu => (mem_filter.mp (hJ hu)).1, hJcard⟩,
        fun u hu => (mem_filter.mp (hJ hu)).2⟩
  have hcard : (Y.filter fun u => ¬G.Adj i u).card =
      Y.card - (Y.filter (G.Adj i)).card := by
    have h := card_filter_add_card_filter_not (s := Y) (p := G.Adj i)
    omega
  simp only [sum_boole, hfilter, card_powersetCard, hcard, Nat.cast_id]

/-- In a forest, an outside edge covers two distinct vertices of a maximum
independent set, hence leaves at most a-2 available vertices. -/
theorem IsMaximumIndependentOn.available_add_two_le_of_edge
    {G : SimpleGraph V} {S I J : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (hJ : J ⊆ S \ I) {u w : V} (hu : u ∈ J) (hw : w ∈ J) (huw : G.Adj u w) :
    (available G I J).card + 2 ≤ I.card := by
  classical
  obtain ⟨x, hxI, hux⟩ := hI.exists_adj_of_mem_sdiff (hJ hu)
  obtain ⟨y, hyI, hwy⟩ := hI.exists_adj_of_mem_sdiff (hJ hw)
  have hxy : x ≠ y := by
    intro heq
    subst y
    have hind := G.isIndepSet_neighborSet_of_triangleFree (hG.cliqueFree (by omega)) x
    exact hind hux.symm hwy.symm huw.ne huw
  have hsubset : ({x, y} : Finset V) ⊆ I \ available G I J := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact mem_sdiff.mpr ⟨hxI, fun hx => (mem_available.mp hx).2 u hu hux.symm⟩
    · have hzy := mem_singleton.mp hz
      subst z
      exact mem_sdiff.mpr ⟨hyI, fun hy => (mem_available.mp hy).2 w hw hwy.symm⟩
  have hcard := card_le_card hsubset
  have hcounts := card_sdiff_add_card_eq_card (available_subset G I J)
  have hpair : ({x, y} : Finset V).card = 2 := by simp [hxy]
  rw [hpair] at hcard
  omega

/-- Every bad outside subset obeys the same two-vertex availability loss. -/
theorem IsMaximumIndependentOn.available_add_two_le_of_bad
    {G : SimpleGraph V} {S I J : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (hJ : J ⊆ S \ I) (hbad : ¬G.IsIndepSet (J : Set V)) :
    (available G I J).card + 2 ≤ I.card := by
  classical
  have hex : ∃ u ∈ J, ∃ w ∈ J, G.Adj u w := by
    by_contra hn
    apply hbad
    intro u hu w hw _ huw
    exact hn ⟨u, hu, w, hw, huw⟩
  obtain ⟨u, hu, w, hw, huw⟩ := hex
  exact hI.available_add_two_le_of_edge hG hJ hu hw huw

/-- Weighted loss from removing all nonindependent r-subsets. -/
theorem IsMaximumIndependentOn.sum_bad_available_le
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r : ℕ) (hr : 2 ≤ r) :
    (∑ J ∈ badSubsetsOn G (S \ I) r, (available G I J).card) ≤
      (I.card - 2) * edgeCountOn G (S \ I) * ((S \ I).card - 2).choose (r - 2) := by
  classical
  calc
    _ ≤ ∑ _J ∈ badSubsetsOn G (S \ I) r, (I.card - 2) := by
      apply sum_le_sum
      intro J hJ
      obtain ⟨hJS, _, hbad⟩ := mem_badSubsetsOn.mp hJ
      have h := hI.available_add_two_le_of_bad hG hJS hbad
      omega
    _ = (badSubsetsOn G (S \ I) r).card * (I.card - 2) := by simp
    _ ≤ (edgeCountOn G (S \ I) * ((S \ I).card - 2).choose (r - 2)) *
        (I.card - 2) := Nat.mul_le_mul_right _
          (card_badSubsetsOn_le_edgeCountOn_mul_choose G (S \ I) r hr)
    _ = _ := by ring

/-- Partitioning all subsets into the independent and bad availability sums. -/
theorem sum_available_independent_add_bad (G : SimpleGraph V)
    (I Y : Finset V) (r : ℕ) :
    (∑ J ∈ independentLayer G Y r, (available G I J).card) +
        (∑ J ∈ badSubsetsOn G Y r, (available G I J).card) =
      ∑ J ∈ Y.powersetCard r, (available G I J).card := by
  classical
  have hind : independentLayer G Y r =
      (Y.powersetCard r).filter (fun J : Finset V => G.IsIndepSet (J : Set V)) := by
    ext J
    simp [mem_independentLayer, and_assoc, and_left_comm, and_comm]
  rw [hind, badSubsetsOn]
  exact sum_filter_add_sum_filter_not _ _ _

/-- Lower bound before excluding nonindependent outside subsets, using the
actual cross-edge count and the actual number of edges inside Y. -/
theorem sum_powersetCard_available_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (I Y : Finset V) (hdis : Disjoint I Y)
    (hI : G.IsIndepSet (I : Set V)) (r : ℕ) (hv : 2 ≤ Y.card) (hr : 2 ≤ r) :
    (I.card : ℝ) * ((Y.card - 2).choose r : ℝ) +
      ((I.card : ℝ) - (Y.card : ℝ) + 1 + (edgeCountOn G Y : ℝ)) *
        ((Y.card - 2).choose (r - 1) : ℝ) ≤
      ∑ J ∈ Y.powersetCard r, ((available G I J).card : ℝ) := by
  classical
  have hpoint (i : V) (_hi : i ∈ I) :=
    choose_complement_support_line Y.card r (Y.filter (G.Adj i)).card hv hr
      (card_le_card (filter_subset _ _))
  have hsum := sum_le_sum hpoint
  have hsum' :
      (I.card : ℝ) * ((Y.card - 2).choose r : ℝ) +
        ((I.card : ℝ) * 2 - ((∑ i ∈ I, (Y.filter (G.Adj i)).card : ℕ) : ℝ)) *
          ((Y.card - 2).choose (r - 1) : ℝ) ≤
        ∑ i ∈ I, ((Y.card - (Y.filter (G.Adj i)).card).choose r : ℝ) := by
    simpa only [sum_add_distrib, ← sum_mul, sum_sub_distrib, sum_const,
      nsmul_eq_mul, Nat.cast_sum] using hsum
  have hne : (I ∪ Y).Nonempty :=
    (card_pos.mp (by omega : 0 < Y.card)).mono subset_union_right
  have hcrossNat := forest_cross_edges_bound G hG I Y hdis hI hne
  have hcross : ((∑ i ∈ I, (Y.filter (G.Adj i)).card : ℕ) : ℝ) +
      (edgeCountOn G Y : ℝ) ≤ (I.card : ℝ) + (Y.card : ℝ) - 1 := by
    have hcast : ((∑ i ∈ I, (Y.filter (G.Adj i)).card : ℕ) : ℝ) +
        (edgeCountOn G Y : ℝ) ≤ ((I.card + Y.card - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcrossNat
    simpa only [Nat.cast_sub (by omega : 1 ≤ I.card + Y.card),
      Nat.cast_add, Nat.cast_one] using hcast
  have hcoef : (I.card : ℝ) - (Y.card : ℝ) + 1 + (edgeCountOn G Y : ℝ) ≤
      (I.card : ℝ) * 2 - ((∑ i ∈ I, (Y.filter (G.Adj i)).card : ℕ) : ℝ) := by
    linarith
  have hid : (∑ J ∈ Y.powersetCard r, ((available G I J).card : ℝ)) =
      ∑ i ∈ I, ((Y.card - (Y.filter (G.Adj i)).card).choose r : ℝ) := by
    exact_mod_cast sum_powersetCard_available G I Y r
  rw [hid]
  apply le_trans _ hsum'
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))

/-- The bad-set loss bound over the reals, preserving real subtraction a-2.
When an outside edge exists, maximum independent sets in forests have a ≥ 2. -/
theorem IsMaximumIndependentOn.sum_bad_available_le_real
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r : ℕ) (hr : 2 ≤ r) :
    (∑ J ∈ badSubsetsOn G (S \ I) r, ((available G I J).card : ℝ)) ≤
      ((I.card : ℝ) - 2) * (edgeCountOn G (S \ I) : ℝ) *
        (((S \ I).card - 2).choose (r - 2) : ℝ) := by
  classical
  have hnat := hI.sum_bad_available_le hG r hr
  by_cases he : edgeCountOn G (S \ I) = 0
  · rw [he, mul_zero, zero_mul] at hnat
    have hzero := Nat.eq_zero_of_le_zero hnat
    have hzero' : (∑ J ∈ badSubsetsOn G (S \ I) r,
        ((available G I J).card : ℝ)) = 0 := by exact_mod_cast hzero
    rw [hzero', he, Nat.cast_zero, mul_zero, zero_mul]
  · have hnonempty : (edgePairsOn G (S \ I)).Nonempty :=
      card_pos.mp (Nat.pos_of_ne_zero he)
    obtain ⟨E, hE⟩ := hnonempty
    obtain ⟨hES, _, hbad⟩ := mem_edgePairsOn.mp hE
    have ha : 2 ≤ I.card := le_trans (Nat.le_add_left _ _)
      (hI.available_add_two_le_of_bad hG hES hbad)
    have hcast : (∑ J ∈ badSubsetsOn G (S \ I) r,
        ((available G I J).card : ℝ)) ≤
        ((I.card - 2 : ℕ) : ℝ) * (edgeCountOn G (S \ I) : ℝ) *
          (((S \ I).card - 2).choose (r - 2) : ℝ) := by exact_mod_cast hnat
    simpa only [Nat.cast_sub ha, Nat.cast_ofNat] using hcast

/-- The manuscript's mean row for genuine layer counts and one common actual
edge count. In particular, its edge coefficient is allowed to be negative. -/
theorem IsMaximumIndependentOn.mean_layer_inequality
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hG : G.IsAcyclic)
    (r : ℕ) (hr : 2 ≤ r) (hv : 2 ≤ (S \ I).card) :
    (I.card : ℝ) * (((S \ I).card - 2).choose r : ℝ) +
      ((I.card : ℝ) - ((S \ I).card : ℝ) + 1) *
        (((S \ I).card - 2).choose (r - 1) : ℝ) +
      ((((S \ I).card - 2).choose (r - 1) : ℝ) -
        ((I.card : ℝ) - 2) * (((S \ I).card - 2).choose (r - 2) : ℝ)) *
        (edgeCountOn G (S \ I) : ℝ) ≤
      ∑ m ∈ range (I.card + 1), (m : ℝ) * (layerCount G I (S \ I) r m : ℝ) := by
  classical
  have hdis : Disjoint I (S \ I) := disjoint_sdiff_self_right
  have hlow := sum_powersetCard_available_lower G hG I (S \ I) hdis hI.independent r hv hr
  have hloss := hI.sum_bad_available_le_real hG r hr
  have hsplit : (∑ J ∈ independentLayer G (S \ I) r, ((available G I J).card : ℝ)) +
      (∑ J ∈ badSubsetsOn G (S \ I) r, ((available G I J).card : ℝ)) =
      ∑ J ∈ (S \ I).powersetCard r, ((available G I J).card : ℝ) := by
    exact_mod_cast sum_available_independent_add_bad G I (S \ I) r
  have hfinal :
      (I.card : ℝ) * (((S \ I).card - 2).choose r : ℝ) +
        ((I.card : ℝ) - ((S \ I).card : ℝ) + 1) *
          (((S \ I).card - 2).choose (r - 1) : ℝ) +
        ((((S \ I).card - 2).choose (r - 1) : ℝ) -
          ((I.card : ℝ) - 2) * (((S \ I).card - 2).choose (r - 2) : ℝ)) *
          (edgeCountOn G (S \ I) : ℝ) ≤
        ∑ J ∈ independentLayer G (S \ I) r, ((available G I J).card : ℝ) := by
    nlinarith
  rw [sum_independentLayer_by_available G I (S \ I) r (fun m => (m : ℝ))] at hfinal
  simpa only [mul_comm] using hfinal

#print axioms sum_powersetCard_available
#print axioms IsMaximumIndependentOn.available_add_two_le_of_edge
#print axioms IsMaximumIndependentOn.available_add_two_le_of_bad
#print axioms IsMaximumIndependentOn.sum_bad_available_le
#print axioms sum_available_independent_add_bad
#print axioms sum_powersetCard_available_lower
#print axioms IsMaximumIndependentOn.sum_bad_available_le_real
#print axioms IsMaximumIndependentOn.mean_layer_inequality

end ForestUnimodality
