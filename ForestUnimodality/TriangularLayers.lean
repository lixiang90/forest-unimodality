import ForestUnimodality.LayerCoefficients
import ForestUnimodality.MaximumIndependent
import ForestUnimodality.GraphBounds
import Mathlib.Data.Real.Basic

/-! The actual layer counts on the finite certificates' triangular domain.
The coefficient identity requires only maximum independence. The bound v ≤ a
is explicit only where every j-layer is represented by m = 0,...,a-j. -/

namespace ForestUnimodality

open Finset

/-- Computable certificate indices: 1 ≤ j ≤ v and j+m ≤ a. -/
def triangularIndices (a v : ℕ) : Finset (ℕ × ℕ) :=
  ((range (v + 1)) ×ˢ (range (a + 1))).filter
    (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ a)

@[simp] theorem mem_triangularIndices {a v j m : ℕ} :
    (j, m) ∈ triangularIndices a v ↔ 1 ≤ j ∧ j ≤ v ∧ j + m ≤ a := by
  simp only [triangularIndices, mem_filter, mem_product, mem_range]
  omega

/-- A fiber of the triangular domain is exactly its intended m-range. -/
theorem triangularIndices_filter_fst (a v j : ℕ)
    (hj : 1 ≤ j) (hjv : j ≤ v) (hja : j ≤ a) :
    (triangularIndices a v).filter (fun p => p.1 = j) =
      (range (a - j + 1)).image (fun m => (j, m)) := by
  ext p
  rcases p with ⟨j', m⟩
  simp only [mem_filter, mem_triangularIndices, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hj', hjv', hsum⟩, rfl⟩
    exact ⟨m, by omega, rfl, rfl⟩
  · rintro ⟨m', hm', rfl, rfl⟩
    exact ⟨⟨hj, hjv, by omega⟩, rfl⟩

/-- Reindexing a triangular fiber as the finite availability range. -/
theorem sum_triangularIndices_fst {R : Type*} [AddCommMonoid R]
    (a v j : ℕ) (hj : 1 ≤ j) (hjv : j ≤ v) (hja : j ≤ a) (f : ℕ → R) :
    (∑ p ∈ (triangularIndices a v).filter (fun p => p.1 = j), f p.2) =
      ∑ m ∈ range (a - j + 1), f m := by
  rw [triangularIndices_filter_fst a v j hj hjv hja, sum_image]
  intro m _ n _ h
  exact (Prod.mk.inj h).2

variable {V : Type*} [DecidableEq V]

/-- General rectangular-to-triangular reweighting, with the unique zero layer
removed as one explicit term. Every removed actual layer is proved zero. -/
theorem IsMaximumIndependentOn.sum_layers_eq_zero_add_triangular
    {R : Type*} [CommSemiring R] {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (f : ℕ → ℕ → R) :
    (∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : R) * f j m) =
      f 0 I.card + ∑ p ∈ triangularIndices I.card (S \ I).card,
        (layerCount G I (S \ I) p.1 p.2 : R) * f p.1 p.2 := by
  classical
  let rectangle := (range ((S \ I).card + 1)) ×ˢ (range (I.card + 1))
  let weight : ℕ × ℕ → R := fun p =>
    (layerCount G I (S \ I) p.1 p.2 : R) * f p.1 p.2
  have hfirst : rectangle.filter (fun p => p = (0, I.card)) = {(0, I.card)} := by
    ext p
    rcases p with ⟨j, m⟩
    simp only [rectangle, mem_filter, mem_product, mem_range, Prod.mk.injEq,
      mem_singleton]
    omega
  have hsubset : triangularIndices I.card (S \ I).card ⊆
      rectangle.filter (fun p => p ≠ (0, I.card)) := by
    intro p hp
    rcases p with ⟨j, m⟩
    obtain ⟨hj, hjv, hjm⟩ := mem_triangularIndices.mp hp
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ?_⟩
    intro h
    have := (Prod.mk.inj h).1
    omega
  have hrest : (∑ p ∈ rectangle.filter (fun p => p ≠ (0, I.card)), weight p) =
      ∑ p ∈ triangularIndices I.card (S \ I).card, weight p := by
    symm
    apply sum_subset hsubset
    intro p hp hnot
    rcases p with ⟨j, m⟩
    obtain ⟨hpRect, hpne⟩ := mem_filter.mp hp
    obtain ⟨hjv, hma⟩ := mem_product.mp hpRect
    have hjv' := mem_range.mp hjv
    have hma' := mem_range.mp hma
    change (layerCount G I (S \ I) j m : R) * f j m = 0
    by_cases hj : j = 0
    · subst j
      have hmaNe : m ≠ I.card := by intro h; exact hpne (by simp [h])
      rw [layerCount_zero_of_ne G I (S \ I) hmaNe, Nat.cast_zero, zero_mul]
    · have hlarge : I.card < j + m := by
        have hnot' := mt mem_triangularIndices.mpr hnot
        omega
      rw [hI.layerCount_eq_zero_of_card_lt hlarge, Nat.cast_zero, zero_mul]
  have hpartition := sum_filter_add_sum_filter_not rectangle
    (fun p => p = (0, I.card)) weight
  rw [hfirst, sum_singleton, hrest] at hpartition
  have hzero : weight (0, I.card) = f 0 I.card := by
    simp [weight]
  rw [hzero] at hpartition
  simpa only [rectangle, weight, sum_product] using hpartition.symm

/-- Actual independent coefficients on exactly the certificate index set. -/
theorem IsMaximumIndependentOn.countIndependent_cast_eq_triangular
    {R : Type*} [CommSemiring R] {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (k : ℕ) :
    (countIndependent G S k : R) = (I.card.choose k : R) +
      ∑ p ∈ triangularIndices I.card (S \ I).card,
        (layerCount G I (S \ I) p.1 p.2 : R) * (shiftedChoose p.2 p.1 k : R) := by
  rw [countIndependent_cast_eq_layer_sum G S I hI.subset hI.independent]
  simpa only [shiftedChoose_zero_shift] using
    hI.sum_layers_eq_zero_add_triangular (fun j m => (shiftedChoose m j k : R))

/-- Source differences c_k-c_(k-1), with the previous shifted guard retained. -/
theorem IsMaximumIndependentOn.countIndependent_delta_eq_triangular
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (k : ℕ) (_hk : 1 ≤ k) :
    (countIndependent G S k : ℝ) - (countIndependent G S (k - 1) : ℝ) =
      (I.card.choose k : ℝ) - (I.card.choose (k - 1) : ℝ) +
      ∑ p ∈ triangularIndices I.card (S \ I).card,
        (layerCount G I (S \ I) p.1 p.2 : ℝ) *
          ((shiftedChoose p.2 p.1 k : ℝ) - (shiftedChoose p.2 p.1 (k - 1) : ℝ)) := by
  rw [hI.countIndependent_cast_eq_triangular k,
    hI.countIndependent_cast_eq_triangular (k - 1)]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- Triangular support permits truncation of the m-sum for every j. -/
theorem IsMaximumIndependentOn.sum_layerCount_truncated
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (j : ℕ) :
    (∑ m ∈ range (I.card - j + 1), layerCount G I (S \ I) j m) =
      countIndependent G (S \ I) j := by
  rw [← sum_layerCount_eq_countIndependent G I (S \ I) j]
  apply sum_subset
  · exact range_mono (by omega)
  · intro m hm hnot
    have hm' := mem_range.mp hm
    have hnot' : I.card - j + 1 ≤ m := Nat.le_of_not_gt (mt mem_range.mpr hnot)
    apply hI.layerCount_eq_zero_of_card_lt
    omega

/-- Exact mass of each represented triangular layer. -/
theorem IsMaximumIndependentOn.triangular_layer_mass
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (j : ℕ) (hj : 1 ≤ j) (hjv : j ≤ (S \ I).card) :
    (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = j),
      layerCount G I (S \ I) p.1 p.2) = countIndependent G (S \ I) j := by
  calc
    _ = ∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = j),
        layerCount G I (S \ I) j p.2 := by
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := by
      rw [sum_triangularIndices_fst I.card (S \ I).card j hj hjv (hjv.trans hav)]
      exact hI.sum_layerCount_truncated j

/-- Each unnormalized triangular mass is at most W_j = choose(v,j). -/
theorem IsMaximumIndependentOn.triangular_layer_mass_le
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (j : ℕ) (hj : 1 ≤ j) (hjv : j ≤ (S \ I).card) :
    (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = j),
      layerCount G I (S \ I) p.1 p.2) ≤ (S \ I).card.choose j := by
  rw [hI.triangular_layer_mass hav j hj hjv]
  exact countIndependent_le_choose G (S \ I) j

/-- The first unnormalized layer has exactly v singleton sets. -/
theorem IsMaximumIndependentOn.triangular_first_mass
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (hv : 1 ≤ (S \ I).card) :
    (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = 1),
      layerCount G I (S \ I) p.1 p.2) = (S \ I).card := by
  rw [hI.triangular_layer_mass hav 1 (by omega) hv, countIndependent_one]

/-- The normalized actual variable x_(j,m)=t_(j,m)/choose(v,j). -/
noncomputable def normalizedLayer (G : SimpleGraph V) (I Y : Finset V) (j m : ℕ) : ℝ :=
  (layerCount G I Y j m : ℝ) / (Y.card.choose j : ℝ)

theorem normalizedLayer_nonneg (G : SimpleGraph V) (I Y : Finset V) (j m : ℕ) :
    0 ≤ normalizedLayer G I Y j m :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Recovery is exact on every j≤v, where W_j is strictly positive. -/
theorem layerCount_eq_choose_mul_normalizedLayer (G : SimpleGraph V) (I Y : Finset V)
    (j m : ℕ) (hjv : j ≤ Y.card) :
    (layerCount G I Y j m : ℝ) = (Y.card.choose j : ℝ) * normalizedLayer G I Y j m := by
  have hpos : 0 < (Y.card.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hjv
  rw [normalizedLayer, mul_div_cancel₀ _ (ne_of_gt hpos)]

/-- Exact normalized mass on the triangular m-range. -/
theorem IsMaximumIndependentOn.normalized_layer_mass
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (j : ℕ) :
    (∑ m ∈ range (I.card - j + 1), normalizedLayer G I (S \ I) j m) =
      (countIndependent G (S \ I) j : ℝ) / ((S \ I).card.choose j : ℝ) := by
  simp only [normalizedLayer, div_eq_mul_inv, ← sum_mul]
  congr 1
  exact_mod_cast hI.sum_layerCount_truncated j

theorem IsMaximumIndependentOn.normalized_layer_mass_le_one
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (j : ℕ) (hjv : j ≤ (S \ I).card) :
    (∑ m ∈ range (I.card - j + 1), normalizedLayer G I (S \ I) j m) ≤ 1 := by
  rw [hI.normalized_layer_mass]
  have hpos : 0 < ((S \ I).card.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hjv
  apply (div_le_one hpos).mpr
  exact_mod_cast countIndependent_le_choose G (S \ I) j

theorem IsMaximumIndependentOn.normalized_first_mass
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hv : 1 ≤ (S \ I).card) :
    (∑ m ∈ range (I.card - 1 + 1), normalizedLayer G I (S \ I) 1 m) = 1 := by
  rw [hI.normalized_layer_mass, countIndependent_one, Nat.choose_one_right]
  have hvpos : 0 < ((S \ I).card : ℝ) := by exact_mod_cast (by omega : 0 < (S \ I).card)
  exact div_self (ne_of_gt hvpos)

/-- Normalized mass over a filter of the common index set, for row checkers. -/
theorem IsMaximumIndependentOn.normalized_triangular_mass_le_one
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (j : ℕ) (hj : 1 ≤ j) (hjv : j ≤ (S \ I).card) :
    (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = j),
      normalizedLayer G I (S \ I) p.1 p.2) ≤ 1 := by
  have heq : (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = j),
      normalizedLayer G I (S \ I) p.1 p.2) =
      ∑ m ∈ range (I.card - j + 1), normalizedLayer G I (S \ I) j m := by
    calc
      _ = ∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = j),
          normalizedLayer G I (S \ I) j p.2 := by
        apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
      _ = _ := sum_triangularIndices_fst _ _ _ hj hjv (hjv.trans hav) _
  rw [heq]
  exact hI.normalized_layer_mass_le_one j hjv

theorem IsMaximumIndependentOn.normalized_triangular_first_mass
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) (hav : (S \ I).card ≤ I.card)
    (hv : 1 ≤ (S \ I).card) :
    (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = 1),
      normalizedLayer G I (S \ I) p.1 p.2) = 1 := by
  have heq : (∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = 1),
      normalizedLayer G I (S \ I) p.1 p.2) =
      ∑ m ∈ range (I.card - 1 + 1), normalizedLayer G I (S \ I) 1 m := by
    calc
      _ = ∑ p ∈ (triangularIndices I.card (S \ I).card).filter (fun p => p.1 = 1),
          normalizedLayer G I (S \ I) 1 p.2 := by
        apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
      _ = _ := sum_triangularIndices_fst _ _ _ (by omega) hv (hv.trans hav) _
  rw [heq]
  exact hI.normalized_first_mass hv

#print axioms IsMaximumIndependentOn.sum_layers_eq_zero_add_triangular
#print axioms IsMaximumIndependentOn.countIndependent_cast_eq_triangular
#print axioms IsMaximumIndependentOn.countIndependent_delta_eq_triangular
#print axioms IsMaximumIndependentOn.triangular_layer_mass
#print axioms IsMaximumIndependentOn.triangular_layer_mass_le
#print axioms IsMaximumIndependentOn.triangular_first_mass
#print axioms normalizedLayer_nonneg
#print axioms layerCount_eq_choose_mul_normalizedLayer
#print axioms IsMaximumIndependentOn.normalized_layer_mass_le_one
#print axioms IsMaximumIndependentOn.normalized_first_mass
#print axioms IsMaximumIndependentOn.normalized_triangular_mass_le_one
#print axioms IsMaximumIndependentOn.normalized_triangular_first_mass

end ForestUnimodality
