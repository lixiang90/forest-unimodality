import ForestUnimodality.ReleaseUpperPointwise
import ForestUnimodality.ExtensionLowerBound

/-! Reverse deletion rows for actual layer counts. The multiplier initially
uses the actual complement edge count; a proved larger edge budget may weaken it. -/

namespace ForestUnimodality
open Finset

def releaseUpperCoeff (a r h m : ℕ) : ℕ :=
  releaseUpperEnvelope r m h (a - m - r + 1) (a - m)

def thresholdUpperCoeff (a r h m : ℕ) : ℕ :=
  thresholdUpperEnvelope r m h (a - m - r + 1) (a - m)

theorem cast_nat_sub_eq_max (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - (b : ℝ)) := by
  by_cases hab : b ≤ a
  · rw [Nat.cast_sub hab]
    symm
    apply max_eq_right
    exact sub_nonneg.mpr (by exact_mod_cast hab)
  · have hab' : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le hab', Nat.cast_zero]
    symm
    apply max_eq_left
    exact sub_nonpos.mpr (by exact_mod_cast hab')

variable {V : Type*} [DecidableEq V]

theorem IsMaximumIndependentOn.sum_release_excess_le_coeff
    {G : SimpleGraph V} {S I J : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hJ : J ∈ independentSubsets G (S \ I)) (r : ℕ) (hr : 1 ≤ r)
    (hJcard : J.card = r) (h : ℕ) :
    (∑ u ∈ J, ((available G I (J.erase u)).card - h)) ≤
      releaseUpperCoeff I.card r h (available G I J).card := by
  classical
  have hsupport := hI.card_add_available_le hJ
  rw [hJcard] at hsupport
  have hL : 0 < I.card - (available G I J).card - r + 1 := by omega
  have hD : I.card - (available G I J).card ≤
      r * (I.card - (available G I J).card - r + 1) := by
    have hsub : I.card - (available G I J).card - r + r =
        I.card - (available G I J).card := by omega
    have hm := Nat.mul_le_mul_right (I.card - (available G I J).card - r) hr
    nlinarith
  have hcap : ∀ u ∈ J, (privateNeighbors G I J u).card ≤
      I.card - (available G I J).card - r + 1 := by
    intro u hu
    simpa only [hJcard] using hI.privateNeighbors_card_le_release_cap hJ hu
  have hsum := sum_privateNeighbors_card_le_covered G I J
  have hb := sum_release_excess_le_envelope J (fun u => (privateNeighbors G I J u).card)
    r (available G I J).card h _ _ hJcard hL hD hcap hsum
  have heq : (∑ u ∈ J, ((available G I (J.erase u)).card - h)) =
      ∑ u ∈ J, ((available G I J).card + (privateNeighbors G I J u).card - h) := by
    apply sum_congr rfl
    intro u hu
    rw [card_available_erase_eq_add_privateNeighbors G I J hu]
  rw [heq]
  exact hb

theorem IsMaximumIndependentOn.card_release_threshold_le_coeff
    {G : SimpleGraph V} {S I J : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hJ : J ∈ independentSubsets G (S \ I)) (r : ℕ) (hJcard : J.card = r) (h : ℕ) :
    (J.filter fun u => h ≤ (available G I (J.erase u)).card).card ≤
      thresholdUpperCoeff I.card r h (available G I J).card := by
  classical
  have hcap : ∀ u ∈ J, (privateNeighbors G I J u).card ≤
      I.card - (available G I J).card - r + 1 := by
    intro u hu
    simpa only [hJcard] using hI.privateNeighbors_card_le_release_cap hJ hu
  have hsum := sum_privateNeighbors_card_le_covered G I J
  have hb := card_release_threshold_le_envelope J (fun u => (privateNeighbors G I J u).card)
    r (available G I J).card h _ _ hJcard hcap hsum
  have heq : J.filter (fun u => h ≤ (available G I (J.erase u)).card) =
      J.filter (fun u => h ≤ (available G I J).card + (privateNeighbors G I J u).card) := by
    apply filter_congr
    intro u hu
    rw [card_available_erase_eq_add_privateNeighbors G I J hu]
  rw [heq]
  exact hb

/-- Reverse excess row with the actual edge count. It needs no forest
assumption once a maximum independent set and the edge count are available. -/
theorem IsMaximumIndependentOn.release_upper_layer_actual_edges
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 2 ≤ r) (h : ℕ) :
    (((S \ I).card - (r - 1) - edgeCountOn G (S \ I) : ℕ) : ℝ) *
        (∑ m ∈ range (I.card + 1), max 0 ((m : ℝ) - (h : ℝ)) *
          (layerCount G I (S \ I) (r - 1) m : ℝ)) ≤
      ∑ m ∈ range (I.card + 1),
        (releaseUpperCoeff I.card r h m : ℝ) * (layerCount G I (S \ I) r m : ℝ) := by
  classical
  let f : Finset V → ℝ := fun J => max 0 (((available G I J).card : ℝ) - (h : ℝ))
  have hlow := weighted_independent_extension_lower_bound G (S \ I) (r - 1) f
    (fun _ _ => le_max_left _ _)
  have hrPred : r - 1 + 1 = r := by omega
  rw [hrPred] at hlow
  have hpoint : ∀ J ∈ independentLayer G (S \ I) r,
      (∑ u ∈ J, f (J.erase u)) ≤ (releaseUpperCoeff I.card r h (available G I J).card : ℝ) := by
    intro J hJL
    obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJL
    have hb := hI.sum_release_excess_le_coeff (mem_independentSubsets.mpr ⟨hJS, hJI⟩)
      r (by omega) hJc h
    have hb' := (Nat.cast_le (α := ℝ)).mpr hb
    simpa only [Nat.cast_sum, cast_nat_sub_eq_max, f] using hb'
  have hsum := hlow.trans (sum_le_sum hpoint)
  simp only [f] at hsum
  rw [sum_independentLayer_by_available G I (S \ I) (r - 1)
      (fun m => max 0 ((m : ℝ) - (h : ℝ))),
    sum_independentLayer_by_available G I (S \ I) r
      (fun m => (releaseUpperCoeff I.card r h m : ℝ))] at hsum
  simpa only [mul_comm] using hsum

/-- Reverse threshold row, retaining integer thresholds and actual edges. -/
theorem IsMaximumIndependentOn.tail_upper_layer_actual_edges
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 2 ≤ r) (h : ℕ) :
    (((S \ I).card - (r - 1) - edgeCountOn G (S \ I) : ℕ) : ℝ) *
        (∑ m ∈ range (I.card + 1), (if h ≤ m then (1 : ℝ) else 0) *
          (layerCount G I (S \ I) (r - 1) m : ℝ)) ≤
      ∑ m ∈ range (I.card + 1),
        (thresholdUpperCoeff I.card r h m : ℝ) * (layerCount G I (S \ I) r m : ℝ) := by
  classical
  let f : Finset V → ℝ := fun J => if h ≤ (available G I J).card then 1 else 0
  have hlow := weighted_independent_extension_lower_bound G (S \ I) (r - 1) f
    (by intro J _; dsimp [f]; split_ifs <;> norm_num)
  have hrPred : r - 1 + 1 = r := by omega
  rw [hrPred] at hlow
  have hpoint : ∀ J ∈ independentLayer G (S \ I) r,
      (∑ u ∈ J, f (J.erase u)) ≤ (thresholdUpperCoeff I.card r h (available G I J).card : ℝ) := by
    intro J hJL
    obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJL
    have hb := hI.card_release_threshold_le_coeff (mem_independentSubsets.mpr ⟨hJS, hJI⟩)
      r hJc h
    have heq : (∑ u ∈ J, f (J.erase u)) =
        ((J.filter fun u => h ≤ (available G I (J.erase u)).card).card : ℝ) := by
      simp [f, sum_boole]
    rw [heq]
    exact_mod_cast hb
  have hsum := hlow.trans (sum_le_sum hpoint)
  simp only [f] at hsum
  rw [sum_independentLayer_by_available G I (S \ I) (r - 1)
      (fun m => if h ≤ m then (1 : ℝ) else 0),
    sum_independentLayer_by_available G I (S \ I) r
      (fun m => (thresholdUpperCoeff I.card r h m : ℝ))] at hsum
  simpa only [mul_comm] using hsum

/-- A proved upper edge budget weakens the actual-edge reverse excess row. -/
theorem IsMaximumIndependentOn.release_upper_layer_of_edge_budget
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 2 ≤ r) (h E : ℕ) (hE : edgeCountOn G (S \ I) ≤ E) :
    (((S \ I).card - (r - 1) - E : ℕ) : ℝ) *
        (∑ m ∈ range (I.card + 1), max 0 ((m : ℝ) - (h : ℝ)) *
          (layerCount G I (S \ I) (r - 1) m : ℝ)) ≤
      ∑ m ∈ range (I.card + 1),
        (releaseUpperCoeff I.card r h m : ℝ) * (layerCount G I (S \ I) r m : ℝ) := by
  have hfactor : (((S \ I).card - (r - 1) - E : ℕ) : ℝ) ≤
      (((S \ I).card - (r - 1) - edgeCountOn G (S \ I) : ℕ) : ℝ) := by
    exact_mod_cast (show (S \ I).card - (r - 1) - E ≤
      (S \ I).card - (r - 1) - edgeCountOn G (S \ I) by omega)
  have hnonneg : 0 ≤ ∑ m ∈ range (I.card + 1),
      max 0 ((m : ℝ) - (h : ℝ)) * (layerCount G I (S \ I) (r - 1) m : ℝ) :=
    sum_nonneg fun _ _ => mul_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_right hfactor hnonneg).trans
    (hI.release_upper_layer_actual_edges r hr h)

/-- The same budget weakening for threshold indicators. -/
theorem IsMaximumIndependentOn.tail_upper_layer_of_edge_budget
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (r : ℕ) (hr : 2 ≤ r) (h E : ℕ) (hE : edgeCountOn G (S \ I) ≤ E) :
    (((S \ I).card - (r - 1) - E : ℕ) : ℝ) *
        (∑ m ∈ range (I.card + 1), (if h ≤ m then (1 : ℝ) else 0) *
          (layerCount G I (S \ I) (r - 1) m : ℝ)) ≤
      ∑ m ∈ range (I.card + 1),
        (thresholdUpperCoeff I.card r h m : ℝ) * (layerCount G I (S \ I) r m : ℝ) := by
  have hfactor : (((S \ I).card - (r - 1) - E : ℕ) : ℝ) ≤
      (((S \ I).card - (r - 1) - edgeCountOn G (S \ I) : ℕ) : ℝ) := by
    exact_mod_cast (show (S \ I).card - (r - 1) - E ≤
      (S \ I).card - (r - 1) - edgeCountOn G (S \ I) by omega)
  have hnonneg : 0 ≤ ∑ m ∈ range (I.card + 1),
      (if h ≤ m then (1 : ℝ) else 0) * (layerCount G I (S \ I) (r - 1) m : ℝ) := by
    apply sum_nonneg
    intro m _
    split_ifs <;> positivity
  exact (mul_le_mul_of_nonneg_right hfactor hnonneg).trans
    (hI.tail_upper_layer_actual_edges r hr h)

#print axioms IsMaximumIndependentOn.sum_release_excess_le_coeff
#print axioms IsMaximumIndependentOn.card_release_threshold_le_coeff
#print axioms IsMaximumIndependentOn.release_upper_layer_actual_edges
#print axioms IsMaximumIndependentOn.tail_upper_layer_actual_edges
#print axioms IsMaximumIndependentOn.release_upper_layer_of_edge_budget
#print axioms IsMaximumIndependentOn.tail_upper_layer_of_edge_budget
end ForestUnimodality
