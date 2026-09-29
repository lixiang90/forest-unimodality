import ForestUnimodality.ReleaseBounds
import ForestUnimodality.PrivateInequality

/-! The lower deletion-threshold row for actual forest layer counts. -/

namespace ForestUnimodality
open Finset

/-- Integer coefficient in the manuscript's `tail(r,h)` row. -/
def deletionThresholdCoeff (a r h m : ℕ) : ℕ :=
  if h ≤ m then r else if r * h ≤ a + (r - 1) * m then 1 else 0

/-- An integral release vector with sufficient total mass has a coordinate
whose post-deletion availability crosses the threshold. -/
theorem exists_release_crossing {V : Type*} (J : Finset V)
    (p : V → ℕ) (a m r h : ℕ) (hcard : J.card = r) (hr : 1 ≤ r)
    (hstruct : a ≤ m + (r - 1) + ∑ u ∈ J, p u)
    (hthreshold : r * h ≤ a + (r - 1) * m) :
    ∃ u ∈ J, h ≤ m + p u := by
  classical
  by_contra hnone
  push Not at hnone
  have hsum := sum_le_sum (fun u hu => Nat.add_one_le_iff.mpr (hnone u hu))
  have hsum' : r * m + (∑ u ∈ J, p u) + r ≤ r * h := by
    simpa [sum_add_distrib, sum_const, nsmul_eq_mul, hcard] using hsum
  have hrpred : r - 1 + 1 = r := by omega
  nlinarith

variable {V : Type*} [DecidableEq V]

/-- Pointwise threshold count for one independent outside set. -/
theorem IsMaximumIndependentOn.deletionThresholdCoeff_le_count
    {G : SimpleGraph V} {S I J : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (hJ : J ∈ independentSubsets G (S \ I))
    (r : ℕ) (hr : 2 ≤ r) (hJcard : J.card = r) (h : ℕ) :
    deletionThresholdCoeff I.card r h (available G I J).card ≤
      (J.filter fun u => h ≤ (available G I (J.erase u)).card).card := by
  classical
  unfold deletionThresholdCoeff
  split_ifs with hmh hthreshold
  · have hall : J.filter (fun u => h ≤ (available G I (J.erase u)).card) = J := by
      apply filter_eq_self.mpr
      intro u hu
      rw [card_available_erase_eq_add_privateNeighbors G I J hu]
      omega
    rw [hall, hJcard]
  · have hne : J.Nonempty := card_pos.mp (by omega)
    have hbudget := hI.release_cap_le_sum_privateNeighbors hG hJ hne
    have hsupport := hI.card_add_available_le hJ
    have hstruct : I.card ≤ (available G I J).card + (r - 1) +
        ∑ u ∈ J, (privateNeighbors G I J u).card := by
      rw [hJcard] at hbudget hsupport
      omega
    obtain ⟨u, hu, hcross⟩ := exists_release_crossing J
      (fun u => (privateNeighbors G I J u).card) I.card (available G I J).card r h
      hJcard (by omega) hstruct hthreshold
    apply card_pos.mpr
    refine ⟨u, mem_filter.mpr ⟨hu, ?_⟩⟩
    rwa [card_available_erase_eq_add_privateNeighbors G I J hu]
  · exact Nat.zero_le _

/-- Complete lower threshold row. All integer coefficient branches retain
the manuscript's conditions; the summation is over genuine layer counts. -/
theorem IsMaximumIndependentOn.tail_layer_inequality
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (r : ℕ) (hr : 2 ≤ r) (hrY : r ≤ (S \ I).card) (h : ℕ) :
    (∑ m ∈ range (I.card + 1),
      (deletionThresholdCoeff I.card r h m : ℝ) * (layerCount G I (S \ I) r m : ℝ)) ≤
      ((S \ I).card - (r : ℝ) + 1) *
        ∑ m ∈ range (I.card + 1),
          (if h ≤ m then (1 : ℝ) else 0) * (layerCount G I (S \ I) (r - 1) m : ℝ) := by
  classical
  let f : Finset V → ℝ := fun J => if h ≤ (available G I J).card then 1 else 0
  have hpoint : ∀ J ∈ independentLayer G (S \ I) r,
      (deletionThresholdCoeff I.card r h (available G I J).card : ℝ) ≤
        ∑ u ∈ J, f (J.erase u) := by
    intro J hJL
    obtain ⟨hJS, hJI, hJc⟩ := mem_independentLayer.mp hJL
    have hc := hI.deletionThresholdCoeff_le_count hG
      (mem_independentSubsets.mpr ⟨hJS, hJI⟩) r hr hJc h
    have hs : (∑ u ∈ J, f (J.erase u)) =
        ((J.filter fun u => h ≤ (available G I (J.erase u)).card).card : ℝ) := by
      simp [f, sum_boole]
    rw [hs]
    exact_mod_cast hc
  have hweighted := weighted_independent_extension_bound G (S \ I) (r - 1) f
    (by intro J _; dsimp [f]; split_ifs <;> norm_num)
  have hrPred : r - 1 + 1 = r := by omega
  have hfactor : (((S \ I).card - (r - 1) : ℕ) : ℝ) =
      ((S \ I).card : ℝ) - (r : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [hrPred, hfactor] at hweighted
  have hsum := (sum_le_sum hpoint).trans hweighted
  simp only [f] at hsum
  rw [sum_independentLayer_by_available G I (S \ I) r
      (fun m => (deletionThresholdCoeff I.card r h m : ℝ)),
    sum_independentLayer_by_available G I (S \ I) (r - 1)
      (fun m => if h ≤ m then (1 : ℝ) else 0)] at hsum
  simpa only [mul_comm] using hsum

#print axioms exists_release_crossing
#print axioms IsMaximumIndependentOn.deletionThresholdCoeff_le_count
#print axioms IsMaximumIndependentOn.tail_layer_inequality
end ForestUnimodality
