import ForestUnimodality.StarUpperBound
import ForestUnimodality.SparseComplement
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
The finite-certificate `edge_upper` row. The actual edge count is retained
throughout: the star bound loses a discrete concave binomial difference,
whose chord at D0 linearizes the bound in that same edge count.
-/

namespace ForestUnimodality

open Finset

/-- Initial averages of a decreasing sequence dominate all longer averages,
stated without division so that the empty prefix is included. -/
theorem antitone_prefix_sum_mul_le (f : ℕ → ℝ) (hf : Antitone f)
    (e D : ℕ) (he : e ≤ D) :
    (e : ℝ) * (∑ i ∈ range D, f i) ≤ (D : ℝ) * ∑ i ∈ range e, f i := by
  induction D, he using Nat.le_induction with
  | base => exact le_refl _
  | succ D he ih =>
    have hlast : (e : ℝ) * f D ≤ ∑ i ∈ range e, f i := by
      calc
        (e : ℝ) * f D = ∑ _i ∈ range e, f D := by simp
        _ ≤ ∑ i ∈ range e, f i := by
          apply sum_le_sum
          intro i hi
          exact hf (by have := mem_range.mp hi; omega)
    rw [sum_range_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- A binomial difference is a sum of consecutive decreasing increments. -/
theorem binomial_loss_eq_sum (n d q : ℕ) (hd : d ≤ n) :
    (Nat.choose n (q + 1) : ℝ) - (Nat.choose (n - d) (q + 1) : ℝ) =
      ∑ i ∈ range d, (Nat.choose (n - i - 1) q : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd' : d ≤ n := by omega
    have hp := Nat.choose_succ_succ' (n - d - 1) q
    have htop : n - d - 1 + 1 = n - d := by omega
    rw [htop] at hp
    have hpR : (Nat.choose (n - d) (q + 1) : ℝ) =
        (Nat.choose (n - d - 1) q : ℝ) + (Nat.choose (n - d - 1) (q + 1) : ℝ) := by
      exact_mod_cast hp
    have hsub : n - (d + 1) = n - d - 1 := by omega
    rw [sum_range_succ, ← ih hd', hsub]
    linarith

/-- The nonnegative gap appearing in the linear fixed-edge-count row. -/
def edgeUpperGap (v D r : ℕ) : ℕ :=
  Nat.choose (v - 1) (r - 1) - Nat.choose (v - D - 1) (r - 1)

theorem cast_edgeUpperGap (v D r : ℕ) :
    (edgeUpperGap v D r : ℝ) = (Nat.choose (v - 1) (r - 1) : ℝ) -
      (Nat.choose (v - D - 1) (r - 1) : ℝ) := by
  unfold edgeUpperGap
  rw [Nat.cast_sub (Nat.choose_le_choose _ (by omega))]

/-- The chord inequality for the discrete concave binomial loss. -/
theorem edgeUpperGap_chord (v e D r : ℕ) (he : e ≤ D) (hD : D ≤ v - 1)
    (hr : 2 ≤ r) :
    (e : ℝ) * (edgeUpperGap v D r : ℝ) ≤
      (D : ℝ) * (edgeUpperGap v e r : ℝ) := by
  let f : ℕ → ℝ := fun i => (Nat.choose (v - 1 - i - 1) (r - 2) : ℝ)
  have hf : Antitone f := by
    intro i j hij
    dsimp [f]
    exact_mod_cast Nat.choose_le_choose (r - 2) (show v - 1 - j - 1 ≤ v - 1 - i - 1 by omega)
  have h := antitone_prefix_sum_mul_le f hf e D he
  have he' : e ≤ v - 1 := he.trans hD
  have hr' : r - 2 + 1 = r - 1 := by omega
  have heSub : v - 1 - e = v - e - 1 := by omega
  have hDSub : v - 1 - D = v - D - 1 := by omega
  rw [cast_edgeUpperGap, cast_edgeUpperGap]
  rw [← hr', ← hDSub, ← heSub]
  rw [binomial_loss_eq_sum _ _ _ hD, binomial_loss_eq_sum _ _ _ he']
  exact h

variable {V : Type*} [DecidableEq V]

/-- The star bound stated as a loss from the unrestricted binomial coefficient. -/
theorem countIndependent_add_edgeUpperGap_le_choose
    (G : SimpleGraph V) (hG : G.IsAcyclic) (Y : Finset V) (hY : Y.Nonempty)
    (r : ℕ) (hr : 1 ≤ r) :
    (countIndependent G Y r : ℝ) + (edgeUpperGap Y.card (edgeCountOn G Y) r : ℝ) ≤
      (Nat.choose Y.card r : ℝ) := by
  have hs := countIndependent_le_choose_add_shiftedChoose G hG Y hY r
  rw [shiftedChoose_of_le _ hr] at hs
  have hsR : (countIndependent G Y r : ℝ) ≤
      (Nat.choose (Y.card - 1) r : ℝ) +
        (Nat.choose (Y.card - edgeCountOn G Y - 1) (r - 1) : ℝ) := by
    exact_mod_cast hs
  have hp := Nat.choose_succ_succ' (Y.card - 1) (r - 1)
  have hcard : Y.card - 1 + 1 = Y.card := by have := card_pos.mpr hY; omega
  have hr' : r - 1 + 1 = r := by omega
  rw [hcard, hr'] at hp
  have hpR : (Nat.choose Y.card r : ℝ) =
      (Nat.choose (Y.card - 1) (r - 1) : ℝ) + (Nat.choose (Y.card - 1) r : ℝ) := by
    exact_mod_cast hp
  rw [cast_edgeUpperGap]
  linarith

/-- The complete real `edge_upper` inequality for the same actual edge count
that appears in the degree-two coefficient identity. -/
theorem countIndependent_edge_upper
    (G : SimpleGraph V) (hG : G.IsAcyclic) (Y : Finset V) (hY : Y.Nonempty)
    (D r : ℕ) (hDpos : 1 ≤ D) (heD : edgeCountOn G Y ≤ D) (hD : D ≤ Y.card - 1)
    (hr : 2 ≤ r) :
    (D : ℝ) * (countIndependent G Y r : ℝ) -
        (edgeUpperGap Y.card D r : ℝ) * (countIndependent G Y 2 : ℝ) ≤
      (D : ℝ) * (Nat.choose Y.card r : ℝ) -
        (edgeUpperGap Y.card D r : ℝ) * (Nat.choose Y.card 2 : ℝ) := by
  have hs := countIndependent_add_edgeUpperGap_le_choose G hG Y hY r (by omega)
  have hc := edgeUpperGap_chord Y.card (edgeCountOn G Y) D r heD hD hr
  have heNat := countIndependent_add_card_badSubsetsOn G Y 2
  change countIndependent G Y 2 + edgeCountOn G Y = Nat.choose Y.card 2 at heNat
  have heR : (countIndependent G Y 2 : ℝ) + (edgeCountOn G Y : ℝ) =
      (Nat.choose Y.card 2 : ℝ) := by exact_mod_cast heNat
  have hDnonneg : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hs hDnonneg
  nlinarith

/-- When the edge budget is zero, the ordinary unrestricted count bound
supplies the corresponding row directly. -/
theorem countIndependent_edge_upper_zero_budget
    (G : SimpleGraph V) (Y : Finset V) (r : ℕ) :
    (countIndependent G Y r : ℝ) ≤ (Nat.choose Y.card r : ℝ) := by
  exact_mod_cast countIndependent_le_choose G Y r

/-- The certificate's canonical budget, for the same edge-minimizing maximum
independent subset used by the sparse-complement rows. Positivity of this
budget already implies that its complement is nonempty. -/
theorem IsEdgeMinimalMaximumOn.edge_upper_row
    {G : SimpleGraph V} {S I : Finset V} (hI : IsEdgeMinimalMaximumOn G S I)
    (hG : G.IsAcyclic)
    (hDpos : 1 ≤ min (I.card - (S \ I).card - 1) ((S \ I).card - 1))
    (r : ℕ) (hr : 2 ≤ r) :
    let D := min (I.card - (S \ I).card - 1) ((S \ I).card - 1)
    (D : ℝ) * (countIndependent G (S \ I) r : ℝ) -
        (edgeUpperGap (S \ I).card D r : ℝ) * (countIndependent G (S \ I) 2 : ℝ) ≤
      (D : ℝ) * (Nat.choose (S \ I).card r : ℝ) -
        (edgeUpperGap (S \ I).card D r : ℝ) * (Nat.choose (S \ I).card 2 : ℝ) := by
  have hD := min_le_right (I.card - (S \ I).card - 1) ((S \ I).card - 1)
  have hY : (S \ I).Nonempty := card_pos.mp (by omega)
  exact countIndependent_edge_upper G hG (S \ I) hY _ r hDpos
    (hI.edgeCountOn_complement_le_min hG) hD hr

#print axioms antitone_prefix_sum_mul_le
#print axioms binomial_loss_eq_sum
#print axioms edgeUpperGap_chord
#print axioms countIndependent_edge_upper
#print axioms IsEdgeMinimalMaximumOn.edge_upper_row

end ForestUnimodality
