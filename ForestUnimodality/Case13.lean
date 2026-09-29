import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
Prototype: the (n, alpha, k) = (13, 7, 4) positive relaxation case
in Tong Zhang's candidate proof of forest independence unimodality.

The entries x i are intended to be the counts t_(j,m) for the index map:
[(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1)]

This theorem verifies only an exact real linear implication. Its graph-count
interpretation, the general row families, coverage, and all larger-order
arguments remain separate obligations. No complete forest theorem is claimed.
-/

namespace ForestUnimodality

/-- Four valid count constraints would force c_4 > c_3 for this parameter pair.
The common binomial constant C(7,3)=C(7,4)=35 cancels. -/
theorem case13_alpha7_rising_four
    (x : Fin 27 → ℝ)
    (hx : ∀ i, 0 ≤ x i)
    (hfirst : (1 : ℝ) * x 0 + (1 : ℝ) * x 1 + (1 : ℝ) * x 2 + (1 : ℝ) * x 3 + (1 : ℝ) * x 4 + (1 : ℝ) * x 5 + (1 : ℝ) * x 6 = 6)
    (hsecond : (1 : ℝ) * x 7 + (1 : ℝ) * x 8 + (1 : ℝ) * x 9 + (1 : ℝ) * x 10 + (1 : ℝ) * x 11 + (1 : ℝ) * x 12 ≤ 15)
    (hthird : (1 : ℝ) * x 13 + (1 : ℝ) * x 14 + (1 : ℝ) * x 15 + (1 : ℝ) * x 16 + (1 : ℝ) * x 17 ≤ 20)
    (hpath : 175 ≤ (1 : ℝ) * x 3 + (4 : ℝ) * x 4 + (10 : ℝ) * x 5 + (20 : ℝ) * x 6 + (1 : ℝ) * x 9 + (3 : ℝ) * x 10 + (6 : ℝ) * x 11 + (10 : ℝ) * x 12 + (1 : ℝ) * x 14 + (2 : ℝ) * x 15 + (3 : ℝ) * x 16 + (4 : ℝ) * x 17 + (1 : ℝ) * x 18 + (1 : ℝ) * x 19 + (1 : ℝ) * x 20 + (1 : ℝ) * x 21) :
    (1 : ℝ) * x 2 + (3 : ℝ) * x 3 + (6 : ℝ) * x 4 + (10 : ℝ) * x 5 + (15 : ℝ) * x 6 + (1 : ℝ) * x 8 + (2 : ℝ) * x 9 + (3 : ℝ) * x 10 + (4 : ℝ) * x 11 + (5 : ℝ) * x 12 + (1 : ℝ) * x 13 + (1 : ℝ) * x 14 + (1 : ℝ) * x 15 + (1 : ℝ) * x 16 + (1 : ℝ) * x 17 < (1 : ℝ) * x 3 + (4 : ℝ) * x 4 + (10 : ℝ) * x 5 + (20 : ℝ) * x 6 + (1 : ℝ) * x 9 + (3 : ℝ) * x 10 + (6 : ℝ) * x 11 + (10 : ℝ) * x 12 + (1 : ℝ) * x 14 + (2 : ℝ) * x 15 + (3 : ℝ) * x 16 + (4 : ℝ) * x 17 + (1 : ℝ) * x 18 + (1 : ℝ) * x 19 + (1 : ℝ) * x 20 + (1 : ℝ) * x 21 := by
  have hx0 := hx (0 : Fin 27)
  have hx1 := hx (1 : Fin 27)
  have hx2 := hx (2 : Fin 27)
  have hx3 := hx (3 : Fin 27)
  have hx4 := hx (4 : Fin 27)
  have hx5 := hx (5 : Fin 27)
  have hx6 := hx (6 : Fin 27)
  have hx7 := hx (7 : Fin 27)
  have hx8 := hx (8 : Fin 27)
  have hx9 := hx (9 : Fin 27)
  have hx10 := hx (10 : Fin 27)
  have hx11 := hx (11 : Fin 27)
  have hx12 := hx (12 : Fin 27)
  have hx13 := hx (13 : Fin 27)
  have hx14 := hx (14 : Fin 27)
  have hx15 := hx (15 : Fin 27)
  have hx16 := hx (16 : Fin 27)
  have hx17 := hx (17 : Fin 27)
  have hx18 := hx (18 : Fin 27)
  have hx19 := hx (19 : Fin 27)
  have hx20 := hx (20 : Fin 27)
  have hx21 := hx (21 : Fin 27)
  have hx22 := hx (22 : Fin 27)
  have hx23 := hx (23 : Fin 27)
  have hx24 := hx (24 : Fin 27)
  have hx25 := hx (25 : Fin 27)
  have hx26 := hx (26 : Fin 27)
  linarith

#print axioms case13_alpha7_rising_four

end ForestUnimodality
