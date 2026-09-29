import ForestUnimodality.Case13
import ForestUnimodality.LayerCoefficients
import ForestUnimodality.MaximumIndependent
import ForestUnimodality.PathLowerBound
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
An actual forest instance of the explicit (13,7,4) linear certificate.
Every certificate constraint is proved here from finite graph counts.
This is a local strict-increase theorem, not the complete unimodality result.
-/

namespace ForestUnimodality
open Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem forest13_alpha7_rising_four {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S I : Finset V)
    (hS : S.card = 13) (hI : IsMaximumIndependentOn G S I)
    (hIc : I.card = 7) :
    countIndependent G S 3 < countIndependent G S 4 := by
  classical
  have hY : (S \ I).card = 6 := by
    have hc := card_sdiff_add_card_eq_card hI.subset
    omega
  have hz (j m : ℕ) (h : 7 < j + m) : layerCount G I (S \ I) j m = 0 :=
    hI.layerCount_eq_zero_of_card_lt (by omega)
  let x : Fin 27 → ℝ := ![(layerCount G I (S \ I) 1 0 : ℝ), (layerCount G I (S \ I) 1 1 : ℝ), (layerCount G I (S \ I) 1 2 : ℝ), (layerCount G I (S \ I) 1 3 : ℝ), (layerCount G I (S \ I) 1 4 : ℝ), (layerCount G I (S \ I) 1 5 : ℝ), (layerCount G I (S \ I) 1 6 : ℝ), (layerCount G I (S \ I) 2 0 : ℝ), (layerCount G I (S \ I) 2 1 : ℝ), (layerCount G I (S \ I) 2 2 : ℝ), (layerCount G I (S \ I) 2 3 : ℝ), (layerCount G I (S \ I) 2 4 : ℝ), (layerCount G I (S \ I) 2 5 : ℝ), (layerCount G I (S \ I) 3 0 : ℝ), (layerCount G I (S \ I) 3 1 : ℝ), (layerCount G I (S \ I) 3 2 : ℝ), (layerCount G I (S \ I) 3 3 : ℝ), (layerCount G I (S \ I) 3 4 : ℝ), (layerCount G I (S \ I) 4 0 : ℝ), (layerCount G I (S \ I) 4 1 : ℝ), (layerCount G I (S \ I) 4 2 : ℝ), (layerCount G I (S \ I) 4 3 : ℝ), (layerCount G I (S \ I) 5 0 : ℝ), (layerCount G I (S \ I) 5 1 : ℝ), (layerCount G I (S \ I) 5 2 : ℝ), (layerCount G I (S \ I) 6 0 : ℝ), (layerCount G I (S \ I) 6 1 : ℝ)]
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    fin_cases i <;> simp [x]
  have h1 : (1 : ℝ) * x 0 + (1 : ℝ) * x 1 + (1 : ℝ) * x 2 + (1 : ℝ) * x 3 + (1 : ℝ) * x 4 + (1 : ℝ) * x 5 + (1 : ℝ) * x 6 = 6 := by
    have hc := sum_layerCount_eq_countIndependent G I (S \ I) 1
    rw [countIndependent_one, hY] at hc
    norm_num [hIc, Finset.sum_range_succ, hz] at hc
    dsimp [x]
    norm_num only [one_mul]
    exact_mod_cast hc
  have h2 : (1 : ℝ) * x 7 + (1 : ℝ) * x 8 + (1 : ℝ) * x 9 + (1 : ℝ) * x 10 + (1 : ℝ) * x 11 + (1 : ℝ) * x 12 ≤ 15 := by
    have hc := sum_layerCount_eq_countIndependent G I (S \ I) 2
    have hb := countIndependent_le_choose G (S \ I) 2
    rw [← hc] at hb
    norm_num [hY, Nat.choose] at hb
    norm_num [hIc, Finset.sum_range_succ, hz] at hb
    dsimp [x]
    norm_num only [one_mul]
    exact_mod_cast hb
  have h3 : (1 : ℝ) * x 13 + (1 : ℝ) * x 14 + (1 : ℝ) * x 15 + (1 : ℝ) * x 16 + (1 : ℝ) * x 17 ≤ 20 := by
    have hc := sum_layerCount_eq_countIndependent G I (S \ I) 3
    have hb := countIndependent_le_choose G (S \ I) 3
    rw [← hc] at hb
    norm_num [hY, Nat.choose] at hb
    norm_num [hIc, Finset.sum_range_succ, hz] at hb
    dsimp [x]
    norm_num only [one_mul]
    exact_mod_cast hb
  have hc3 : (countIndependent G S 3 : ℝ) = 35 + ((1 : ℝ) * x 2 + (3 : ℝ) * x 3 + (6 : ℝ) * x 4 + (10 : ℝ) * x 5 + (15 : ℝ) * x 6 + (1 : ℝ) * x 8 + (2 : ℝ) * x 9 + (3 : ℝ) * x 10 + (4 : ℝ) * x 11 + (5 : ℝ) * x 12 + (1 : ℝ) * x 13 + (1 : ℝ) * x 14 + (1 : ℝ) * x 15 + (1 : ℝ) * x 16 + (1 : ℝ) * x 17) := by
    have hc := countIndependent_cast_eq_layer_sum (R := ℝ) G S I hI.subset hI.independent 3
    norm_num [hY, hIc, Finset.sum_range_succ, layerCount_zero, hz, shiftedChoose, Nat.choose] at hc
    dsimp [x]
    convert hc using 1 <;> ring
  have hc4 : (countIndependent G S 4 : ℝ) = 35 + ((1 : ℝ) * x 3 + (4 : ℝ) * x 4 + (10 : ℝ) * x 5 + (20 : ℝ) * x 6 + (1 : ℝ) * x 9 + (3 : ℝ) * x 10 + (6 : ℝ) * x 11 + (10 : ℝ) * x 12 + (1 : ℝ) * x 14 + (2 : ℝ) * x 15 + (3 : ℝ) * x 16 + (4 : ℝ) * x 17 + (1 : ℝ) * x 18 + (1 : ℝ) * x 19 + (1 : ℝ) * x 20 + (1 : ℝ) * x 21) := by
    have hc := countIndependent_cast_eq_layer_sum (R := ℝ) G S I hI.subset hI.independent 4
    norm_num [hY, hIc, Finset.sum_range_succ, layerCount_zero, hz, shiftedChoose, Nat.choose] at hc
    dsimp [x]
    convert hc using 1 <;> ring
  have hp : 175 ≤ (1 : ℝ) * x 3 + (4 : ℝ) * x 4 + (10 : ℝ) * x 5 + (20 : ℝ) * x 6 + (1 : ℝ) * x 9 + (3 : ℝ) * x 10 + (6 : ℝ) * x 11 + (10 : ℝ) * x 12 + (1 : ℝ) * x 14 + (2 : ℝ) * x 15 + (3 : ℝ) * x 16 + (4 : ℝ) * x 17 + (1 : ℝ) * x 18 + (1 : ℝ) * x 19 + (1 : ℝ) * x 20 + (1 : ℝ) * x 21 := by
    have hb := choose_path_le_countIndependent G hG S 4
    norm_num [hS, Nat.choose] at hb
    have hb' : (210 : ℝ) ≤ (countIndependent G S 4 : ℝ) := by exact_mod_cast hb
    linarith [hc4]
  have hlt := case13_alpha7_rising_four x hx h1 h2 h3 hp
  have hcast : (countIndependent G S 3 : ℝ) < (countIndependent G S 4 : ℝ) := by
    linarith [hc3, hc4]
  exact_mod_cast hcast

#print axioms forest13_alpha7_rising_four
end ForestUnimodality
