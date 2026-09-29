import ForestUnimodality.SpiderMean
import Mathlib.Tactic.IntervalCases

/-! A rational lower bound for the actual uniform independent-set mean of
every path.  The infinite tail is proved by an invariant of the Fibonacci
transfer; finite checks only establish its initial state. -/
namespace ForestUnimodality.UnitActivityPathDensity

def data : ℕ → (ℕ × ℕ × ℕ × ℕ)
  | 0 => (1, 0, 1, 0)
  | n + 1 =>
    let x := data n
    (x.1 + x.2.2.1, x.2.1 + x.2.2.2 + x.2.2.1, x.1, x.2.1)

def Z (n : ℕ) : ℕ := (data n).1
def M (n : ℕ) : ℕ := (data n).2.1

theorem Z_recurrence (n : ℕ) : Z (n + 2) = Z (n + 1) + Z n := rfl
theorem M_recurrence (n : ℕ) : M (n + 2) = M (n + 1) + M n + Z n := rfl

theorem Z_positive (n : ℕ) : 0 < Z n := by
  have h : 0 < (data n).1 ∧ 0 < (data n).2.2.1 := by
    induction n with
    | zero => norm_num [data]
    | succ n ih => exact ⟨Nat.add_pos_left ih.1 _, ih.1⟩
  exact h.1

def Invariant (n : ℕ) : Prop :=
  276393 * (Z (n + 1) : ℝ) ≤ 447214 * Z n ∧
  723607 * (Z n : ℝ) ≤ 447214 * Z (n + 1) ∧
  (276393 * (n : ℝ) + 144420) * Z n ≤ 1000000 * M n ∧
  (276393 * ((n : ℝ) + 1) + 144420) * Z (n + 1) ≤ 1000000 * M (n + 1)

theorem invariant_step (n : ℕ) (h : Invariant n) : Invariant (n + 1) := by
  obtain ⟨hu, hl, h0, h1⟩ := h
  have hz : (0 : ℝ) ≤ Z n := Nat.cast_nonneg _
  unfold Invariant
  rw [show n + 1 + 1 = n + 2 by omega, Z_recurrence, M_recurrence]
  push_cast
  refine ⟨?_, ?_, h1, ?_⟩
  · nlinarith
  · linarith
  · nlinarith

theorem invariant_eighteen : Invariant 18 := by
  norm_num [Invariant, Z, M, data]

theorem invariant_tail (n : ℕ) (hn : 18 ≤ n) : Invariant n := by
  induction n, hn using Nat.le_induction with
  | base => exact invariant_eighteen
  | succ n hn ih => exact invariant_step n ih

theorem numerator_lower (n : ℕ) (hn : 0 < n) :
    (276393 * (n : ℝ) + 113880) * Z n ≤ 1000000 * M n := by
  by_cases htail : 18 ≤ n
  · have h := (invariant_tail n htail).2.2.1
    have hz : (0 : ℝ) ≤ Z n := Nat.cast_nonneg _
    nlinarith
  · have hs : n ≤ 17 := by omega
    interval_cases n <;> norm_num [Z, M, data]

theorem numerator_lower_except_two (n : ℕ) (hn : 0 < n) (hne : n ≠ 2) :
    (276393 * (n : ℝ) + 144420) * Z n ≤ 1000000 * M n := by
  by_cases htail : 18 ≤ n
  · exact (invariant_tail n htail).2.2.1
  · have hs : n ≤ 17 := by omega
    interval_cases n <;> norm_num [Z, M, data] at *

theorem transfer (n : ℕ) :
    pathMomentTransfer 1 n (2, 1, 1, 0) =
      ((Z (n + 1) : ℝ), (M (n + 1) : ℝ), (Z n : ℝ), (M n : ℝ)) := by
  induction n with
  | zero => norm_num [pathMomentTransfer, Z, M, data]
  | succ n ih =>
    rw [pathMomentTransfer, ih]
    simp only [Z_recurrence, M_recurrence, Nat.cast_add, one_mul]
    congr 2; ring

theorem mean_lower (n : ℕ) (hn : 0 < n) :
    276393 / 1000000 * (n : ℝ) + 113880 / 1000000 ≤ (M n : ℝ) / Z n := by
  have hz : (0 : ℝ) < Z n := by exact_mod_cast Z_positive n
  apply (le_div_iff₀ hz).mpr
  nlinarith [numerator_lower n hn]

theorem mean_lower_except_two (n : ℕ) (hn : 0 < n) (hne : n ≠ 2) :
    276393 / 1000000 * (n : ℝ) + 144420 / 1000000 ≤ (M n : ℝ) / Z n := by
  have hz : (0 : ℝ) < Z n := by exact_mod_cast Z_positive n
  apply (le_div_iff₀ hz).mpr
  nlinarith [numerator_lower_except_two n hn hne]

#print axioms invariant_tail
#print axioms mean_lower_except_two
end ForestUnimodality.UnitActivityPathDensity

namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem PendantPathExtension.unitActivity_mean_lower
    {G : SimpleGraph V} {S : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G {v} v n S u) :
    276393 / 1000000 * (S.card : ℝ) + 113880 / 1000000 ≤ hardCoreMean G S 1 := by
  have ht := h.moment_transfer 1
  rw [hardCore_singleton_statistics] at ht
  norm_num only at ht
  rw [UnitActivityPathDensity.transfer] at ht
  have hZ := congrArg Prod.fst ht
  have hM := congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) ht
  dsimp only at hZ hM
  have hc : S.card = n + 1 := by simpa [Nat.add_comm] using h.card_eq
  unfold hardCoreMean
  rw [hZ, hM, hc]
  exact UnitActivityPathDensity.mean_lower (n + 1) (by omega)

theorem PendantPathExtension.unitActivity_mean_lower_except_two
    {G : SimpleGraph V} {S : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G {v} v n S u) (hne : S.card ≠ 2) :
    276393 / 1000000 * (S.card : ℝ) + 144420 / 1000000 ≤ hardCoreMean G S 1 := by
  have ht := h.moment_transfer 1
  rw [hardCore_singleton_statistics] at ht
  norm_num only at ht
  rw [UnitActivityPathDensity.transfer] at ht
  have hZ := congrArg Prod.fst ht
  have hM := congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) ht
  dsimp only at hZ hM
  have hc : S.card = n + 1 := by simpa [Nat.add_comm] using h.card_eq
  unfold hardCoreMean
  rw [hZ, hM, hc]
  exact UnitActivityPathDensity.mean_lower_except_two (n + 1) (by omega) (hc ▸ hne)

#print axioms PendantPathExtension.unitActivity_mean_lower
#print axioms PendantPathExtension.unitActivity_mean_lower_except_two
end ForestUnimodality
