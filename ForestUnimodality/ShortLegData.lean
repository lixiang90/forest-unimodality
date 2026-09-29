import ForestUnimodality.SpiderMean
import ForestUnimodality.MeanTerminalClosure
import Mathlib.Data.Rat.BigOperators

/-! Exact rational path statistics with a proved bridge to actual path data.
No numerical table is substituted for the graph recurrence. -/
namespace ForestUnimodality.ShortLegData

def transfer : ℕ → (ℚ × ℚ × ℚ × ℚ) → (ℚ × ℚ × ℚ × ℚ)
  | 0, x => x
  | n + 1, x =>
    let y := transfer n x
    (y.1 + 2 * y.2.2.1, y.2.1 + 2 * (y.2.2.2 + y.2.2.1), y.1, y.2.1)

def castState (x : ℚ × ℚ × ℚ × ℚ) : ℝ × ℝ × ℝ × ℝ :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2)

theorem transfer_cast (n : ℕ) (x : ℚ × ℚ × ℚ × ℚ) :
    castState (transfer n x) = pathMomentTransfer 2 n (castState x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pathMomentTransfer, ← ih]
    simp only [transfer, castState, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]

def pathData (n : ℕ) : ℚ × ℚ × ℚ × ℚ := transfer (n - 1) (3, 2, 1, 0)

theorem pathData_cast (n : ℕ) : castState (pathData n) = pathBranchStatistics n := by
  simpa [pathData, pathBranchStatistics, castState] using transfer_cast (n - 1) (3, 2, 1, 0)

theorem transfer_positive (n : ℕ) (x : ℚ × ℚ × ℚ × ℚ)
    (hZ : 0 < x.1) (hD : 0 < x.2.2.1) :
    0 < (transfer n x).1 ∧ 0 < (transfer n x).2.2.1 := by
  induction n with
  | zero => exact ⟨hZ, hD⟩
  | succ n ih =>
    exact ⟨add_pos ih.1 (mul_pos (by norm_num) ih.2), ih.1⟩

theorem pathData_positive (n : ℕ) : 0 < (pathData n).1 ∧ 0 < (pathData n).2.2.1 :=
  transfer_positive (n - 1) (3, 2, 1, 0) (by norm_num) (by norm_num)

def ratio (n : ℕ) : ℚ := (pathData n).1 / (pathData n).2.2.1
def excess (n : ℕ) : ℚ :=
  3 * (pathData n).2.1 / (pathData n).1 - ((n + 1) / 2 : ℕ) - 29 * n / 60
def deletedExcess (n : ℕ) : ℚ :=
  3 * (pathData n).2.2.2 / (pathData n).2.2.1 - ((n + 1) / 2 : ℕ) - 29 * n / 60

theorem even_bounds (i : ℕ) (hi : i < 6) :
    5 / 3 ≤ ratio (2 * i + 2) ∧ 13 / 30 ≤ excess (2 * i + 2) ∧
      -(11 / 60) ≤ deletedExcess (2 * i + 2) := by
  interval_cases i <;> norm_num [ratio, excess, deletedExcess, pathData, transfer]

theorem odd_bounds (i : ℕ) (hi : i < 7) :
    2 ≤ ratio (2 * i + 1) ∧ 343 / 1140 ≤ excess (2 * i + 1) ∧
      -(89 / 60) ≤ deletedExcess (2 * i + 1) := by
  interval_cases i <;> norm_num [ratio, excess, deletedExcess, pathData, transfer]

theorem data_positive (n : ℕ) (hn : 1 ≤ n) (hb : n ≤ 13) :
    0 < (pathData n).1 ∧ 0 < (pathData n).2.2.1 := by
  interval_cases n <;> norm_num [pathData, transfer]

/-- Affine numerator of the attachment residual. The state is alpha(H)-alpha(H-v).
Only same-parity leg families are later passed to this expression. -/
def residual (odd : Bool) (legs : List ℕ) (delta : ℕ) (r : ℚ) : ℚ :=
  let h : ℚ := 29 / 60 + if odd then 0 else delta
  (legs.map ratio).prod * ((legs.map excess).sum - h) +
    (r - 1) * (legs.map deletedExcess).sum + h + if odd then r * delta else 0

def spiderNumerator (legs : List ℕ) : ℚ :=
  let A := (legs.map fun n => (pathData n).1).prod
  let B := (legs.map fun n => (pathData n).2.2.1).prod
  let ma := (legs.map fun n => (pathData n).2.1 / (pathData n).1).sum
  let mb := (legs.map fun n => (pathData n).2.2.2 / (pathData n).2.2.1).sum
  let alpha : ℕ := max (legs.map fun n => (n + 1) / 2).sum
    ((legs.map fun n => n / 2).sum + 1)
  3 * (A * ma + 2 * B * (mb + 1)) - (A + 2 * B) *
    ((alpha : ℚ) + 29 * ((legs.sum : ℚ) + 1) / 60)

theorem residual_perm {legs other : List ℕ} (hp : legs.Perm other)
    (odd : Bool) (delta : ℕ) (r : ℚ) :
    residual odd legs delta r = residual odd other delta r := by
  unfold residual
  rw [(hp.map ratio).prod_eq, (hp.map excess).sum_eq, (hp.map deletedExcess).sum_eq]

theorem spiderNumerator_perm {legs other : List ℕ} (hp : legs.Perm other) :
    spiderNumerator legs = spiderNumerator other := by
  unfold spiderNumerator
  rw [(hp.map _).prod_eq, (hp.map _).prod_eq, (hp.map _).sum_eq,
    (hp.map _).sum_eq, (hp.map _).sum_eq, (hp.map _).sum_eq, hp.sum_eq]

#print axioms pathData_cast
#print axioms even_bounds
#print axioms odd_bounds
end ForestUnimodality.ShortLegData
