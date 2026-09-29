import ForestUnimodality.ShiftedChoose
import ForestUnimodality.TailInequality
import ForestUnimodality.ReverseInequality

/-! Executable integer formulas for the finite certificate rows. These
definitions alone do not assert validity; graph soundness is proved separately. -/

namespace ForestUnimodality
namespace FiniteRows

inductive Row where
  | count (r : ℕ)
  | path (r : ℕ)
  | privateRow (r h : ℕ)
  | hall (r l : ℕ)
  | tail (r h : ℕ)
  | releaseUpper (r h : ℕ)
  | tailUpper (r h : ℕ)
  | mean (r : ℕ)
  | unionRow (r : ℕ)
  | edgeLower (r : ℕ)
  | edgeUpper (r : ℕ)
  | assumptionRow (r : ℕ)
  deriving DecidableEq, Repr

inductive Kind where
  | positive | negative | conditional
  deriving DecidableEq, Repr

def indicator (j r : ℕ) : ℤ := if j = r then 1 else 0

/-- Both offsets are guarded, so the coefficient at a negative index is zero. -/
def differenceCoeff (m j r : ℕ) : ℤ :=
  (shiftedChoose m j r : ℤ) - (shiftedChoose m (j + 1) r : ℤ)

def sparseBudget (n a : ℕ) : ℕ := a - (n - a) - 1
def intrinsicBudget (n a : ℕ) : ℕ := min (sparseBudget n a) (n - a - 1)
def hallFactor (n a r l : ℕ) : ℕ := (n - a) - r - (l - (a - (n - a)))
def extensionFactor (n a r : ℕ) : ℕ := (n - a) - (r - 1) - sparseBudget n a
def edgeGap (v D r : ℕ) : ℕ := (v - 1).choose (r - 1) - (v - D - 1).choose (r - 1)

def meanBeta (n a r : ℕ) : ℤ :=
  ((n - a - 2).choose (r - 1) : ℤ) - ((a : ℤ) - 2) * ((n - a - 2).choose (r - 2) : ℤ)

def meanBase (n a r : ℕ) : ℤ :=
  (a : ℤ) * ((n - a - 2).choose r : ℤ) +
    (2 * (a : ℤ) - (n : ℤ) + 1) * ((n - a - 2).choose (r - 1) : ℤ)

def coeff (n a : ℕ) (row : Row) (jm : ℕ × ℕ) : ℤ :=
  let j := jm.1
  let m := jm.2
  let v := n - a
  match row with
  | .count r => indicator j r
  | .path r => -(shiftedChoose m j r : ℤ)
  | .privateRow r h =>
      indicator j r * max 0 (((r : ℤ) - 1) * (m : ℤ) + (a : ℤ) - (r : ℤ) + 1 - (r : ℤ) * h) -
        indicator j (r - 1) * (v - (r - 1) : ℕ) * max 0 ((m : ℤ) - h)
  | .hall r l => (m.choose l : ℤ) *
      ((r + 1 : ℕ) * indicator j (r + 1) - (hallFactor n a r l : ℤ) * indicator j r)
  | .tail r h => indicator j r * (deletionThresholdCoeff a r h m : ℤ) -
      indicator j (r - 1) * (v - (r - 1) : ℕ) * (if h ≤ m then 1 else 0)
  | .releaseUpper r h =>
      indicator j (r - 1) * (extensionFactor n a r : ℤ) * max 0 ((m : ℤ) - h) -
        indicator j r * (releaseUpperCoeff a r h m : ℤ)
  | .tailUpper r h =>
      indicator j (r - 1) * (extensionFactor n a r : ℤ) * (if h ≤ m then 1 else 0) -
        indicator j r * (thresholdUpperCoeff a r h m : ℤ)
  | .mean r => -(m : ℤ) * indicator j r - meanBeta n a r * indicator j 2
  | .unionRow r => ((a : ℤ) - m) *
      (indicator j r - ((v - 1).choose (r - 1) : ℤ) * indicator j 1)
  | .edgeLower r => -indicator j r + ((v - 2).choose (r - 2) : ℤ) * indicator j 2
  | .edgeUpper r =>
      if intrinsicBudget n a = 0 then indicator j r else
        (intrinsicBudget n a : ℤ) * indicator j r -
          (edgeGap v (intrinsicBudget n a) r : ℤ) * indicator j 2
  | .assumptionRow r => differenceCoeff m j r

def rhs (n a : ℕ) (row : Row) : ℤ :=
  let v := n - a
  match row with
  | .count r => v.choose r
  | .path r => (a.choose r : ℤ) - ((n + 1 - r).choose r : ℤ)
  | .privateRow _ _ | .tail _ _ | .releaseUpper _ _ | .tailUpper _ _ | .unionRow _ => 0
  | .hall r l => if r = 0 then (hallFactor n a r l : ℤ) * (a.choose l : ℤ) else 0
  | .mean r => -meanBase n a r - meanBeta n a r * (v.choose 2 : ℤ)
  | .edgeLower r => -(v.choose r : ℤ) + ((v - 2).choose (r - 2) : ℤ) * (v.choose 2 : ℤ)
  | .edgeUpper r => if intrinsicBudget n a = 0 then v.choose r else
      (intrinsicBudget n a : ℤ) * (v.choose r : ℤ) -
        (edgeGap v (intrinsicBudget n a) r : ℤ) * (v.choose 2 : ℤ)
  | .assumptionRow r => -differenceCoeff a 0 r

/-- Legal row domain, including the restriction on conditional assumptions. -/
def Valid (n a k : ℕ) (kind : Kind) (row : Row) : Prop :=
  let v := n - a
  match row with
  | .count r | .mean r | .unionRow r | .edgeLower r | .edgeUpper r => 2 ≤ r ∧ r ≤ v
  | .path r => 2 ≤ r ∧ r ≤ a
  | .privateRow r h => 2 ≤ r ∧ r ≤ v ∧ h < a
  | .hall r l => l ≤ a ∧ r < min v (a - l) ∧ (l - (a - v)) ≤ v - r
  | .tail r h | .releaseUpper r h | .tailUpper r h =>
      2 ≤ r ∧ r ≤ v ∧ h ≤ a - r + 1
  | .assumptionRow r => kind = .conditional ∧ r = k

instance (n a k : ℕ) (kind : Kind) (row : Row) : Decidable (Valid n a k kind row) := by
  unfold Valid
  cases row <;> infer_instance

def targetIndex (k : ℕ) (kind : Kind) : ℕ := if kind = .positive then k else k + 1
def targetSign (kind : Kind) : ℤ := if kind = .positive then -1 else 1
def targetCoeff (k : ℕ) (kind : Kind) (jm : ℕ × ℕ) : ℤ :=
  targetSign kind * differenceCoeff jm.2 jm.1 (targetIndex k kind)
def targetConstant (a k : ℕ) (kind : Kind) : ℤ :=
  targetSign kind * differenceCoeff a 0 (targetIndex k kind)

end FiniteRows
end ForestUnimodality
