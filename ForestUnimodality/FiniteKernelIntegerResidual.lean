import ForestUnimodality.FiniteKernelIntervalCertificate

/-! Clearing one shared positive denominator turns the entire finite state
loop into integer arithmetic. The coefficient identities are themselves
checked; the integer polynomial cannot choose a different residual. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate

structure IntegerResidualPolynomial where
  denominator : ℕ
  center : ℤ
  previous : ℤ
  next : ℤ
  square : ℤ
  linear : ℤ
  constant : ℤ

def IntegerResidualPolynomial.eval (p : IntegerResidualPolynomial) (lo hi : ℤ → ℤ) (j : ℤ) : ℤ :=
  p.center * lo j - p.previous * hi (j - 1) - p.next * hi (j + 1) +
    p.square * j ^ 2 + p.linear * j + p.constant

def IntegerResidualPolynomial.check {ι : Type*} (p : IntegerResidualPolynomial)
    (r : RationalRow ι) (n : ℕ) (q base : ℚ) (massDenominator : ℕ) : Bool := decide
  (0 < p.denominator ∧ 0 < massDenominator ∧
    (p.center : ℚ) / p.denominator =
      r.scale * (r.wL * (1 - q) + r.wR * q + 2 * r.wC) / massDenominator ∧
    (p.previous : ℚ) / p.denominator = r.scale * (r.wL * q + r.wC) / massDenominator ∧
    (p.next : ℚ) / p.denominator = r.scale * (r.wR * (1 - q) + r.wC) / massDenominator ∧
    (p.square : ℚ) / p.denominator = r.dδ ∧
    (p.linear : ℚ) / p.denominator = -2 * r.dδ * q * n - r.C ∧
    (p.constant : ℚ) / p.denominator = r.dδ * (q * n) ^ 2 + r.C * q * n + base)

theorem IntegerResidualPolynomial.check_sound {ι : Type*} (p : IntegerResidualPolynomial)
    (r : RationalRow ι) (n : ℕ) (q base : ℚ) (massDenominator : ℕ)
    (hc : p.check r n q base massDenominator = true) (lo hi : ℤ → ℤ) (j : ℤ) :
    r.shortResidual n j q base
      (fun s => (lo s : ℚ) / massDenominator) (fun s => (hi s : ℚ) / massDenominator) =
      (p.eval lo hi j : ℚ) / p.denominator := by
  have hp := of_decide_eq_true hc
  have he : (p.eval lo hi j : ℚ) / p.denominator =
      ((p.center : ℚ) / p.denominator) * lo j -
      ((p.previous : ℚ) / p.denominator) * hi (j - 1) -
      ((p.next : ℚ) / p.denominator) * hi (j + 1) +
      ((p.square : ℚ) / p.denominator) * (j : ℚ) ^ 2 +
      ((p.linear : ℚ) / p.denominator) * j + ((p.constant : ℚ) / p.denominator) := by
    push_cast [eval]
    ring
  rw [he, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2]
  unfold RationalRow.shortResidual kernelLower
  ring

def IntegerResidualPolynomial.spanCheck (p : IntegerResidualPolynomial) (n : ℕ)
    (lo hi : ℤ → ℤ) : Bool :=
  (List.range (n + 5)).all (fun i => decide (0 ≤ p.eval lo hi ((i : ℤ) - 2)))

theorem IntegerResidualPolynomial.spanCheck_sound {ι : Type*} (p : IntegerResidualPolynomial)
    (r : RationalRow ι) (n : ℕ) (q base : ℚ) (massDenominator : ℕ)
    (hc : p.check r n q base massDenominator = true) (lo hi : ℤ → ℤ)
    (hs : p.spanCheck n lo hi = true) :
    (List.range (n + 5)).all (fun i => decide (0 ≤ r.shortResidual n ((i : ℤ) - 2) q base
      (fun s => (lo s : ℚ) / massDenominator) (fun s => (hi s : ℚ) / massDenominator))) = true := by
  apply List.all_eq_true.mpr
  intro i hi'
  apply decide_eq_true
  rw [p.check_sound r n q base massDenominator hc lo hi]
  have hv : 0 ≤ p.eval lo hi ((i : ℤ) - 2) :=
    of_decide_eq_true (List.all_eq_true.mp hs i hi')
  exact div_nonneg (by exact_mod_cast hv) (by positivity)

#print axioms IntegerResidualPolynomial.check_sound
#print axioms IntegerResidualPolynomial.spanCheck_sound

end ForestUnimodality.FiniteKernelRationalCertificate
