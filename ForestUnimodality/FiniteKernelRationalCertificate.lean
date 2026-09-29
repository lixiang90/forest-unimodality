import ForestUnimodality.FiniteKernelCurvatureCertificate

/-! Exact rational endpoint checks for finite binomial-mixture certificates.
The binomial probabilities and the complete curvature price are reconstructed
from the row; no supplied residual or `passed` flag enters the interpretation. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate

open Finset FiniteKernelInterpolation FiniteKernelCurvatureCertificate

def mass (n : ℕ) (j : ℤ) (q : ℚ) : ℚ :=
  if 0 ≤ j ∧ j ≤ n then (n.choose j.toNat : ℚ) * q ^ j.toNat * (1 - q) ^ (n - j.toNat)
  else 0

def kernel (n : ℕ) (j : ℤ) (q wL wR wC : ℚ) : ℚ :=
  wL * ((1 - q) * mass n j q - q * mass n (j - 1) q) +
  wR * (q * mass n j q - (1 - q) * mass n (j + 1) q) +
  wC * (2 * mass n j q - mass n (j - 1) q - mass n (j + 1) q)

theorem cast_mass (n : ℕ) (j : ℤ) (q : ℚ) :
    (mass n j q : ℝ) = binomialMass n j (q : ℝ) := by
  unfold mass binomialMass
  split_ifs <;> push_cast <;> rfl

theorem cast_kernel (n : ℕ) (j : ℤ) (q wL wR wC : ℚ) :
    (kernel n j q wL wR wC : ℝ) =
      binomialKernel n j (q : ℝ) (wL : ℝ) (wR : ℝ) (wC : ℝ) := by
  simp only [kernel, binomialKernel, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_one, Rat.cast_ofNat, cast_mass]

structure RationalRow (ι : Type*) where
  terms : Finset ι
  scale : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  dδ : ℚ
  dM : ℚ
  wL : ℚ
  wR : ℚ
  wC : ℚ
  price : ι → ℚ
  retention : ι → ℚ
  fixedIndices : Finset ℤ
  fixedPrice : ℤ → ℚ

def RationalRow.fixed {ι : Type*} (r : RationalRow ι) (j : ℤ) : ℚ :=
  if j ∈ r.fixedIndices then r.fixedPrice j else 0

noncomputable def RationalRow.toReal {ι : Type*} (r : RationalRow ι) : Row ι where
  terms := r.terms
  scale := r.scale
  A := r.A
  B := r.B
  C := r.C
  dδ := r.dδ
  dM := r.dM
  wL := r.wL
  wR := r.wR
  wC := r.wC
  price i := r.price i
  retention i := r.retention i
  fixedPrice j := r.fixed j

def RationalRow.signCheck {ι : Type*} [DecidableEq ι] (r : RationalRow ι) : Bool :=
  decide ((0 < r.scale ∧ 0 ≤ r.wL ∧ 0 ≤ r.wR ∧ 0 ≤ r.wC ∧ 0 ≤ r.dδ ∧ 0 ≤ r.dM) ∧
    (∀ i ∈ r.terms, 0 ≤ r.price i ∧ 0 ≤ r.retention i ∧ r.retention i ≤ 1) ∧
    (∀ j ∈ r.fixedIndices, 0 ≤ r.fixedPrice j))

theorem RationalRow.signCheck_sound {ι : Type*} [DecidableEq ι] (r : RationalRow ι)
    (hr : r.signCheck = true) : r.toReal.Nonnegative := by
  have hs : (0 < r.scale ∧ 0 ≤ r.wL ∧ 0 ≤ r.wR ∧ 0 ≤ r.wC ∧ 0 ≤ r.dδ ∧ 0 ≤ r.dM) ∧
      (∀ i ∈ r.terms, 0 ≤ r.price i ∧ 0 ≤ r.retention i ∧ r.retention i ≤ 1) ∧
      (∀ j ∈ r.fixedIndices, 0 ≤ r.fixedPrice j) := of_decide_eq_true hr
  constructor
  · change (0 : ℝ) ≤ (r.scale : ℝ)
    exact_mod_cast hs.1.1.le
  · change (0 : ℝ) ≤ (r.wL : ℝ)
    exact_mod_cast hs.1.2.1
  · change (0 : ℝ) ≤ (r.wR : ℝ)
    exact_mod_cast hs.1.2.2.1
  · change (0 : ℝ) ≤ (r.wC : ℝ)
    exact_mod_cast hs.1.2.2.2.1
  · change (0 : ℝ) ≤ (r.dδ : ℝ)
    exact_mod_cast hs.1.2.2.2.2.1
  · intro i hi
    change (0 : ℝ) ≤ (r.price i : ℝ)
    exact_mod_cast (hs.2.1 i hi).1
  · intro i hi
    change (r.retention i : ℝ) ∈ Set.Icc 0 1
    exact ⟨by exact_mod_cast (hs.2.1 i hi).2.1, by exact_mod_cast (hs.2.1 i hi).2.2⟩
  · intro j
    dsimp [toReal, fixed]
    by_cases hj : j ∈ r.fixedIndices
    · simpa only [if_pos hj] using (show (0 : ℝ) ≤ r.fixedPrice j by exact_mod_cast hs.2.2 j hj)
    · simp [hj]

def RationalRow.residual {ι : Type*} (r : RationalRow ι) (n : ℕ) (j : ℤ) (q : ℚ) : ℚ :=
  r.scale * kernel n j q r.wL r.wR r.wC - r.A - r.B * n - r.C * ((j : ℚ) - q * n) +
    r.dδ * ((j : ℚ) - q * n) ^ 2 + r.dM * (n : ℚ) ^ 2 +
    (∑ i ∈ r.terms, r.price i * (1 - q + q * r.retention i) ^ n) +
    r.fixed j * (1 - q) ^ n

def secondTransform (n : ℕ) (t q : ℚ) : ℚ :=
  (n : ℚ) * (n - 1 : ℕ) * (1 - t) ^ 2 * (1 - q + q * t) ^ (n - 2)

def RationalRow.curvaturePrice {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (j : ℤ) (a bd bc : ℚ) : ℚ :=
  r.scale * (r.wL * bd + r.wR * bd + r.wC * bc) + 2 * r.dδ * (n : ℚ) ^ 2 +
    (∑ i ∈ r.terms, r.price i * secondTransform n (r.retention i) a) +
    r.fixed j * secondTransform n 0 a

theorem cast_secondTransform (n : ℕ) (t q : ℚ) :
    (secondTransform n t q : ℝ) = transformSecond n (t : ℝ) (q : ℝ) := by
  simp [secondTransform, transformSecond]

theorem RationalRow.cast_residual {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (j : ℤ) (q : ℚ) :
    (r.residual n j q : ℝ) = r.toReal.residual n j (q : ℝ) := by
  simp only [RationalRow.residual, Row.residual, Row.quadratic, transform, toReal,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_sum,
    Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, cast_kernel, mul_zero, add_zero]
  ring

theorem RationalRow.cast_curvaturePrice {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (j : ℤ) (a bd bc : ℚ) :
    (r.curvaturePrice n j a bd bc : ℝ) =
      r.toReal.curvaturePrice n j (a : ℝ) (bd : ℝ) (bd : ℝ) (bc : ℝ) := by
  simp only [RationalRow.curvaturePrice, Row.curvaturePrice, toReal,
    Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_sum, Rat.cast_natCast,
    Rat.cast_ofNat, cast_secondTransform, Rat.cast_zero]

def RationalRow.endpointCheck {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (j : ℤ) (a b bd bc : ℚ) : Bool := decide
  ((b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j a ∧
   (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j b)

theorem RationalRow.endpointCheck_cast {ι : Type*} (r : RationalRow ι)
    (n : ℕ) (j : ℤ) (a b bd bc : ℚ) (h : r.endpointCheck n j a b bd bc = true) :
    ((b : ℝ) - (a : ℝ)) ^ 2 * r.toReal.curvaturePrice n j (a : ℝ) bd bd bc / 8 ≤
      r.toReal.residual n j (a : ℝ) ∧
    ((b : ℝ) - (a : ℝ)) ^ 2 * r.toReal.curvaturePrice n j (a : ℝ) bd bd bc / 8 ≤
      r.toReal.residual n j (b : ℝ) := by
  have hQ : (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j a ∧
      (b - a) ^ 2 * r.curvaturePrice n j a bd bc / 8 ≤ r.residual n j b := of_decide_eq_true h
  have hR : ((b : ℝ) - (a : ℝ)) ^ 2 * (r.curvaturePrice n j a bd bc : ℝ) / 8 ≤
        (r.residual n j a : ℝ) ∧
      ((b : ℝ) - (a : ℝ)) ^ 2 * (r.curvaturePrice n j a bd bc : ℝ) / 8 ≤
        (r.residual n j b : ℝ) := by exact_mod_cast hQ
  simpa only [r.cast_curvaturePrice, r.cast_residual] using hR

/-- A checked interval, a checked rational Gaussian-curvature witness and
two reconstructed endpoint residuals imply the actual kernel inequality
throughout the real interval. No derivatives or pointwise estimates remain
as assumptions. -/
theorem RationalRow.checked_state_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (w : IntervalWitness) (d : DegreeWitness) (n : ℕ) (j : ℤ)
    (hr : r.signCheck = true) (hw : w.check = true) (hd : d.check n w.damping = true)
    (he : r.endpointCheck n j w.lo w.hi (d.directionUpper n w.damping)
      (d.centralUpper n w.damping) = true)
    {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hs := r.signCheck_sound hr
  have hi := w.endpoints hw
  have hda := w.sound hw (show (w.lo : ℝ) ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ) from
    ⟨le_rfl, hi.2.1⟩)
  have hbd : (0 : ℝ) ≤ d.directionUpper n w.damping :=
    (abs_nonneg _).trans (d.left_sound n w.damping hd j hda)
  have hbc : (0 : ℝ) ≤ d.centralUpper n w.damping :=
    (abs_nonneg _).trans (d.central_sound n w.damping hd j hda)
  have hep := r.endpointCheck_cast n j w.lo w.hi _ _ he
  exact r.toReal.nonnegative_of_endpoints hs n j hi.1 hi.2.2 hi.2.1 hbd hbd hbc
    (fun x hx => d.left_sound n w.damping hd j (w.sound hw hx))
    (fun x hx => d.right_sound n w.damping hd j (w.sound hw hx))
    (fun x hx => d.central_sound n w.damping hd j (w.sound hw hx)) hep.1 hep.2 hq

def RationalRow.statesCheck {ι : Type*} (r : RationalRow ι) (w : IntervalWitness)
    (degrees : ℕ → DegreeWitness) (states : List (ℕ × ℤ)) : Bool :=
  states.all fun s => (degrees s.1).check s.1 w.damping &&
    r.endpointCheck s.1 s.2 w.lo w.hi ((degrees s.1).directionUpper s.1 w.damping)
      ((degrees s.1).centralUpper s.1 w.damping)

/-- The state list is an explicit proof domain. A separate graph theorem
must prove that each positive-probability state belongs to it. -/
theorem RationalRow.statesCheck_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (w : IntervalWitness) (degrees : ℕ → DegreeWitness)
    (states : List (ℕ × ℤ)) (hr : r.signCheck = true) (hw : w.check = true)
    (hs : r.statesCheck w degrees states = true) {n : ℕ} {j : ℤ}
    (hstate : (n, j) ∈ states) {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hh := (List.all_eq_true.mp hs) (n, j) hstate
  have hc := Bool.and_eq_true_iff.mp hh
  exact r.checked_state_sound w (degrees n) n j hr hw hc.1 hc.2 hq

def RationalRow.spanCheck {ι : Type*} (r : RationalRow ι) (w : IntervalWitness)
    (d : DegreeWitness) (n : ℕ) : Bool := d.check n w.damping &&
  (List.range (n + 5)).all fun i =>
    r.endpointCheck n ((i : ℤ) - 2) w.lo w.hi (d.directionUpper n w.damping)
      (d.centralUpper n w.damping)

theorem RationalRow.spanCheck_sound {ι : Type*} [DecidableEq ι]
    (r : RationalRow ι) (w : IntervalWitness) (d : DegreeWitness) (n : ℕ)
    (hr : r.signCheck = true) (hw : w.check = true) (hs : r.spanCheck w d n = true)
    {j : ℤ} (hjlo : -2 ≤ j) (hjhi : j ≤ (n : ℤ) + 2)
    {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    0 ≤ r.toReal.residual n j q := by
  have hparts := Bool.and_eq_true_iff.mp hs
  have hmem : (j + 2).toNat ∈ List.range (n + 5) := by
    simp only [List.mem_range]
    omega
  have he := List.all_eq_true.mp hparts.2 (j + 2).toNat hmem
  have hei : ((j + 2).toNat : ℤ) - 2 = j := by omega
  rw [hei] at he
  exact r.checked_state_sound w d n j hr hw hparts.1 he hq

#print axioms cast_mass
#print axioms RationalRow.signCheck_sound
#print axioms RationalRow.cast_residual
#print axioms RationalRow.cast_curvaturePrice
#print axioms RationalRow.checked_state_sound
#print axioms RationalRow.statesCheck_sound
#print axioms RationalRow.spanCheck_sound

end ForestUnimodality.FiniteKernelRationalCertificate
