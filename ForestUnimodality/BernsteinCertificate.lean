import ForestUnimodality.PolynomialList
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Executable rational Bernstein certificates. The coefficient-list
arithmetic checks the full polynomial identity and all Bernstein coefficients.
Real semantics cover entire closed intervals and rectangles after exact
affine pullback. Cleared denominators require separate positivity proofs. -/

namespace ForestUnimodality.BernsteinCertificate

open PolynomialList

abbrev RatPolynomial := Poly ℚ
abbrev BiPolynomial := Poly RatPolynomial

def basis (n i : ℕ) : RatPolynomial :=
  C (n.choose i : ℚ) * pow X i * pow (1 - X) (n - i)

structure Certificate where
  degree : ℕ
  coeff : Fin (degree + 1) → ℚ

def expansion (c : Certificate) : RatPolynomial :=
  sum ((List.finRange (c.degree + 1)).map (fun i => C (c.coeff i) * basis c.degree i))

def ratZero (a : ℚ) : Bool := decide (a = 0)

def check (p : RatPolynomial) (c : Certificate) : Bool :=
  equalCheck ratZero p (expansion c) && decide (∀ i, 0 ≤ c.coeff i)

noncomputable def evalReal (p : RatPolynomial) (x : ℝ) : ℝ := eval rationalEvaluation.value x p

theorem ratZero_sound (a : ℚ) (h : ratZero a = true) : rationalEvaluation.value a = 0 := by
  have ha : a = 0 := of_decide_eq_true h
  simp [ha, rationalEvaluation]

theorem evalReal_basis_nonneg (n i : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    0 ≤ evalReal (basis n i) x := by
  simp only [evalReal, basis, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_nonneg (mul_nonneg (by change (0 : ℝ) ≤ ((n.choose i : ℚ) : ℝ); positivity) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem check_sound {p : RatPolynomial} {c : Certificate} (h : check p c = true)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) : 0 ≤ evalReal p x := by
  have hc : equalCheck ratZero p (expansion c) = true ∧ ∀ i, 0 ≤ c.coeff i := by
    simpa only [check, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  rw [evalReal, equalCheck_sound rationalEvaluation ratZero ratZero_sound hc.1 x]
  rw [expansion, eval_sum]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  rw [eval_mul, eval_C]
  exact mul_nonneg (Rat.cast_nonneg.mpr (hc.2 i)) (evalReal_basis_nonneg _ _ hx)

theorem check_polynomial_identity {p : RatPolynomial} {c : Certificate} (h : check p c = true) :
    toPolynomial p = toPolynomial (expansion c) := by
  have hc : equalCheck ratZero p (expansion c) = true ∧ ∀ i, 0 ≤ c.coeff i := by
    simpa only [check, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  exact equalCheck_toPolynomial_eq hc.1

def affine (lo hi : ℚ) : RatPolynomial := C lo + C (hi - lo) * X

def intervalCheck (p : RatPolynomial) (lo hi : ℚ) (c : Certificate) : Bool :=
  decide (lo ≤ hi) && check (comp p (affine lo hi)) c

theorem evalReal_affine (lo hi : ℚ) (t : ℝ) :
    evalReal (affine lo hi) t = (lo : ℝ) + ((hi : ℝ) - lo) * t := by
  simp only [evalReal, affine, eval_add, eval_mul, eval_C, eval_X]
  simp [rationalEvaluation]

theorem evalReal_comp_affine (p : RatPolynomial) (lo hi : ℚ) (t : ℝ) :
    evalReal (comp p (affine lo hi)) t =
      evalReal p ((lo : ℝ) + ((hi : ℝ) - lo) * t) := by
  change eval rationalEvaluation.value t (comp p (affine lo hi)) = _
  rw [eval_comp]
  change evalReal p (evalReal (affine lo hi) t) = _
  rw [evalReal_affine]

theorem exists_affine_parameter {lo hi x : ℝ} (hlohi : lo ≤ hi)
    (hx : x ∈ Set.Icc lo hi) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, lo + (hi - lo) * t = x := by
  by_cases heq : lo = hi
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    have h : x = lo := by rw [← heq] at hx; exact le_antisymm hx.2 hx.1
    simp [h]
  · have hpos : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne hlohi heq)
    refine ⟨(x - lo) / (hi - lo), ⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le, ?_⟩, ?_⟩
    · apply (div_le_one hpos).mpr
      linarith [hx.2]
    · field_simp
      ring

theorem intervalCheck_sound {p : RatPolynomial} {lo hi : ℚ} {c : Certificate}
    (h : intervalCheck p lo hi c = true) {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) : 0 ≤ evalReal p x := by
  have hc : lo ≤ hi ∧ check (comp p (affine lo hi)) c = true := by
    simpa only [intervalCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  obtain ⟨t, ht, heq⟩ := exists_affine_parameter (Rat.cast_le.mpr hc.1) hx
  have hpos := check_sound hc.2 ht
  rwa [evalReal_comp_affine, heq] at hpos

def basis₂ (nx ny i j : ℕ) : BiPolynomial :=
  C (basis nx i) * C (C (ny.choose j : ℚ)) * pow X j * pow (1 - X) (ny - j)

structure Certificate₂ where
  degreeX : ℕ
  degreeY : ℕ
  coeff : Fin (degreeX + 1) → Fin (degreeY + 1) → ℚ

def expansion₂ (c : Certificate₂) : BiPolynomial :=
  sum ((List.finRange (c.degreeX + 1)).map (fun i =>
    sum ((List.finRange (c.degreeY + 1)).map (fun j =>
      C (C (c.coeff i j)) * basis₂ c.degreeX c.degreeY i j))))

def check₂ (p : BiPolynomial) (c : Certificate₂) : Bool :=
  equalCheck (zeroCheck ratZero) p (expansion₂ c) && decide (∀ i j, 0 ≤ c.coeff i j)

noncomputable def evalReal₂ (p : BiPolynomial) (x y : ℝ) : ℝ :=
  eval (liftEvaluation rationalEvaluation x).value y p

theorem evalReal₂_basis_nonneg (nx ny i j : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    0 ≤ evalReal₂ (basis₂ nx ny i j) x y := by
  simp only [evalReal₂, basis₂, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  change 0 ≤ evalReal (basis nx i) x * evalReal (C (ny.choose j : ℚ)) x * y ^ j * (1 - y) ^ (ny - j)
  simp only [evalReal, eval_C]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (evalReal_basis_nonneg nx i hx)
      (by change (0 : ℝ) ≤ ((ny.choose j : ℚ) : ℝ); positivity)) (pow_nonneg hy.1 _))
    (pow_nonneg (sub_nonneg.mpr hy.2) _)

theorem check₂_sound {p : BiPolynomial} {c : Certificate₂} (h : check₂ p c = true)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    0 ≤ evalReal₂ p x y := by
  have hc : equalCheck (zeroCheck ratZero) p (expansion₂ c) = true ∧ ∀ i j, 0 ≤ c.coeff i j := by
    simpa only [check₂, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  have hz : ∀ a, zeroCheck ratZero a = true → (liftEvaluation rationalEvaluation x).value a = 0 := by
    intro a ha
    exact zeroCheck_sound rationalEvaluation.value ratZero ratZero_sound ha x
  rw [evalReal₂, equalCheck_sound (liftEvaluation rationalEvaluation x) _ hz hc.1 y]
  rw [expansion₂, eval_sum]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  rw [eval_sum]
  apply List.sum_nonneg
  intro b hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
  rw [eval_mul, eval_C]
  change 0 ≤ evalReal (C (c.coeff i j)) x * evalReal₂ (basis₂ c.degreeX c.degreeY i j) x y
  rw [evalReal, eval_C]
  exact mul_nonneg (Rat.cast_nonneg.mpr (hc.2 i j)) (evalReal₂_basis_nonneg _ _ _ _ hx hy)

def boxPullback (p : BiPolynomial) (loX hiX loY hiY : ℚ) : BiPolynomial :=
  comp (map (fun q => comp q (affine loX hiX)) p)
    (C (C loY) + C (C (hiY - loY)) * X)

def boxCheck (p : BiPolynomial) (loX hiX loY hiY : ℚ) (c : Certificate₂) : Bool :=
  decide (loX ≤ hiX ∧ loY ≤ hiY) && check₂ (boxPullback p loX hiX loY hiY) c

theorem evalReal₂_boxPullback (p : BiPolynomial) (loX hiX loY hiY : ℚ) (t u : ℝ) :
    evalReal₂ (boxPullback p loX hiX loY hiY) t u =
      evalReal₂ p ((loX : ℝ) + ((hiX : ℝ) - loX) * t)
        ((loY : ℝ) + ((hiY : ℝ) - loY) * u) := by
  have hevalY : eval (liftEvaluation rationalEvaluation t).value u
      (C (C loY) + C (C (hiY - loY)) * X) = (loY : ℝ) + ((hiY : ℝ) - loY) * u := by
    rw [eval_add, eval_mul, eval_C, eval_C, eval_X]
    change evalReal (C loY) t + evalReal (C (hiY - loY)) t * u = _
    simp only [evalReal, eval_C]
    simp [rationalEvaluation]
  unfold evalReal₂ boxPullback
  rw [eval_comp, hevalY, eval_map]
  have hevalX : (fun q => (liftEvaluation rationalEvaluation t).value (comp q (affine loX hiX))) =
      (liftEvaluation rationalEvaluation ((loX : ℝ) + ((hiX : ℝ) - loX) * t)).value := by
    funext q
    exact evalReal_comp_affine q loX hiX t
  rw [hevalX]

theorem boxCheck_sound {p : BiPolynomial} {loX hiX loY hiY : ℚ} {c : Certificate₂}
    (h : boxCheck p loX hiX loY hiY c = true) {x y : ℝ}
    (hx : x ∈ Set.Icc (loX : ℝ) (hiX : ℝ))
    (hy : y ∈ Set.Icc (loY : ℝ) (hiY : ℝ)) : 0 ≤ evalReal₂ p x y := by
  have hc : (loX ≤ hiX ∧ loY ≤ hiY) ∧ check₂ (boxPullback p loX hiX loY hiY) c = true := by
    simpa only [boxCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  obtain ⟨t, ht, heqX⟩ := exists_affine_parameter (Rat.cast_le.mpr hc.1.1) hx
  obtain ⟨u, hu, heqY⟩ := exists_affine_parameter (Rat.cast_le.mpr hc.1.2) hy
  have hpos := check₂_sound hc.2 ht hu
  rwa [evalReal₂_boxPullback, heqX, heqY] at hpos

theorem intervalCheck_polynomial_sound {p : RatPolynomial} {lo hi : ℚ} {c : Certificate}
    (h : intervalCheck p lo hi c = true) {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    0 ≤ (toPolynomial p).eval₂ (Rat.castHom ℝ) x := by
  rw [eval_toPolynomial]
  exact intervalCheck_sound h hx

theorem quotient_nonneg_of_intervalCheck {p : RatPolynomial} {lo hi : ℚ} {c : Certificate}
    (h : intervalCheck p lo hi c = true) {x d : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) (hd : 0 < d) :
    0 ≤ evalReal p x / d := div_nonneg (intervalCheck_sound h hx) hd.le

theorem quotient_nonneg_of_boxCheck {p : BiPolynomial} {loX hiX loY hiY : ℚ} {c : Certificate₂}
    (h : boxCheck p loX hiX loY hiY c = true) {x y d : ℝ}
    (hx : x ∈ Set.Icc (loX : ℝ) (hiX : ℝ)) (hy : y ∈ Set.Icc (loY : ℝ) (hiY : ℝ))
    (hd : 0 < d) : 0 ≤ evalReal₂ p x y / d := div_nonneg (boxCheck_sound h hx hy) hd.le

def intervalLowerCheck (p : RatPolynomial) (lo hi lower : ℚ) (c : Certificate) : Bool :=
  intervalCheck (p - C lower) lo hi c

theorem intervalLowerCheck_sound {p : RatPolynomial} {lo hi lower : ℚ} {c : Certificate}
    (h : intervalLowerCheck p lo hi lower c = true) {x : ℝ}
    (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) : (lower : ℝ) ≤ evalReal p x := by
  have hp := intervalCheck_sound h hx
  change 0 ≤ eval rationalEvaluation.value x (p - C lower) at hp
  rw [eval_sub, eval_C] at hp
  exact sub_nonneg.mp hp

def boxLowerCheck (p : BiPolynomial) (loX hiX loY hiY lower : ℚ) (c : Certificate₂) : Bool :=
  boxCheck (p - C (C lower)) loX hiX loY hiY c

theorem boxLowerCheck_sound {p : BiPolynomial} {loX hiX loY hiY lower : ℚ} {c : Certificate₂}
    (h : boxLowerCheck p loX hiX loY hiY lower c = true) {x y : ℝ}
    (hx : x ∈ Set.Icc (loX : ℝ) (hiX : ℝ)) (hy : y ∈ Set.Icc (loY : ℝ) (hiY : ℝ)) :
    (lower : ℝ) ≤ evalReal₂ p x y := by
  have hp := boxCheck_sound h hx hy
  change 0 ≤ eval (liftEvaluation rationalEvaluation x).value y (p - C (C lower)) at hp
  rw [eval_sub, eval_C] at hp
  change 0 ≤ evalReal₂ p x y - evalReal (C lower) x at hp
  simp only [evalReal, eval_C] at hp
  exact sub_nonneg.mp hp

/-- A nontrivial exact interval witness for 4-x² on [-2,2]. -/
def intervalExample : Certificate := ⟨2, fun i => if i = 1 then 8 else 0⟩

theorem intervalExample_checked : intervalCheck ⟨[4, 0, -1]⟩ (-2) 2 intervalExample = true := by
  decide +kernel

/-- A tensor witness for x(1-x)y(1-y), vanishing on all four box edges. -/
def rectangleExample : Certificate₂ := ⟨2, 2, fun i j => if i = 1 ∧ j = 1 then 1 / 4 else 0⟩

theorem rectangleExample_checked :
    boxCheck ⟨[0, ⟨[0, 1, -1]⟩, ⟨[0, -1, 1]⟩]⟩ 0 1 0 1 rectangleExample = true := by
  decide +kernel

/-- A positive Bernstein list cannot silently drop a higher-degree term. -/
theorem rejects_unmatched_high_degree :
    check ⟨[0, 1, -1, 1]⟩ ⟨2, fun i => if i = 1 then 1 / 2 else 0⟩ = false := by
  decide +kernel

#print axioms check_sound
#print axioms check_polynomial_identity
#print axioms intervalCheck_sound
#print axioms check₂_sound
#print axioms boxCheck_sound
#print axioms intervalExample_checked
#print axioms rectangleExample_checked

end ForestUnimodality.BernsteinCertificate
