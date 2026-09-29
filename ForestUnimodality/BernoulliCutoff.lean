import ForestUnimodality.BernoulliGaussianError
import ForestUnimodality.BinomialGradientBound

/-! Finite-frequency Bernoulli estimates. Every condition is a scalar inequality;
in particular no Gaussian damping outside the certified cutoff is assumed. -/
namespace ForestUnimodality.BernoulliCutoff
open Real Set

structure Valid (q T : ℝ) : Prop where
  positive : 0 < T
  period : T < Real.pi
  variance : 1 / 6 ≤ q * (1 - q)
  damping : 1 / 6 ≤ (q * (1 - q)) * (1 - T ^ 2 / 12)
  quartic : 1 - 5 * (q * (1 - q)) - 10 * (q * (1 - q)) ^ 2 +
    (15 / 8 : ℝ) * (q * (1 - q)) ^ 3 * T ^ 2 ≤ 0

theorem Valid.q_nonneg {q T : ℝ} (h : Valid q T) : 0 ≤ q := by
  have := h.variance
  nlinarith

theorem Valid.q_le_one {q T : ℝ} (h : Valid q T) : q ≤ 1 := by
  have := h.variance
  nlinarith

theorem cos_le_taylor_four {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  let f : ℝ → ℝ := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by dsimp [f]; fun_prop)
      (by dsimp [f]; fun_prop)
    intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    have he := Real.sin_ge_sub_cube hx0
    dsimp [f]
    simp (disch := fun_prop)
    nlinarith
  have he := hm (by simp) ht ht
  dsimp [f] at he
  simp only [zero_pow (by omega : 2 ≠ 0), zero_pow (by omega : 4 ≠ 0),
    zero_div, sub_zero, add_zero, Real.cos_zero, sub_self] at he
  linarith

theorem sine_comparison {v T t : ℝ} (hv : 0 ≤ v) (_hT : 0 ≤ T)
    (hcond : 1 / 6 ≤ v * (1 - T ^ 2 / 12)) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    t * (1 - 2 * v + 2 * v * Real.cos t) - Real.sin t ≤ 0 := by
  have hsq : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 htT 2
  have hcp := mul_nonneg hv (sub_nonneg.mpr hsq)
  have hlocal : 1 / 6 - v + v * t ^ 2 / 12 ≤ 0 := by nlinarith
  have hcos := mul_le_mul_of_nonneg_left (cos_le_taylor_four ht0)
    (show 0 ≤ 2 * v * t by positivity)
  have hsin := Real.sin_ge_sub_cube ht0
  calc
    _ ≤ t ^ 3 * (1 / 6 - v + v * t ^ 2 / 12) := by nlinarith
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hlocal

private noncomputable def compensatedModulus (v t : ℝ) : ℝ :=
  Real.exp (v * t ^ 2) * (1 - 2 * v * (1 - Real.cos t))

private theorem compensated_deriv (v t : ℝ) :
    HasDerivAt (compensatedModulus v)
      (2 * v * Real.exp (v * t ^ 2) *
        (t * (1 - 2 * v + 2 * v * Real.cos t) - Real.sin t)) t := by
  unfold compensatedModulus
  convert! (((hasDerivAt_id t).pow 2).const_mul v).exp.mul
    ((hasDerivAt_const t 1).sub
      (((hasDerivAt_const t 1).sub (Real.hasDerivAt_cos t)).const_mul (2 * v))) using 1
  simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring_nf

theorem modulus_sq_le_gaussian {v T t : ℝ} (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hcond : 1 / 6 ≤ v * (1 - T ^ 2 / 12)) (ht : |t| ≤ T) :
    1 - 2 * v * (1 - Real.cos t) ≤ Real.exp (-v * t ^ 2) := by
  have hm : AntitoneOn (compensatedModulus v) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (by unfold compensatedModulus; fun_prop) (by unfold compensatedModulus; fun_prop)
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) T := interior_subset hx
    rw [(compensated_deriv v x).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sine_comparison hv hT hcond hx'.1 hx'.2)
  have he := hm ⟨le_rfl, hT⟩ ⟨abs_nonneg t, ht⟩ (abs_nonneg t)
  dsimp [compensatedModulus] at he
  simp only [Real.cos_abs, sq_abs, zero_pow (by omega : 2 ≠ 0), mul_zero,
    Real.exp_zero, Real.cos_zero, sub_self, sub_zero, one_mul] at he
  have hmul := mul_le_mul_of_nonneg_left he (Real.exp_pos (-v * t ^ 2)).le
  have hinv : Real.exp (-v * t ^ 2) * Real.exp (v * t ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring_nf
  simpa only [← mul_assoc, hinv, one_mul, mul_one] using hmul

theorem norm_le_gaussian {q T t : ℝ} (h : Valid q T) (ht : |t| ≤ T) :
    ‖centeredBernoulliCharacteristic q t‖ ≤
      Real.exp (-(q * (1 - q)) * t ^ 2 / 2) := by
  have hv0 : 0 ≤ q * (1 - q) := by linarith [h.variance]
  have he := modulus_sq_le_gaussian hv0 h.positive.le h.damping ht
  rw [← centeredBernoulliCharacteristic_norm_sq] at he
  have hs : Real.exp (-(q * (1 - q)) * t ^ 2 / 2) ^ 2 =
      Real.exp (-(q * (1 - q)) * t ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  rw [← hs] at he
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp he

theorem re_error_bound {q T t : ℝ} (h : Valid q T) (ht : |t| ≤ T) :
    0 ≤ Real.exp (-(q * (1 - q)) * t ^ 2 / 2) - (centeredBernoulliCharacteristic q t).re ∧
    Real.exp (-(q * (1 - q)) * t ^ 2 / 2) - (centeredBernoulliCharacteristic q t).re ≤
      q * (1 - q) * t ^ 4 / 48 := by
  have hq0 := h.q_nonneg
  have hq1 := h.q_le_one
  have hv0 : 0 ≤ q * (1 - q) := by linarith [h.variance]
  have hv1 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  refine ⟨sub_nonneg.mpr ((Complex.re_le_norm _).trans (norm_le_gaussian h ht)), ?_⟩
  have hpoly := centeredBernoulliCharacteristic_re_error_polynomial (t := t) hq0 hq1 rfl
  have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith [sq_abs t, abs_nonneg t, h.positive]
  have hcprod := mul_le_mul_of_nonneg_left ht2
    (show 0 ≤ (15 / 8 : ℝ) * (q * (1 - q)) ^ 3 by positivity)
  have hc : 1 - 5 * (q * (1 - q)) - 10 * (q * (1 - q)) ^ 2 +
      (15 / 8 : ℝ) * (q * (1 - q)) ^ 3 * t ^ 2 ≤ 0 := by linarith [h.quartic]
  have hhigh := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (q * (1 - q)) * t ^ 6 / 720 by positivity) hc
  have hlead := mul_nonneg (show 0 ≤ (q * (1 - q)) * t ^ 4 / 4 by positivity)
    (sub_nonneg.mpr hv1)
  nlinarith

theorem error_bound {q T t : ℝ} (h : Valid q T) (ht : |t| ≤ T) :
    ‖centeredBernoulliCharacteristic q t -
      (Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℂ)‖ ≤
      q * (1 - q) * |1 - 2 * q| * |t| ^ 3 / 6 + q * (1 - q) * t ^ 4 / 48 := by
  have hr := re_error_bound h ht
  have hi := centeredBernoulliCharacteristic_im_bound h.q_nonneg h.q_le_one (ht.trans h.period.le)
  have hn := Complex.norm_le_abs_re_add_abs_im (centeredBernoulliCharacteristic q t -
    (Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero, abs_of_nonpos (by linarith [hr.1] :
      (centeredBernoulliCharacteristic q t).re - Real.exp (-(q * (1 - q)) * t ^ 2 / 2) ≤ 0)] at hn
  linarith [hr.2]

theorem pow_error_bound (m : ℕ) {q T t : ℝ} (h : Valid q T) (ht : |t| ≤ T) :
    ‖centeredBernoulliCharacteristic q t ^ m -
      (Real.exp (-(m : ℝ) * (q * (1 - q)) * t ^ 2 / 2) : ℂ)‖ ≤
      (m : ℝ) *
        (q * (1 - q) * |1 - 2 * q| * |t| ^ 3 / 6 + q * (1 - q) * t ^ 4 / 48) *
        Real.exp (-((m - 1 : ℕ) : ℝ) * (q * (1 - q)) * t ^ 2 / 2) := by
  cases m with
  | zero => simp
  | succ n =>
    let g := Real.exp (-(q * (1 - q)) * t ^ 2 / 2)
    have hg0 : 0 ≤ g := (Real.exp_pos _).le
    have hmod : ‖(g : ℂ)‖ ≤ g := by
      exact (show ‖(g : ℂ)‖ = g by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]).le
    have hpow := complex_pow_difference_bound (centeredBernoulliCharacteristic q t) (g : ℂ)
      (norm_le_gaussian h ht) hmod n
    have hgp (r : ℕ) : g ^ r = Real.exp (-(r : ℝ) * (q * (1 - q)) * t ^ 2 / 2) := by
      dsimp [g]
      rw [← Real.exp_nat_mul]
      congr 1
      ring_nf
    have hgc : (g : ℂ) ^ (n + 1) =
        (Real.exp (-((n + 1 : ℕ) : ℝ) * (q * (1 - q)) * t ^ 2 / 2) : ℂ) := by
      rw [← Complex.ofReal_pow, hgp]
    rw [hgc] at hpow
    have herr := error_bound h ht
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (n + 1))) (pow_nonneg hg0 n)
    simpa only [Nat.add_sub_cancel, hgp] using hpow.trans hmul

theorem norm_antitone {q s t : ℝ} (hv : 0 ≤ q * (1 - q))
    (hs : 0 ≤ s) (ht : t ≤ Real.pi) (hst : s ≤ t) :
    ‖centeredBernoulliCharacteristic q t‖ ≤ ‖centeredBernoulliCharacteristic q s‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [centeredBernoulliCharacteristic_norm_sq, centeredBernoulliCharacteristic_norm_sq]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hs ht hst
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * (q * (1 - q)) by positivity)
  nlinarith

theorem norm_abs (q t : ℝ) :
    ‖centeredBernoulliCharacteristic q |t|‖ = ‖centeredBernoulliCharacteristic q t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [centeredBernoulliCharacteristic_norm_sq, Real.cos_abs]

/-- The outer interval is paid using the actual characteristic-function modulus
at the cutoff. This is not an extension of the local Gaussian comparison. -/
theorem pow_norm_outside (m : ℕ) {q T t : ℝ} (h : Valid q T)
    (htT : T ≤ |t|) (ht : |t| ≤ Real.pi) :
    ‖centeredBernoulliCharacteristic q t ^ m‖ ≤
      Real.exp (-(m : ℝ) * (q * (1 - q)) * T ^ 2 / 2) := by
  have hv0 : 0 ≤ q * (1 - q) := by linarith [h.variance]
  have he := norm_antitone hv0 h.positive.le ht htT
  rw [norm_abs] at he
  have hlocal := norm_le_gaussian h (show |T| ≤ T by rw [abs_of_pos h.positive])
  have hp := pow_le_pow_left₀ (norm_nonneg _) (he.trans hlocal) m
  rw [norm_pow]
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring_nf

#print axioms norm_le_gaussian
#print axioms re_error_bound
#print axioms error_bound
#print axioms pow_error_bound
#print axioms pow_norm_outside
end ForestUnimodality.BernoulliCutoff
