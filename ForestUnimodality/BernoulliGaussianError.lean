import ForestUnimodality.BernoulliGaussian

/-! Finite, phase-sensitive error estimates for the actual centered Bernoulli
characteristic function. In particular, the cubic imaginary error vanishes
at the symmetric parameter; it is not replaced by an absolute third moment. -/
namespace ForestUnimodality
open Real Set

theorem hasDerivAt_sinc_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Real.sinc ((x * Real.cos x - Real.sin x) / x ^ 2) x := by
  have he : Real.sinc =ᶠ[nhds x] (fun y => Real.sin y / y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact Real.sinc_of_ne_zero hy
  have hd := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  convert! hd.congr_of_eventuallyEq he using 1
  simp only [id_eq, mul_one]
  ring

private theorem nonneg_of_deriv {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hzero : 0 ≤ f 0)
    (hd : ∀ x, 0 < x → 0 ≤ deriv f x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    hf.continuous.continuousOn hf.differentiableOn
    (fun x hx => hd x (by simpa using hx))
  exact hzero.trans (hm (by simp) hx hx)

theorem sin_sub_mul_cos_le_cube {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x - x * Real.cos x ≤ x ^ 3 / 3 := by
  have hh : 0 ≤ x ^ 3 / 3 - Real.sin x + x * Real.cos x := by
    apply nonneg_of_deriv (f := fun t => t ^ 3 / 3 - Real.sin t + t * Real.cos t)
      (by fun_prop) (by norm_num) ?_ hx
    intro t ht
    have he := mul_le_mul_of_nonneg_left (Real.sin_le ht.le) ht.le
    simp (disch := fun_prop)
    nlinarith
  linarith

theorem sinc_add_sq_monotone : MonotoneOn (fun x => Real.sinc x + x ^ 2 / 6) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) (by fun_prop)
  · intro x hx
    have hp : 0 < x := by simpa using hx
    exact ((hasDerivAt_sinc_of_ne_zero hp.ne').add
      (((hasDerivAt_id x).pow 2).div_const 6)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hp : 0 < x := by simpa using hx
    have hd : HasDerivAt (fun x => Real.sinc x + x ^ 2 / 6)
        ((x * Real.cos x - Real.sin x) / x ^ 2 + 2 * x / 6) x := by
      convert! ((hasDerivAt_sinc_of_ne_zero hp.ne').add
        (((hasDerivAt_id x).pow 2).div_const 6)) using 1
      simp
    rw [hd.deriv]
    have he := sin_sub_mul_cos_le_cube hp.le
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hp)).mp
    field_simp
    nlinarith

theorem sinc_antitone_on_period : AntitoneOn Real.sinc (Icc 0 Real.pi) := by
  have hnum {x : ℝ} (hx : x ∈ Icc 0 Real.pi) : 0 ≤ Real.sin x - x * Real.cos x := by
    have hm : MonotoneOn (fun t => Real.sin t - t * Real.cos t) (Icc 0 Real.pi) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop) (by fun_prop)
      intro t ht
      have hh : t ∈ Ioo 0 Real.pi := by simpa only [interior_Icc] using ht
      have he := mul_nonneg hh.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hh.1.le hh.2.le)
      simp (disch := fun_prop)
      nlinarith
    have he := hm ⟨le_rfl, Real.pi_pos.le⟩ hx hx.1
    simpa using he
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) Real.continuous_sinc.continuousOn
  · intro x hx
    have hp : x ∈ Ioo 0 Real.pi := by simpa only [interior_Icc] using hx
    exact (hasDerivAt_sinc_of_ne_zero hp.1.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    have hp : x ∈ Ioo 0 Real.pi := by simpa only [interior_Icc] using hx
    rw [(hasDerivAt_sinc_of_ne_zero hp.1.ne').deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hnum ⟨hp.1.le, hp.2.le⟩]) (sq_nonneg x)

theorem sinc_sub_le_square_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ Real.pi) :
    0 ≤ Real.sinc a - Real.sinc b ∧ Real.sinc a - Real.sinc b ≤ (b ^ 2 - a ^ 2) / 6 := by
  have h1 := sinc_antitone_on_period ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
  have h2 := sinc_add_sq_monotone ha (ha.trans hab) hab
  constructor <;> linarith

theorem abs_sinc_sub_le_abs_square_difference {a b : ℝ}
    (ha : a ∈ Icc 0 Real.pi) (hb : b ∈ Icc 0 Real.pi) :
    |Real.sinc a - Real.sinc b| ≤ |a ^ 2 - b ^ 2| / 6 := by
  rcases le_total a b with hab | hba
  · have he := sinc_sub_le_square_difference ha.1 hab hb.2
    have hs : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.1 hab 2
    rw [abs_of_nonneg he.1, abs_of_nonpos (sub_nonpos.mpr hs)]
    linarith [he.2]
  · have he := sinc_sub_le_square_difference hb.1 hba ha.2
    have hs : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb.1 hba 2
    rw [abs_of_nonpos (by linarith [he.1]), abs_of_nonneg (sub_nonneg.mpr hs)]
    linarith [he.2]

theorem centeredBernoulliCharacteristic_eq_two_exp (q t : ℝ) :
    centeredBernoulliCharacteristic q t =
      (1 - q : ℝ) * Complex.exp (-((q : ℂ) * t * Complex.I)) +
        (q : ℂ) * Complex.exp (((1 - q : ℝ) : ℂ) * t * Complex.I) := by
  unfold centeredBernoulliCharacteristic
  rw [mul_add]
  have he : Complex.exp (-((q : ℂ) * t * Complex.I)) *
      Complex.exp ((t : ℂ) * Complex.I) =
      Complex.exp (((1 - q : ℝ) : ℂ) * t * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (1 - q : ℝ) * Complex.exp (-((q : ℂ) * t * Complex.I)) +
        (q : ℂ) * (Complex.exp (-((q : ℂ) * t * Complex.I)) *
          Complex.exp ((t : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [he]

theorem centeredBernoulliCharacteristic_re (q t : ℝ) :
    (centeredBernoulliCharacteristic q t).re =
      (1 - q) * Real.cos (q * t) + q * Real.cos ((1 - q) * t) := by
  rw [centeredBernoulliCharacteristic_eq_two_exp]
  have h1 : -((q : ℂ) * t * Complex.I) = (-(q * t) : ℝ) * Complex.I := by push_cast; ring
  have h2 : ((1 - q : ℝ) : ℂ) * t * Complex.I = ((1 - q) * t : ℝ) * Complex.I := by push_cast; ring
  rw [h1, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem centeredBernoulliCharacteristic_im (q t : ℝ) :
    (centeredBernoulliCharacteristic q t).im =
      q * Real.sin ((1 - q) * t) - (1 - q) * Real.sin (q * t) := by
  rw [centeredBernoulliCharacteristic_eq_two_exp]
  have h1 : -((q : ℂ) * t * Complex.I) = (-(q * t) : ℝ) * Complex.I := by push_cast; ring
  have h2 : ((1 - q : ℝ) : ℂ) * t * Complex.I = ((1 - q) * t : ℝ) * Complex.I := by push_cast; ring
  rw [h1, h2]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ring

theorem mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx]
  field_simp

theorem centeredBernoulliCharacteristic_im_sinc (q t : ℝ) :
    (centeredBernoulliCharacteristic q t).im =
      q * (1 - q) * t * (Real.sinc ((1 - q) * t) - Real.sinc (q * t)) := by
  rw [centeredBernoulliCharacteristic_im]
  have h1 := mul_sinc ((1 - q) * t)
  have h2 := mul_sinc (q * t)
  nlinarith [congrArg (fun a : ℝ => q * a) h1, congrArg (fun a : ℝ => (1 - q) * a) h2]

theorem sinc_abs (x : ℝ) : Real.sinc |x| = Real.sinc x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, Real.sinc_neg]

/-- The sharp cubic asymmetry factor vanishes at q=1/2. -/
theorem centeredBernoulliCharacteristic_im_bound {q t : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : |t| ≤ Real.pi) :
    |(centeredBernoulliCharacteristic q t).im| ≤
      q * (1 - q) * |1 - 2 * q| * |t| ^ 3 / 6 := by
  have hp : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have ha : |(1 - q) * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg hp]
    nlinarith [abs_nonneg t]
  have hb : |q * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg hq0]
    nlinarith [abs_nonneg t]
  have he := abs_sinc_sub_le_abs_square_difference
    ⟨abs_nonneg ((1 - q) * t), ha⟩ ⟨abs_nonneg (q * t), hb⟩
  simp only [sinc_abs, sq_abs] at he
  have hs : ((1 - q) * t) ^ 2 - (q * t) ^ 2 = (1 - 2 * q) * t ^ 2 := by ring
  rw [hs, abs_mul, abs_of_nonneg (sq_nonneg t)] at he
  rw [centeredBernoulliCharacteristic_im_sinc, abs_mul, abs_mul,
    abs_mul, abs_of_nonneg hq0, abs_of_nonneg hp]
  calc
    _ ≤ q * (1 - q) * |t| * (|1 - 2 * q| * t ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [← sq_abs t]; ring

theorem cos_ge_taylor_six (x : ℝ) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have h4 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    apply nonneg_of_deriv (f := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := Real.sin_ge_sub_cube hy.le
    simp (disch := fun_prop)
    nlinarith
  have h5 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t := by
    apply nonneg_of_deriv (f := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h4 y hy.le
    simp (disch := fun_prop)
    nlinarith
  have h6 (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720 := by
    apply nonneg_of_deriv (f := fun t =>
      Real.cos t - 1 + t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 720)
      (by fun_prop) (by norm_num) ?_ ht
    intro y hy
    have he := h5 y hy.le
    simp (disch := fun_prop)
    nlinarith
  have he := h6 |x| (abs_nonneg x)
  rw [Real.cos_abs, show |x| ^ 2 = x ^ 2 by exact sq_abs x,
    show |x| ^ 4 = x ^ 4 by rw [show 4 = 2 * 2 by norm_num, pow_mul, sq_abs, pow_mul]] at he
  have h6eq : |x| ^ 6 = x ^ 6 := by rw [show 6 = 2 * 3 by norm_num, pow_mul, sq_abs, pow_mul]
  rw [h6eq] at he
  linarith

theorem centeredBernoulliCharacteristic_re_lower {q v t : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : v = q * (1 - q)) :
    1 - v * t ^ 2 / 2 + v * (1 - 3 * v) * t ^ 4 / 24 -
      v * (1 - 5 * v + 5 * v ^ 2) * t ^ 6 / 720 ≤
        (centeredBernoulliCharacteristic q t).re := by
  have h1 := mul_le_mul_of_nonneg_left (cos_ge_taylor_six (q * t)) (sub_nonneg.mpr hq1)
  have h2 := mul_le_mul_of_nonneg_left (cos_ge_taylor_six ((1 - q) * t)) hq0
  rw [centeredBernoulliCharacteristic_re]
  calc
    _ = (1 - q) * (1 - (q * t) ^ 2 / 2 + (q * t) ^ 4 / 24 - (q * t) ^ 6 / 720) +
        q * (1 - ((1 - q) * t) ^ 2 / 2 + ((1 - q) * t) ^ 4 / 24 - ((1 - q) * t) ^ 6 / 720) := by
      rw [hv]
      ring
    _ ≤ _ := add_le_add h1 h2

theorem centeredBernoulliCharacteristic_re_error_polynomial {q v t : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : v = q * (1 - q)) :
    Real.exp (-v * t ^ 2 / 2) - (centeredBernoulliCharacteristic q t).re ≤
      v * (6 * v - 1) * t ^ 4 / 24 +
        v * (1 - 5 * v - 10 * v ^ 2) * t ^ 6 / 720 + v ^ 4 * t ^ 8 / 384 := by
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hc := centeredBernoulliCharacteristic_re_lower (t := t) hq0 hq1 hv
  have he := TriangularGaussian.exp_neg_le_taylor_four (x := v * t ^ 2 / 2) (by positivity)
  have hid : -(v * t ^ 2 / 2) = -v * t ^ 2 / 2 := by ring
  rw [hid] at he
  nlinarith

theorem centeredBernoulliCharacteristic_re_error_bound {q t : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    0 ≤ Real.exp (-(q * (1 - q)) * t ^ 2 / 2) - (centeredBernoulliCharacteristic q t).re ∧
    Real.exp (-(q * (1 - q)) * t ^ 2 / 2) - (centeredBernoulliCharacteristic q t).re ≤
      q * (1 - q) * t ^ 4 / 48 := by
  have hq0 : 0 ≤ q := by nlinarith
  have hq1 : q ≤ 1 := by nlinarith
  have hv0 : 0 ≤ q * (1 - q) := by linarith
  have hv1 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  refine ⟨sub_nonneg.mpr ((Complex.re_le_norm _).trans
    (centeredBernoulliCharacteristic_norm_le_gaussian hv ht)), ?_⟩
  generalize hvdef : q * (1 - q) = v at *
  have hpoly := centeredBernoulliCharacteristic_re_error_polynomial (t := t) hq0 hq1 hvdef.symm
  have ht2 : t ^ 2 ≤ 10 := by
    have hp := Real.pi_lt_d2
    nlinarith [sq_abs t, abs_nonneg t]
  have hv2 : (9 / 40 : ℝ) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (by norm_num) hv 2
  have hv3 : v ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hv0 hv1 3
  have hcprod : v ^ 3 * t ^ 2 ≤ (1 / 4 : ℝ) ^ 3 * 10 :=
    mul_le_mul hv3 ht2 (sq_nonneg t) (by norm_num)
  have hc : 1 - 5 * v - 10 * v ^ 2 + (15 / 8 : ℝ) * v ^ 3 * t ^ 2 ≤ 0 := by
    nlinarith
  have hhigh := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ v * t ^ 6 / 720 by positivity) hc
  have hlead := mul_nonneg (show 0 ≤ v * t ^ 4 / 4 by positivity)
    (sub_nonneg.mpr hv1)
  nlinarith

/-- The finite Bernoulli error retains both sharp costs used in the analytic
budget: cubic asymmetry and quartic real-part error. -/
theorem centeredBernoulliCharacteristic_error_bound {q t : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
    ‖centeredBernoulliCharacteristic q t -
      (Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℂ)‖ ≤
      q * (1 - q) * |1 - 2 * q| * |t| ^ 3 / 6 + q * (1 - q) * t ^ 4 / 48 := by
  have hq0 : 0 ≤ q := by nlinarith
  have hq1 : q ≤ 1 := by nlinarith
  have hr := centeredBernoulliCharacteristic_re_error_bound hv ht
  have hi := centeredBernoulliCharacteristic_im_bound hq0 hq1 ht
  have hn := Complex.norm_le_abs_re_add_abs_im (centeredBernoulliCharacteristic q t -
    (Real.exp (-(q * (1 - q)) * t ^ 2 / 2) : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero, abs_of_nonpos (by linarith [hr.1] :
      (centeredBernoulliCharacteristic q t).re - Real.exp (-(q * (1 - q)) * t ^ 2 / 2) ≤ 0)] at hn
  linarith [hr.2]

theorem complex_pow_difference_bound (a b : ℂ) {r : ℝ}
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) * ‖a - b‖ * r ^ n := by
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by
      simp only [pow_succ]
      ring
    rw [he]
    calc
      _ ≤ ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ + ‖(a - b) * b ^ (n + 1)‖ := norm_add_le _ _
      _ = ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b‖ ^ (n + 1) := by
        rw [norm_mul, norm_mul, norm_pow]
      _ ≤ r * (((n + 1 : ℕ) : ℝ) * ‖a - b‖ * r ^ n) + ‖a - b‖ * r ^ (n + 1) :=
        add_le_add (mul_le_mul ha ih (norm_nonneg _) hr)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg b) hb (n + 1)) (norm_nonneg _))
      _ = _ := by push_cast; rw [pow_succ]; ring

/-- Actual finite-power error with full Gaussian damping. The zero-trial case
is included explicitly by the natural subtraction in the damping exponent. -/
theorem centeredBinomialCharacteristic_error_bound (m : ℕ) {q t : ℝ}
    (hv : 9 / 40 ≤ q * (1 - q)) (ht : |t| ≤ Real.pi) :
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
      (centeredBernoulliCharacteristic_norm_le_gaussian hv ht) hmod n
    have hgp (r : ℕ) : g ^ r = Real.exp (-(r : ℝ) * (q * (1 - q)) * t ^ 2 / 2) := by
      dsimp [g]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hgc : (g : ℂ) ^ (n + 1) =
        (Real.exp (-((n + 1 : ℕ) : ℝ) * (q * (1 - q)) * t ^ 2 / 2) : ℂ) := by
      rw [← Complex.ofReal_pow, hgp]
    rw [hgc] at hpow
    have herr := centeredBernoulliCharacteristic_error_bound hv ht
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (n + 1))) (pow_nonneg hg0 n)
    have he := hpow.trans hmul
    simpa only [Nat.add_sub_cancel, hgp] using he

#print axioms abs_sinc_sub_le_abs_square_difference
#print axioms centeredBernoulliCharacteristic_im_sinc
#print axioms centeredBernoulliCharacteristic_im_bound
#print axioms centeredBernoulliCharacteristic_re_error_polynomial
#print axioms centeredBernoulliCharacteristic_re_error_bound
#print axioms centeredBernoulliCharacteristic_error_bound
#print axioms complex_pow_difference_bound
#print axioms centeredBinomialCharacteristic_error_bound
end ForestUnimodality
