import ForestUnimodality.GaussianDirectionalHalf
import ForestUnimodality.GaussianDirectionalLayerBudget

/-! Real directional envelopes, convex interpolation, and their common
actual-layer expectation budget. All statements concern the genuine
exponential kernel and the original hard-core layer law. -/
namespace ForestUnimodality.GaussianDirectionalFamily
open GaussianDirectionalEnvelope GaussianDirectionalLayerBudget NegativePowerLayerBudget

def HasEnvelope (t a B : ℝ) : Prop :=
  ∀ {y theta : ℝ}, 4 / 9 ≤ y → |theta| ≤ t → ∀ x : ℝ,
    quadratic (99 / 100) a B theta y x ≤ kernel y x theta

theorem half : HasEnvelope (1 / 2) (3 / 5) 2 := GaussianDirectionalHalf.envelope

theorem quadratic_le_of_coeff_le {a a' B B' : ℝ} (ha : a ≤ a') (hB : B ≤ B')
    (theta y x : ℝ) : quadratic (99 / 100) a' B' theta y x ≤
      quadratic (99 / 100) a B theta y x := by
  unfold quadratic
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg x),
    mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg (y - 1))]

theorem HasEnvelope.weaken {t a a' B B' : ℝ} (h : HasEnvelope t a B)
    (ha : a ≤ a') (hB : B ≤ B') : HasEnvelope t a' B' := by
  intro y theta hy ht x
  exact (quadratic_le_of_coeff_le ha hB theta y x).trans (h hy ht x)

theorem zero_of_large_coeff {a B y : ℝ} (ha : 3 / 5 ≤ a) (hB : 2 ≤ B)
    (hy : 4 / 9 ≤ y) (x : ℝ) :
    quadratic (99 / 100) a B 0 y x ≤ kernel y x 0 :=
  (quadratic_le_of_coeff_le ha hB 0 y x).trans (half hy (by norm_num) x)

theorem from_endpoints {t a B : ℝ} (ht : 0 < t)
    (hzero : ∀ {y : ℝ}, 4 / 9 ≤ y → ∀ x : ℝ,
      quadratic (99 / 100) a B 0 y x ≤ kernel y x 0)
    (hmax : ∀ {y : ℝ}, 4 / 9 ≤ y → ∀ x : ℝ,
      quadratic (99 / 100) a B t y x ≤ kernel y x t) : HasEnvelope t a B := by
  have hnonneg {y theta : ℝ} (hy : 4 / 9 ≤ y) (htheta : 0 ≤ theta) (hupper : theta ≤ t)
      (x : ℝ) : quadratic (99 / 100) a B theta y x ≤ kernel y x theta := by
    have hl : 0 ≤ theta / t := div_nonneg htheta ht.le
    have hu : theta / t ≤ 1 := (div_le_one ht).mpr hupper
    have h0 := mul_le_mul_of_nonneg_left (hzero hy x) (sub_nonneg.mpr hu)
    have h1 := mul_le_mul_of_nonneg_left (hmax hy x) hl
    have hq : quadratic (99 / 100) a B theta y x =
        (1 - theta / t) * quadratic (99 / 100) a B 0 y x +
          (theta / t) * quadratic (99 / 100) a B t y x := by
      unfold quadratic
      field_simp
      ring
    have hk : kernel y x theta = (1 - theta / t) * kernel y x 0 +
        (theta / t) * kernel y x t := by
      unfold kernel
      field_simp
      ring
    rw [hq, hk]
    exact add_le_add h0 h1
  intro y theta hy htheta x
  by_cases h0 : 0 ≤ theta
  · exact hnonneg hy h0 (abs_le.mp htheta).2 x
  · have hn := hnonneg hy (by linarith : 0 ≤ -theta)
      (by linarith [(abs_le.mp htheta).1] : -theta ≤ t) (-x)
    simpa [quadratic, kernel] using hn

theorem interpolate {t0 t1 a0 a1 B0 B1 s : ℝ}
    (h0 : HasEnvelope t0 a0 B0) (h1 : HasEnvelope t1 a1 B1)
    (ht0 : 0 < t0) (ht1 : 0 < t1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasEnvelope ((1 - s) * t0 + s * t1) ((1 - s) * a0 + s * a1) ((1 - s) * B0 + s * B1) := by
  have ht : 0 < (1 - s) * t0 + s * t1 := by
    by_cases he : s = 1
    · simpa [he] using ht1
    · have hsl : s < 1 := lt_of_le_of_ne hs1 he
      nlinarith [mul_pos (sub_pos.mpr hsl) ht0, mul_nonneg hs0 ht1.le]
  apply from_endpoints ht
  all_goals intro y hy x
  · have hl := mul_le_mul_of_nonneg_left (h0 (theta := 0) hy (by simpa using ht0.le) x) (sub_nonneg.mpr hs1)
    have hr := mul_le_mul_of_nonneg_left (h1 (theta := 0) hy (by simpa using ht1.le) x) hs0
    unfold quadratic kernel at *
    nlinarith
  · have hl := mul_le_mul_of_nonneg_left (h0 (theta := t0) hy (by rw [abs_of_pos ht0]) x) (sub_nonneg.mpr hs1)
    have hr := mul_le_mul_of_nonneg_left (h1 (theta := t1) hy (by rw [abs_of_pos ht1]) x) hs0
    have hq : quadratic (99 / 100) ((1 - s) * a0 + s * a1)
        ((1 - s) * B0 + s * B1) ((1 - s) * t0 + s * t1) y x =
        (1 - s) * quadratic (99 / 100) a0 B0 t0 y x +
          s * quadratic (99 / 100) a1 B1 t1 y x := by unfold quadratic; ring
    have hk : kernel y x ((1 - s) * t0 + s * t1) =
        (1 - s) * kernel y x t0 + s * kernel y x t1 := by unfold kernel; ring
    rw [hq, hk]
    exact add_le_add hl hr

noncomputable def badPrice (t a B : ℝ) : ℝ :=
  max 0 (99 / 100 + 5 / 18 - 25 * B / 81 + t ^ 2 / (4 * a))

theorem badPrice_nonneg (t a B : ℝ) : 0 ≤ badPrice t a B := le_max_left _ _

theorem quadratic_bad_bound {t a B y theta x : ℝ} (ha : 0 < a) (hB : 9 / 20 ≤ B)
    (_ht : 0 ≤ t) (hy : y ≤ 4 / 9) (htheta : |theta| ≤ t) :
    quadratic (99 / 100) a B theta y x ≤ badPrice t a B := by
  have htheta2 : theta ^ 2 ≤ t ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp htheta
    nlinarith [mul_nonneg (by linarith : 0 ≤ t + theta) (by linarith : 0 ≤ t - theta)]
  have hx : -theta * x - a * x ^ 2 ≤ t ^ 2 / (4 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * a)).mpr
    nlinarith [sq_nonneg (2 * a * x + theta)]
  have hy' : -(y - 1) / 2 - B * (y - 1) ^ 2 ≤ 5 / 18 - 25 * B / 81 := by
    have hB0 : 0 ≤ B := by linarith
    have hfactor : 0 ≤ B * (2 - 4 / 9 - y) - 1 / 2 := by
      nlinarith [mul_nonneg hB0 (by linarith : 0 ≤ 4 / 9 - y)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 / 9 - y) hfactor]
  have hraw : quadratic (99 / 100) a B theta y x ≤
      99 / 100 + 5 / 18 - 25 * B / 81 + t ^ 2 / (4 * a) := by unfold quadratic; linarith
  exact hraw.trans (le_max_right _ _)

variable {V : Type*} [DecidableEq V]

theorem HasEnvelope.actual_layer_lower {t a B : ℝ} (henv : HasEnvelope t a B)
    (ha : 0 < a) (hB : 9 / 20 ≤ B) (ht0 : 0 ≤ t)
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z m k nu theta R D epsilon : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu) (ht : |theta| ≤ t)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (htail : hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ epsilon) :
    99 / 100 - a * R - B * D / m - badPrice t a B * epsilon ≤
      hardCoreLayerExpectation G S I z (fun j M =>
        if (4 / 9) * m ≤ (M : ℝ) then
          kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta else 0) := by
  have hpoint (j M : ℕ) :
      quadratic (99 / 100) a B theta ((M : ℝ) / m)
          ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) -
        badPrice t a B * (if (M : ℝ) < (4 / 9) * m then 1 else 0) ≤
      if (4 / 9) * m ≤ (M : ℝ) then
        kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta else 0 := by
    by_cases hg : (4 / 9) * m ≤ (M : ℝ)
    · simp only [if_pos hg, if_neg (not_lt.mpr hg), mul_zero, sub_zero]
      exact henv ((le_div_iff₀ hm0).mpr hg) ht _
    · simp only [if_neg hg, if_pos (lt_of_not_ge hg), mul_one]
      exact sub_nonpos.mpr (quadratic_bad_bound ha hB ht0 ((div_le_iff₀ hm0).mpr (le_of_not_ge hg)) ht)
  have hraw := layer_mono G S I hz.le _ _ hpoint
  rw [layer_sub, layer_const_mul] at hraw
  change hardCoreLayerExpectation G S I z (fun j M =>
      quadratic (99 / 100) a B theta ((M : ℝ) / m)
        ((k - binomialLayerMean j M z) / Real.sqrt (nu * m))) -
      badPrice t a B * hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ _ at hraw
  have hquad := quadratic_expectation_lower G S I hIS hI hz hm hm0 hmean hnu
    ha.le (by linarith : 0 ≤ B) hvarL hvarM (H := 99 / 100) (theta := theta)
  have hcost := mul_le_mul_of_nonneg_left htail (badPrice_nonneg t a B)
  linarith

#print axioms from_endpoints
#print axioms interpolate
#print axioms quadratic_bad_bound
#print axioms HasEnvelope.actual_layer_lower
end ForestUnimodality.GaussianDirectionalFamily
