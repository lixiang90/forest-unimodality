import ForestUnimodality.GaussianMassTangent
import ForestUnimodality.NegativePowerLayerBudget

/-! Averaging the Gaussian mass tangent over an arbitrary finite joint law.
The entropy and squared-offset bounds concern that same law. -/
namespace ForestUnimodality.GaussianMassBudget
open Finset KernelBudget

theorem expect_lower {Ω : Type*} (s : Finset Ω) (w Y X : Ω → ℝ)
    (good : Ω → Prop) [DecidablePred good] {R H ε : ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hY0 : ∀ x ∈ s, 0 ≤ Y x)
    (hY : expect s w Y = 1) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hent : expect s w (fun x => Y x * Real.log (Y x)) ≤ H)
    (hX : expect s w (fun x => (X x) ^ 2) ≤ R)
    (hbad : expect s w (fun x => if good x then 0 else 1) ≤ ε) :
    Real.exp (-R / 2 - 3 * H / 2) - (43 / 40) * ε ≤
      expect s w (fun x => if good x then
        Real.exp (-(X x) ^ 2 / (2 * Y x)) / Real.sqrt (Y x) else 0) := by
  let r := R / 2 + 3 * H / 2
  let T := fun x => Real.exp (-r) *
    ((1 + r) * Y x - (3 / 2) * (Y x * Real.log (Y x)) - (1 / 2) * (X x) ^ 2)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hT : Real.exp (-r) ≤ expect s w T := by
    dsimp only [T]
    rw [expect_const_mul, expect_sub, expect_sub, expect_const_mul,
      expect_const_mul, expect_const_mul, hY, mul_one]
    have hh : 1 ≤ 1 + r - (3 / 2) * expect s w (fun x => Y x * Real.log (Y x)) -
        (1 / 2) * expect s w (fun x => (X x) ^ 2) := by dsimp [r]; linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (Real.exp_pos (-r)).le
  have hp : expect s w T ≤ expect s w (fun x =>
      (if good x then Real.exp (-(X x) ^ 2 / (2 * Y x)) / Real.sqrt (Y x) else 0) +
      (43 / 40) * (if good x then 0 else 1)) := by
    apply Finset.sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (hw x hx)
    by_cases hg : good x
    · simp only [hg, if_true, mul_zero, add_zero]
      convert GaussianMassTangent.lower (x := X x) (r := r) (hY0 x hx) using 1
      all_goals first | rfl | (dsimp only [T]; ring)
    · simp only [hg, if_false, mul_one, zero_add]
      have hb := GaussianMassTangent.upper (hY0 x hx) hr
      dsimp [T]
      nlinarith [mul_nonneg (Real.exp_pos (-r)).le (sq_nonneg (X x))]
  rw [expect_add, expect_const_mul s w (fun x => if good x then 0 else 1) (43 / 40)] at hp
  have hh := mul_le_mul_of_nonneg_left hbad (by norm_num : (0 : ℝ) ≤ 43 / 40)
  have he : -r = -R / 2 - 3 * H / 2 := by dsimp [r]; ring
  rw [he] at hT
  linarith

open NegativePowerLayerBudget
variable {V : Type*} [DecidableEq V]

theorem normalized_entropy_le (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m) :
    hardCoreLayerExpectation G S I z
      (fun _ M => ((M : ℝ) / m) * Real.log ((M : ℝ) / m)) ≤ D / m := by
  have hent := hardCoreAvailable_entropy_le_of_variance G S I hIS hI hz
    (hm ▸ hm0) (hm ▸ hvar)
  rw [← hm] at hent
  have he (M : ℕ) : ((M : ℝ) / m) * Real.log ((M : ℝ) / m) =
      (1 / m) * ((M : ℝ) * Real.log M) - (Real.log m / m) * (M : ℝ) := by
    by_cases hM : M = 0
    · simp [hM]
    · rw [Real.log_div (by exact_mod_cast hM) hm0.ne']
      ring
  simp_rw [he]
  rw [layer_sub, layer_const_mul, layer_const_mul]
  have hmeanM : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ)) = m := by
    simpa only [hardCoreLayerExpectation, hardCoreAvailableMean] using hm.symm
  rw [hmeanM]
  have hh := div_le_div_of_nonneg_right hent hm0.le
  have heq : (m * Real.log m + D) / m = Real.log m + D / m := by field_simp
  rw [heq] at hh
  have heq2 : Real.log m / m * m = Real.log m := by field_simp
  rw [heq2]
  calc
    (1 / m) * hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ) * Real.log M) - Real.log m =
      hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ) * Real.log M) / m - Real.log m := by ring
    _ ≤ D / m := by linarith

#print axioms expect_lower
#print axioms normalized_entropy_le

/-- The true hard-core joint layer law satisfies the normalized Gaussian
mass bound. M and its conditional mean are allowed arbitrary correlation. -/
theorem actual_layer_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m k nu R D α ε : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (hbad : hardCoreAvailableLowerTail G S I z (α * m) ≤ ε) :
    Real.exp (-R / 2 - 3 * D / (2 * m)) - (43 / 40) * ε ≤
      hardCoreLayerExpectation G S I z (fun j M => if α * m ≤ (M : ℝ) then
        Real.exp (-((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) ^ 2 /
          (2 * ((M : ℝ) / m))) / Real.sqrt ((M : ℝ) / m) else 0) := by
  classical
  let Ω := range ((S \ I).card + 1) ×ˢ range (I.card + 1)
  let w := fun p : ℕ × ℕ => hardCoreLayerWeight G S I z p.1 p.2
  let Y := fun p : ℕ × ℕ => (p.2 : ℝ) / m
  let X := fun p : ℕ × ℕ => (k - binomialLayerMean p.1 p.2 z) / Real.sqrt (nu * m)
  let good := fun p : ℕ × ℕ => α * m ≤ (p.2 : ℝ)
  have hw : ∀ p ∈ Ω, 0 ≤ w p := fun p _ => hardCoreLayerWeight_nonneg G S I hz.le p.1 p.2
  have hy0 : ∀ p ∈ Ω, 0 ≤ Y p := fun p _ => div_nonneg (Nat.cast_nonneg _) hm0.le
  have hmeanM : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ)) = m := by
    simpa only [hardCoreLayerExpectation, hardCoreAvailableMean] using hm.symm
  have hy : expect Ω w Y = 1 := by
    have hyActual : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ) / m) = 1 := by
      have he : (fun (_ : ℕ) (M : ℕ) => (M : ℝ) / m) = fun (_ : ℕ) (M : ℕ) => (1 / m) * (M : ℝ) := by
        funext j M; ring
      rw [he, layer_const_mul, hmeanM]
      field_simp
    simpa only [hardCoreLayerExpectation_eq_expect, Ω, w, Y] using hyActual
  have hent : expect Ω w (fun p => Y p * Real.log (Y p)) ≤ D / m := by
    simpa only [hardCoreLayerExpectation_eq_expect, Ω, w, Y] using
      normalized_entropy_le G S I hIS hI hz.le hm hm0 hvarM
  have hx : expect Ω w (fun p => X p ^ 2) ≤ R := by
    have hxActual : hardCoreLayerExpectation G S I z (fun j M =>
        ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) ^ 2) ≤ R := by
      have he (j M : ℕ) : ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) ^ 2 =
          (1 / (nu * m)) * (k - binomialLayerMean j M z) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (mul_pos hnu hm0).le]
        ring
      simp_rw [he]
      rw [layer_const_mul, hardCoreLayerExpectation_centered_sq G S I hIS hI hz hmean, ← hm]
      have hh := (div_le_iff₀ (mul_pos hnu hm0)).mpr hvarL
      calc
        _ = (hardCoreVariance G S z - z / (1 + z) * (1 - z / (1 + z)) * m) /
            (nu * m) := by ring
        _ ≤ R := hh
    simpa only [hardCoreLayerExpectation_eq_expect, Ω, w, X] using hxActual
  have hb : expect Ω w (fun p => if good p then 0 else 1) ≤ ε := by
    have he : (fun p : ℕ × ℕ => if good p then (0 : ℝ) else 1) =
        fun p => if (p.2 : ℝ) < α * m then 1 else 0 := by
      funext p
      dsimp [good]
      by_cases hp : α * m ≤ (p.2 : ℝ)
      · simp [hp, not_lt.mpr hp]
      · simp [hp, lt_of_not_ge hp]
    rw [he]
    simpa only [hardCoreAvailableLowerTail, hardCoreLayerExpectation_eq_expect, Ω, w] using hbad
  have hh := expect_lower Ω w Y X good hw hy0 hy hR (div_nonneg hD hm0.le) hent hx hb
  have he : -R / 2 - 3 * (D / m) / 2 = -R / 2 - 3 * D / (2 * m) := by ring
  rw [he] at hh
  simpa only [hardCoreLayerExpectation_eq_expect, Ω, w, Y, X, good] using hh

#print axioms actual_layer_lower
end ForestUnimodality.GaussianMassBudget
