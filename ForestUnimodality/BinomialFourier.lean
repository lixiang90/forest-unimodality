import ForestUnimodality.BinomialKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact finite Fourier formulas for the actual guarded binomial masses.
The integer index may be negative or exceed the support. No limiting or
Gaussian approximation enters these identities. -/
namespace ForestUnimodality
open Finset intervalIntegral

noncomputable def binomialCharacteristic (m : ℕ) (q t : ℝ) : ℂ :=
  ((1 - q : ℝ) + (q : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ^ m

noncomputable def periodFourier (f : ℝ → ℂ) (j : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t in -Real.pi..Real.pi, Complex.exp (-((j : ℂ) * t * Complex.I)) * f t

theorem integral_integer_frequency (n : ℤ) :
    (∫ t in -Real.pi..Real.pi, Complex.exp ((n : ℂ) * t * Complex.I)) =
      if n = 0 then 2 * (Real.pi : ℂ) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
    ring
  · have hcn : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hfun : (fun t : ℝ => Complex.exp ((n : ℂ) * t * Complex.I)) =
        (fun t : ℝ => Complex.exp (((n : ℂ) * Complex.I) * t)) := by
      funext t
      congr 1
      ring
    rw [hfun, integral_exp_mul_complex hcn, if_neg hn]
    have he : Complex.exp (((n : ℂ) * Complex.I) * (Real.pi : ℂ)) =
        Complex.exp (((n : ℂ) * Complex.I) * (-Real.pi : ℝ)) := by
      have h1 : ((n : ℂ) * Complex.I) * (Real.pi : ℂ) =
          ((n : ℝ) * Real.pi : ℝ) * Complex.I := by push_cast; ring
      have h2 : ((n : ℂ) * Complex.I) * (-Real.pi : ℝ) =
          (-((n : ℝ) * Real.pi) : ℝ) * Complex.I := by push_cast; ring
      rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
      simp [Complex.sin_int_mul_pi]
    rw [he, sub_self, zero_div]

theorem binomialMass_nat (m d : ℕ) (q : ℝ) :
    binomialMass m d q = (m.choose d : ℝ) * q ^ d * (1 - q) ^ (m - d) := by
  by_cases hd : d ≤ m
  · simp [binomialMass, hd]
  · have hc : m.choose d = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [binomialMass, hd, hc]

theorem binomialCharacteristic_eq_sum (m : ℕ) (q t : ℝ) :
    binomialCharacteristic m q t =
      ∑ d ∈ range (m + 1), (binomialMass m d q : ℂ) *
        Complex.exp ((d : ℂ) * t * Complex.I) := by
  unfold binomialCharacteristic
  rw [add_comm, add_pow]
  apply sum_congr rfl
  intro d hd
  rw [binomialMass_nat]
  push_cast
  rw [mul_pow, ← Complex.exp_nat_mul]
  have he : (d : ℂ) * ((t : ℂ) * Complex.I) = (d : ℂ) * t * Complex.I := by ring
  rw [he]
  ring

theorem continuous_binomialCharacteristic (m : ℕ) (q : ℝ) :
    Continuous (binomialCharacteristic m q) := by
  unfold binomialCharacteristic
  fun_prop

theorem periodFourier_exp (d j : ℤ) :
    periodFourier (fun t => Complex.exp ((d : ℂ) * t * Complex.I)) j =
      if d = j then 1 else 0 := by
  unfold periodFourier
  have he (t : ℝ) : Complex.exp (-((j : ℂ) * t * Complex.I)) *
      Complex.exp ((d : ℂ) * t * Complex.I) =
      Complex.exp (((d - j : ℤ) : ℂ) * t * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_integer_frequency]
  by_cases h : d = j
  · simp only [h, sub_self]
    exact inv_mul_cancel₀ (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero))
  · simp [h, sub_ne_zero.mpr h]

theorem periodFourier_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (j : ℤ) :
    periodFourier (fun t => ∑ i ∈ s, f i t) j =
      ∑ i ∈ s, periodFourier (f i) j := by
  unfold periodFourier
  simp_rw [mul_sum]
  rw [integral_finsetSum]
  · rw [mul_sum]
  · intro i hi
    exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-((j : ℂ) * t * Complex.I)) * f i t)).intervalIntegrable _ _

theorem periodFourier_const_mul (c : ℂ) (f : ℝ → ℂ) (j : ℤ) :
    periodFourier (fun t => c * f t) j = c * periodFourier f j := by
  unfold periodFourier
  simp_rw [show ∀t : ℝ, Complex.exp (-((j : ℂ) * t * Complex.I)) * (c * f t) =
    c * (Complex.exp (-((j : ℂ) * t * Complex.I)) * f t) by intro t; ring]
  rw [integral_const_mul]
  ring

theorem periodFourier_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (j : ℤ) : periodFourier (fun t => f t + g t) j =
      periodFourier f j + periodFourier g j := by
  unfold periodFourier
  simp_rw [mul_add]
  rw [integral_add]
  · ring
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-((j : ℂ) * t * Complex.I)) * f t)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-((j : ℂ) * t * Complex.I)) * g t)).intervalIntegrable _ _

/-- Exact Fourier inversion, without a support restriction on the integer index. -/
theorem binomialMass_eq_periodFourier (m : ℕ) (j : ℤ) (q : ℝ) :
    (binomialMass m j q : ℂ) = periodFourier (binomialCharacteristic m q) j := by
  have hf : binomialCharacteristic m q = (fun t : ℝ => ∑ d ∈ range (m + 1),
      (binomialMass m d q : ℂ) * Complex.exp ((d : ℂ) * t * Complex.I)) := by
    funext t
    exact binomialCharacteristic_eq_sum m q t
  rw [hf, periodFourier_sum _ _ (by intro d hd; fun_prop)]
  simp_rw [periodFourier_const_mul]
  have hi (d : ℕ) : periodFourier (fun t : ℝ =>
      Complex.exp ((d : ℂ) * t * Complex.I)) j = if (d : ℤ) = j then 1 else 0 := by
    exact periodFourier_exp d j
  simp_rw [hi]
  by_cases hj : 0 ≤ j ∧ j ≤ (m : ℤ)
  · have hmem : j.toNat ∈ range (m + 1) := by simp; omega
    rw [sum_eq_single_of_mem j.toNat hmem]
    · simp [Int.toNat_of_nonneg hj.1]
    · intro d hd hne
      have hn : (d : ℤ) ≠ j := by omega
      simp [hn]
  · have hz : binomialMass m j q = 0 := by simp [binomialMass, hj]
    rw [hz]
    simp only [Complex.ofReal_zero]
    symm
    apply sum_eq_zero
    intro d hd
    have hn : (d : ℤ) ≠ j := by have hdm := mem_range.mp hd; omega
    simp [hn]

theorem periodFourier_sub (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (j : ℤ) : periodFourier (fun t => f t - g t) j =
      periodFourier f j - periodFourier g j := by
  unfold periodFourier
  simp_rw [mul_sub]
  rw [integral_sub]
  · ring
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-((j : ℂ) * t * Complex.I)) * f t)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      Complex.exp (-((j : ℂ) * t * Complex.I)) * g t)).intervalIntegrable _ _

theorem periodFourier_shift (f : ℝ → ℂ) (l j : ℤ) :
    periodFourier (fun t => Complex.exp ((l : ℂ) * t * Complex.I) * f t) j =
      periodFourier f (j - l) := by
  unfold periodFourier
  congr 1
  apply integral_congr
  intro t ht
  dsimp only
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem latticeMultiplier_eq_exp (t : ℝ) :
    (2 - 2 * Real.cos t : ℂ) =
      2 - Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I)) := by
  rw [show -((t : ℂ) * Complex.I) = (-t : ℂ) * Complex.I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

/-- The discrete second difference has exactly the lattice multiplier; no
replacement of this multiplier by `t²` is involved. -/
theorem binomial_curvature_eq_periodFourier (m : ℕ) (j : ℤ) (q : ℝ) :
    ((2 * binomialMass m j q - binomialMass m (j - 1) q -
      binomialMass m (j + 1) q : ℝ) : ℂ) =
    periodFourier (fun t => (2 - 2 * Real.cos t : ℂ) * binomialCharacteristic m q t) j := by
  have hc := continuous_binomialCharacteristic m q
  have hf : (fun t => (2 - 2 * Real.cos t : ℂ) * binomialCharacteristic m q t) =
      (fun t : ℝ => 2 * binomialCharacteristic m q t -
        Complex.exp ((1 : ℤ) * (t : ℂ) * Complex.I) * binomialCharacteristic m q t -
        Complex.exp ((-1 : ℤ) * (t : ℂ) * Complex.I) * binomialCharacteristic m q t) := by
    funext t
    rw [latticeMultiplier_eq_exp]
    have he : (-1 : ℤ) * (t : ℂ) * Complex.I = -((t : ℂ) * Complex.I) := by push_cast; ring
    rw [he]
    simp only [Int.cast_one, one_mul]
    ring
  rw [hf, periodFourier_sub _ _ (by fun_prop) (by fun_prop),
    periodFourier_sub _ _ (by fun_prop) (by fun_prop), periodFourier_const_mul,
    periodFourier_shift, periodFourier_shift]
  rw [← binomialMass_eq_periodFourier, ← binomialMass_eq_periodFourier,
    ← binomialMass_eq_periodFourier]
  push_cast
  congr 2

noncomputable def centeredBernoulliCharacteristic (q t : ℝ) : ℂ :=
  Complex.exp (-((q : ℂ) * t * Complex.I)) *
    ((1 - q : ℝ) + (q : ℂ) * Complex.exp ((t : ℂ) * Complex.I))

theorem centered_binomial_identity (m : ℕ) (j : ℤ) (q t : ℝ) :
    Complex.exp (-((j : ℂ) * t * Complex.I)) * binomialCharacteristic m q t =
      Complex.exp (-(((j : ℝ) - m * q : ℝ) : ℂ) * t * Complex.I) *
        centeredBernoulliCharacteristic q t ^ m := by
  unfold centeredBernoulliCharacteristic binomialCharacteristic
  rw [mul_pow, ← mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact centered-frequency representation of the curvature of Bin(m,q).
This is the frequency kernel compared with the Gaussian in stage 350 §4.3. -/
theorem binomial_curvature_eq_centered_integral (m : ℕ) (j : ℤ) (q : ℝ) :
    ((2 * binomialMass m j q - binomialMass m (j - 1) q -
      binomialMass m (j + 1) q : ℝ) : ℂ) =
    (2 * (Real.pi : ℂ))⁻¹ * ∫ t in -Real.pi..Real.pi,
      (2 - 2 * Real.cos t : ℂ) *
        Complex.exp (-(((j : ℝ) - m * q : ℝ) : ℂ) * t * Complex.I) *
        centeredBernoulliCharacteristic q t ^ m := by
  rw [binomial_curvature_eq_periodFourier, periodFourier]
  congr 1
  apply integral_congr
  intro t ht
  calc
    _ = (2 - 2 * Real.cos t : ℂ) *
        (Complex.exp (-((j : ℂ) * t * Complex.I)) * binomialCharacteristic m q t) := by ring
    _ = _ := by rw [centered_binomial_identity]; ring

noncomputable def binomialKernelMultiplier (q wL wR wC t : ℝ) : ℂ :=
  (wL : ℂ) * ((1 - q : ℝ) - (q : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) +
  (wR : ℂ) * ((q : ℂ) - (1 - q : ℝ) * Complex.exp (-((t : ℂ) * Complex.I))) +
  (wC : ℂ) * (2 - 2 * Real.cos t : ℂ)

theorem continuous_binomialKernelMultiplier (q wL wR wC : ℝ) :
    Continuous (binomialKernelMultiplier q wL wR wC) := by
  unfold binomialKernelMultiplier
  fun_prop

/-- The complete weighted left/right/curvature kernel also has an exact
Fourier formula. The weights need not have a sign for this identity. -/
theorem binomialKernel_eq_periodFourier (m : ℕ) (j : ℤ) (q wL wR wC : ℝ) :
    (binomialKernel m j q wL wR wC : ℂ) =
      periodFourier (fun t => binomialKernelMultiplier q wL wR wC t *
        binomialCharacteristic m q t) j := by
  have hc := continuous_binomialCharacteristic m q
  have hf : (fun t => binomialKernelMultiplier q wL wR wC t *
      binomialCharacteristic m q t) = (fun t : ℝ =>
      (wL : ℂ) * ((1 - q : ℝ) * binomialCharacteristic m q t -
        (q : ℂ) * (Complex.exp ((1 : ℤ) * (t : ℂ) * Complex.I) * binomialCharacteristic m q t)) +
      (wR : ℂ) * ((q : ℂ) * binomialCharacteristic m q t -
        (1 - q : ℝ) * (Complex.exp ((-1 : ℤ) * (t : ℂ) * Complex.I) * binomialCharacteristic m q t)) +
      (wC : ℂ) * ((2 - 2 * Real.cos t : ℂ) * binomialCharacteristic m q t)) := by
    funext t
    unfold binomialKernelMultiplier
    have he : (-1 : ℤ) * (t : ℂ) * Complex.I = -((t : ℂ) * Complex.I) := by push_cast; ring
    rw [he]
    simp only [Int.cast_one, one_mul]
    ring
  rw [hf, periodFourier_add _ _ (by fun_prop) (by fun_prop),
    periodFourier_add _ _ (by fun_prop) (by fun_prop)]
  simp_rw [periodFourier_const_mul]
  rw [periodFourier_sub _ _ (by fun_prop) (by fun_prop),
    periodFourier_sub _ _ (by fun_prop) (by fun_prop)]
  simp_rw [periodFourier_const_mul, periodFourier_shift]
  rw [← binomial_curvature_eq_periodFourier]
  rw [← binomialMass_eq_periodFourier, ← binomialMass_eq_periodFourier,
    ← binomialMass_eq_periodFourier]
  simp only [sub_neg_eq_add, Int.reduceNeg]
  unfold binomialKernel
  push_cast
  ring

variable {V : Type*} [DecidableEq V]

noncomputable def layerMixtureCharacteristic (G : SimpleGraph V) (S I : Finset V)
    (z t : ℝ) : ℂ :=
  ∑ y ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
    (hardCoreLayerWeight G S I z y m : ℂ) *
      (Complex.exp ((y : ℂ) * t * Complex.I) *
        binomialCharacteristic m (z / (1 + z)) t)

/-- Exact finite-mixture Fourier bridge. The graph weights are the original
hard-core layer weights; no replacement distribution is introduced. -/
theorem averagedBinomialKernel_eq_periodFourier (G : SimpleGraph V) (S I : Finset V)
    (z wL wR wC : ℝ) (k : ℕ) :
    (averagedBinomialKernel G S I z wL wR wC k : ℂ) =
      periodFourier (fun t => binomialKernelMultiplier (z / (1 + z)) wL wR wC t *
        layerMixtureCharacteristic G S I z t) k := by
  unfold layerMixtureCharacteristic
  simp_rw [mul_sum]
  have hcont (y m : ℕ) : Continuous (fun t : ℝ =>
      binomialKernelMultiplier (z / (1 + z)) wL wR wC t *
        ((hardCoreLayerWeight G S I z y m : ℂ) *
          (Complex.exp ((y : ℂ) * t * Complex.I) * binomialCharacteristic m (z / (1 + z)) t))) := by
    unfold binomialKernelMultiplier binomialCharacteristic
    fun_prop
  rw [periodFourier_sum _ _ (by
    intro y hy
    apply continuous_finsetSum
    intro m hm
    exact hcont y m)]
  have hsum (y : ℕ) := periodFourier_sum (range (I.card + 1))
    (fun m t => binomialKernelMultiplier (z / (1 + z)) wL wR wC t *
      ((hardCoreLayerWeight G S I z y m : ℂ) *
        (Complex.exp ((y : ℂ) * t * Complex.I) * binomialCharacteristic m (z / (1 + z)) t)))
    (fun m _ => hcont y m) (k : ℤ)
  simp_rw [hsum]
  unfold averagedBinomialKernel
  push_cast
  apply sum_congr rfl
  intro y hy
  apply sum_congr rfl
  intro m hm
  have hf : (fun t => binomialKernelMultiplier (z / (1 + z)) wL wR wC t *
      ((hardCoreLayerWeight G S I z y m : ℂ) *
        (Complex.exp ((y : ℂ) * t * Complex.I) * binomialCharacteristic m (z / (1 + z)) t))) =
      (fun t : ℝ => (hardCoreLayerWeight G S I z y m : ℂ) *
        (Complex.exp ((y : ℂ) * t * Complex.I) *
          (binomialKernelMultiplier (z / (1 + z)) wL wR wC t *
            binomialCharacteristic m (z / (1 + z)) t))) := by funext t; ring
  rw [hf, periodFourier_const_mul]
  have hs := periodFourier_shift
    (fun t => binomialKernelMultiplier (z / (1 + z)) wL wR wC t *
      binomialCharacteristic m (z / (1 + z)) t) (y : ℤ) k
  simp only [Int.cast_natCast] at hs
  rw [hs, ← binomialKernel_eq_periodFourier]

#print axioms integral_integer_frequency
#print axioms binomialCharacteristic_eq_sum
#print axioms binomialMass_eq_periodFourier
#print axioms binomial_curvature_eq_periodFourier
#print axioms binomial_curvature_eq_centered_integral
#print axioms binomialKernel_eq_periodFourier
#print axioms averagedBinomialKernel_eq_periodFourier
end ForestUnimodality
