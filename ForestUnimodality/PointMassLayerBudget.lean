import ForestUnimodality.GaussianMassBudget
import ForestUnimodality.BinomialPointMassError
import ForestUnimodality.PointMassErrorEnvelope

/-! The Gaussian mass budget and a conditional Fourier error are averaged
over the same actual graph layer law. No independence between the two layer
coordinates is assumed. -/
namespace ForestUnimodality.PointMassLayerBudget
open NegativePowerLayerBudget BinomialPointMassError

theorem gaussianDensity_normalization {v m y : ℝ} (hv : 0 < v)
    (hm : 0 < m) (hy : 0 < y) (d : ℝ) :
    gaussianDensity (y * v) d =
      (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt (v * m))) *
        (Real.exp (-((d / Real.sqrt (v * m)) ^ 2) / (2 * (y / m))) /
          Real.sqrt (y / m)) := by
  have hvm : 0 < v * m := mul_pos hv hm
  have hs : Real.sqrt (y * v) = Real.sqrt (v * m) * Real.sqrt (y / m) := by
    rw [← Real.sqrt_mul hvm.le]
    congr 1
    field_simp
  have he : -((d / Real.sqrt (v * m)) ^ 2) / (2 * (y / m)) =
      -d ^ 2 / (2 * (y * v)) := by
    rw [div_pow, Real.sq_sqrt hvm.le]
    field_simp
  unfold gaussianDensity
  rw [he, hs]
  ring

theorem gaussian_prefactor_normalization {v m : ℝ} (hv : 0 < v) (hm : 0 < m) :
    Real.sqrt m * (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt (v * m))) =
      1 / Real.sqrt (2 * Real.pi * v) := by
  rw [Real.sqrt_mul hv.le, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hs : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
  field_simp

variable {V : Type*} [DecidableEq V]

theorem layer_gaussian_eq (G : SimpleGraph V) (S I : Finset V)
    {z v m α : ℝ} (hv : 0 < v) (hm : 0 < m) (ha : 0 < α * m) (k : ℕ) :
    hardCoreLayerExpectation G S I z (fun j M => if α * m ≤ (M : ℝ) then
      gaussianDensity ((M : ℝ) * v) ((k : ℝ) - binomialLayerMean j M z) else 0) =
      (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt (v * m))) *
        hardCoreLayerExpectation G S I z (fun j M => if α * m ≤ (M : ℝ) then
          Real.exp (-(((k : ℝ) - binomialLayerMean j M z) /
            Real.sqrt (v * m)) ^ 2 / (2 * ((M : ℝ) / m))) /
            Real.sqrt ((M : ℝ) / m) else 0) := by
  rw [← layer_const_mul]
  congr 1
  funext j M
  by_cases hM : α * m ≤ (M : ℝ)
  · simp only [if_pos hM]
    exact gaussianDensity_normalization hv hm (ha.trans_le hM) _
  · simp [hM]

/-- The pointwise error is required only on the retained layers. Dropped
layers contribute their true nonnegative binomial mass. -/
theorem probability_lower_of_layer_error (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m α E : ℝ}
    (hz : 0 < z) (k : ℕ) (err : ℕ → ℝ)
    (hpoint : ∀ (j M : ℕ), α * m ≤ (M : ℝ) →
      gaussianDensity ((M : ℝ) * ((z / (1 + z)) * (1 - z / (1 + z))))
        ((k : ℝ) - binomialLayerMean j M z) - err M ≤
          binomialMass M ((k : ℤ) - j) (z / (1 + z)))
    (hErr : hardCoreLayerExpectation G S I z
      (fun _ M => if α * m ≤ (M : ℝ) then err M else 0) ≤ E) :
    hardCoreLayerExpectation G S I z (fun j M => if α * m ≤ (M : ℝ) then
      gaussianDensity ((M : ℝ) * ((z / (1 + z)) * (1 - z / (1 + z))))
        ((k : ℝ) - binomialLayerMean j M z) else 0) - E ≤
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k := by
  have hq0 : 0 ≤ z / (1 + z) := by positivity
  have hq1 : z / (1 + z) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hh := layer_mono G S I hz.le
    (fun j M => (if α * m ≤ (M : ℝ) then
      gaussianDensity ((M : ℝ) * ((z / (1 + z)) * (1 - z / (1 + z))))
        ((k : ℝ) - binomialLayerMean j M z) else 0) -
      (if α * m ≤ (M : ℝ) then err M else 0))
    (fun j M => binomialMass M ((k : ℤ) - j) (z / (1 + z))) (by
      intro j M
      by_cases hM : α * m ≤ (M : ℝ)
      · simpa only [if_pos hM] using hpoint j M hM
      · simpa only [if_neg hM, sub_self] using binomialMass_nonneg M ((k : ℤ) - j) hq0 hq1)
  rw [layer_sub] at hh
  have hp := tiltedProbability_eq_binomial_mixture G S I hIS hI hz k
  change _ = hardCoreLayerExpectation G S I z
    (fun j M => binomialMass M ((k : ℤ) - j) (z / (1 + z))) at hp
  rw [← hp] at hh
  linarith

/-- Stage 900 (9.1), before replacing the Fourier error by its explicit
negative-moment upper bound. Every statistical hypothesis refers to the
same graph, fixed independent set, and activity. -/
theorem scaled_probability_lower (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m R D α ε E : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (ha : 0 < α * m) (k : ℕ) (hmean : hardCoreMean G S z = (k : ℝ))
    (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤
      R * (((z / (1 + z)) * (1 - z / (1 + z))) * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (hbad : hardCoreAvailableLowerTail G S I z (α * m) ≤ ε)
    (err : ℕ → ℝ)
    (hpoint : ∀ (j M : ℕ), α * m ≤ (M : ℝ) →
      gaussianDensity ((M : ℝ) * ((z / (1 + z)) * (1 - z / (1 + z))))
        ((k : ℝ) - binomialLayerMean j M z) - err M ≤
          binomialMass M ((k : ℤ) - j) (z / (1 + z)))
    (hErr : hardCoreLayerExpectation G S I z
      (fun _ M => if α * m ≤ (M : ℝ) then err M else 0) ≤ E) :
    (1 / Real.sqrt (2 * Real.pi * ((z / (1 + z)) * (1 - z / (1 + z))))) *
      (Real.exp (-R / 2 - 3 * D / (2 * m)) - (43 / 40) * ε) - Real.sqrt m * E ≤
      Real.sqrt m * tiltedProbability (countIndependent G S) z (partitionFunction G S z) k := by
  have hq0 : 0 < z / (1 + z) := by positivity
  have hq1 : z / (1 + z) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hv : 0 < (z / (1 + z)) * (1 - z / (1 + z)) := mul_pos hq0 (sub_pos.mpr hq1)
  have hG := GaussianMassBudget.actual_layer_lower G S I hIS hI hz hm hm0
    hmean hv hR hD hvarL hvarM hbad
  have hp := probability_lower_of_layer_error G S I hIS hI hz k err hpoint hErr
  rw [layer_gaussian_eq G S I hv hm0 ha k] at hp
  have hfactor : 0 ≤ 1 / (Real.sqrt (2 * Real.pi) *
      Real.sqrt (((z / (1 + z)) * (1 - z / (1 + z))) * m)) := by positivity
  have hl := mul_le_mul_of_nonneg_left hG hfactor
  have hall := mul_le_mul_of_nonneg_left (sub_le_sub_right hl E |>.trans hp)
    (Real.sqrt_nonneg m)
  rw [mul_sub, ← mul_assoc, gaussian_prefactor_normalization hv hm0] at hall
  exact hall

#print axioms gaussianDensity_normalization
#print axioms layer_gaussian_eq
#print axioms probability_lower_of_layer_error
#print axioms scaled_probability_lower

noncomputable def errorBudget (α m vminus eta T D : ℝ) : ℝ :=
  PointMassErrorEnvelope.costOne α m vminus eta *
      (1 + NegativePowerHermite.coefficient 1 α * D / m) +
    PointMassErrorEnvelope.costThreeHalves α m vminus *
      (1 + NegativePowerHermite.coefficient (3 / 2) α * D / m) +
    PointMassErrorEnvelope.tailCost α m vminus T

theorem layer_error_le (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m α vminus eta T D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (ha : 0 < α) (ha1 : α < 1) (ham : 1 < α * m)
    (hvm : 0 < vminus) (heta : 0 ≤ eta)
    (hcut : BernoulliCutoff.Valid (z / (1 + z)) T)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m) :
    hardCoreLayerExpectation G S I z (fun _ M => if α * m ≤ (M : ℝ) then
      PointMassErrorEnvelope.envelope α m vminus eta T ((M : ℝ) / m) else 0) ≤
        errorBudget α m vminus eta T D := by
  have h1 := single_hermite_layer_bound G S I hIS hI hz hm hm0
    (p := 1) (by norm_num) ha ha1 hvar
  have h32 := single_hermite_layer_bound G S I hIS hI hz hm hm0
    (p := 3 / 2) (by norm_num) ha ha1 hvar
  have hc1 := PointMassErrorEnvelope.costOne_nonneg (alpha := α) hm0.le hvm.le heta
  have hc32 := PointMassErrorEnvelope.costThreeHalves_nonneg hm0 ham hvm
  have ht := PointMassErrorEnvelope.tailCost_nonneg ham hvm hcut
  have he := layer_mono G S I hz
    (fun _ M => if α * m ≤ (M : ℝ) then
      PointMassErrorEnvelope.envelope α m vminus eta T ((M : ℝ) / m) else 0)
    (fun _ M => PointMassErrorEnvelope.costOne α m vminus eta *
      (if α * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-1 : ℝ) else 0) +
      PointMassErrorEnvelope.costThreeHalves α m vminus *
      (if α * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-(3 / 2 : ℝ)) else 0) +
      PointMassErrorEnvelope.tailCost α m vminus T) (by
        intro j M
        by_cases hM : α * m ≤ (M : ℝ)
        · simp only [if_pos hM, PointMassErrorEnvelope.envelope, le_refl]
        · simpa only [if_neg hM, mul_zero, zero_add] using ht)
  rw [layer_add, layer_add, layer_const_mul, layer_const_mul,
    layer_const G S I hIS hI hz] at he
  exact he.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h32 hc32)) le_rfl)

/-- The complete actual point-probability estimate (9.1)--(9.2). The Fourier
error has been proved and averaged; it is no longer a pointwise input. -/
theorem scaled_probability_lower_explicit (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z m R D α ε vminus eta T : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (ha : 0 < α) (ha1 : α < 1) (ham : 1 < α * m)
    (k : ℕ) (hmean : hardCoreMean G S z = (k : ℝ)) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤
      R * (((z / (1 + z)) * (1 - z / (1 + z))) * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (hbad : hardCoreAvailableLowerTail G S I z (α * m) ≤ ε)
    (hcut : BernoulliCutoff.Valid (z / (1 + z)) T) (hvm : 0 < vminus)
    (hv : vminus ≤ (z / (1 + z)) * (1 - z / (1 + z)))
    (heta : |1 - 2 * (z / (1 + z))| ≤ eta) :
    (1 / Real.sqrt (2 * Real.pi * ((z / (1 + z)) * (1 - z / (1 + z))))) *
      (Real.exp (-R / 2 - 3 * D / (2 * m)) - (43 / 40) * ε) -
        Real.sqrt m * errorBudget α m vminus eta T D ≤
      Real.sqrt m * tiltedProbability (countIndependent G S) z (partitionFunction G S z) k := by
  apply scaled_probability_lower G S I hIS hI hz hm hm0 (by linarith) k hmean
    hR hD hvarL hvarM hbad
    (fun M => PointMassErrorEnvelope.envelope α m vminus eta T ((M : ℝ) / m))
  · intro j M hM
    have he := PointMassErrorEnvelope.error_le_envelope M ((k : ℤ) - j)
      hm0 hcut ham hM hvm hv heta
    have hoff : (((k : ℤ) - j : ℤ) : ℝ) - (M : ℝ) * (z / (1 + z)) =
        (k : ℝ) - binomialLayerMean j M z := by
      simp only [Int.cast_sub, Int.cast_natCast, binomialLayerMean]
      ring
    rw [hoff] at he
    linarith [(abs_le.mp he).1]
  · exact layer_error_le G S I hIS hI hz.le hm hm0 ha ha1 ham hvm
      ((abs_nonneg _).trans heta) hcut hvarM

/-- Replacing the actual Gaussian prefactor by an interval lower bound
is sound only when its bracket is nonnegative. -/
theorem weaken_prefactor {v vplus B E P : ℝ} (hv : 0 < v) (hvp : v ≤ vplus)
    (hB : 0 ≤ B) (h : (1 / Real.sqrt (2 * Real.pi * v)) * B - E ≤ P) :
    (1 / Real.sqrt (2 * Real.pi * vplus)) * B - E ≤ P := by
  have hs : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.sqrt (2 * Real.pi * v) ≤ Real.sqrt (2 * Real.pi * vplus) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvp (by positivity))
  have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hs he
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_right hi hB) E).trans h

#print axioms layer_error_le
#print axioms scaled_probability_lower_explicit
#print axioms weaken_prefactor
end ForestUnimodality.PointMassLayerBudget
