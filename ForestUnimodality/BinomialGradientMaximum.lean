import ForestUnimodality.BinomialEntropyBound
import Mathlib.Data.Finset.Max

/-! Actual finite-support maximizers of weighted binomial deviations. -/
namespace ForestUnimodality.BinomialGradientMaximum
open Real Finset

noncomputable def weightedDeviation (n : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  |(n : ℝ) * q - k| * binomialMass n k q

theorem mass_succ_ratio (n k : ℕ) (hk : k < n) (q : ℝ) :
    binomialMass n ((k + 1 : ℕ) : ℤ) q * (k + 1 : ℕ) * (1 - q) =
      binomialMass n k q * (n - k : ℕ) * q := by
  have hc : (n.choose (k + 1) : ℝ) * (k + 1 : ℕ) = (n.choose k : ℝ) * (n - k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  rw [binomialMass_nat, binomialMass_nat]
  have he : n - k = (n - (k + 1)) + 1 := by omega
  rw [he, pow_succ]
  rw [he] at hc
  linear_combination (q ^ (k + 1) * (1 - q) ^ (n - (k + 1)) * (1 - q)) * hc

theorem exists_maximum (n : ℕ) (q : ℝ) :
    ∃ k ≤ n, ∀ j ≤ n, weightedDeviation n q j ≤ weightedDeviation n q k := by
  classical
  have hn : (range (n + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨k, hk, he⟩ := mem_image.mp
    (((range (n + 1)).image (weightedDeviation n q)).max'_mem (hn.image _))
  refine ⟨k, by simpa using hk, ?_⟩
  intro j hj
  rw [he]
  exact le_max' _ _ (mem_image_of_mem _ (by simpa using hj))

private theorem offset_left_algebra {N K q B C : ℝ} (hK : 0 ≤ K) (_hq : 0 < q)
    (hq1 : q < 1) (hB : 0 < B) (_hz : 1 ≤ N * q - K)
    (hmax : (N * q - K - 1) * C ≤ (N * q - K) * B)
    (hratio : C * (K + 1) * (1 - q) = B * (N - K) * q) :
    (N * q - K) ^ 2 - (N * q - K) ≤ N * q * (1 - q) := by
  have hd : 0 ≤ (K + 1) * (1 - q) := by positivity
  have hm := mul_le_mul_of_nonneg_right hmax hd
  have he : (((N * q - K) ^ 2 - (N * q - K) - N * q * (1 - q)) * B) ≤ 0 := by
    calc
      _ = (N * q - K - 1) * (C * (K + 1) * (1 - q)) -
          (N * q - K) * B * ((K + 1) * (1 - q)) := by rw [hratio]; ring
      _ ≤ 0 := by nlinarith [hm]
  have hin : (N * q - K) ^ 2 - (N * q - K) - N * q * (1 - q) ≤ 0 :=
    (mul_le_mul_iff_of_pos_right hB).mp (by simpa using he)
  linarith

private theorem offset_right_algebra {N K q B C : ℝ} (hKN : K ≤ N) (hq : 0 < q)
    (_hq1 : q < 1) (hB : 0 < B) (_hz : 1 ≤ K - N * q)
    (hmax : (K - N * q - 1) * C ≤ (K - N * q) * B)
    (hratio : C * (N - K + 1) * q = B * K * (1 - q)) :
    (K - N * q) ^ 2 - (K - N * q) ≤ N * q * (1 - q) := by
  have hd : 0 ≤ (N - K + 1) * q := by positivity
  have hm := mul_le_mul_of_nonneg_right hmax hd
  have he : (((K - N * q) ^ 2 - (K - N * q) - N * q * (1 - q)) * B) ≤ 0 := by
    calc
      _ = (K - N * q - 1) * (C * (N - K + 1) * q) -
          (K - N * q) * B * ((N - K + 1) * q) := by rw [hratio]; ring
      _ ≤ 0 := by nlinarith [hm]
  have hin : (K - N * q) ^ 2 - (K - N * q) - N * q * (1 - q) ≤ 0 :=
    (mul_le_mul_iff_of_pos_right hB).mp (by simpa using he)
  linarith

theorem maximum_offset_quadratic (n k : ℕ) (hk : k ≤ n) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hmax : ∀ j ≤ n, weightedDeviation n q j ≤ weightedDeviation n q k) :
    |(n : ℝ) * q - k| ^ 2 - |(n : ℝ) * q - k| ≤ (n : ℝ) * q * (1 - q) := by
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hv : 0 ≤ (n : ℝ) * q * (1 - q) :=
    mul_nonneg (mul_nonneg hnR hq.1.le) (sub_nonneg.mpr hq.2.le)
  have hmass := BinomialEntropyBound.binomialMass_pos n k hk hq
  by_cases hsmall : |(n : ℝ) * q - k| ≤ 1
  · nlinarith [abs_nonneg ((n : ℝ) * q - k)]
  · have hlarge : 1 < |(n : ℝ) * q - k| := lt_of_not_ge hsmall
    by_cases hside : 0 ≤ (n : ℝ) * q - k
    · rw [abs_of_nonneg hside] at hlarge ⊢
      have hkn : k < n := by
        by_contra hh
        have he : (n : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_not_gt hh)
        nlinarith [mul_nonneg hnR (sub_nonneg.mpr hq.2.le)]
      have hm := hmax (k + 1) (by omega)
      dsimp [weightedDeviation] at hm
      push_cast at hm
      rw [abs_of_nonneg (by linarith : 0 ≤ (n : ℝ) * q - ((k : ℝ) + 1)),
        abs_of_nonneg hside] at hm
      have hr := mass_succ_ratio n k hkn q
      push_cast at hr
      rw [Nat.cast_sub hk] at hr
      exact offset_left_algebra hkR hq.1 hq.2 hmass hlarge.le (by convert hm using 1; ring) hr
    · have hz : 1 < (k : ℝ) - (n : ℝ) * q := by
        rw [abs_of_neg (lt_of_not_ge hside)] at hlarge
        linarith
      have hkpos : 1 ≤ k := by
        by_contra hh
        have he : k = 0 := by omega
        subst k
        norm_num at hz
        nlinarith [mul_nonneg hnR hq.1.le]
      have hm := hmax (k - 1) (by omega)
      dsimp [weightedDeviation] at hm
      rw [Nat.cast_sub hkpos] at hm
      norm_num only [Nat.cast_one] at hm
      rw [abs_of_nonpos (by linarith : (n : ℝ) * q - ((k : ℝ) - 1) ≤ 0),
        abs_of_nonpos (by linarith : (n : ℝ) * q - k ≤ 0)] at hm
      have hr := mass_succ_ratio n (k - 1) (by omega) q
      rw [Nat.sub_add_cancel hkpos] at hr
      have hdiff : n - (k - 1) = (n - k) + 1 := by omega
      rw [hdiff] at hr
      push_cast at hr
      rw [Nat.cast_sub hk] at hr
      have he := offset_right_algebra hknR hq.1 hq.2 hmass hz.le
        (by convert hm using 1 <;> ring) hr.symm
      rw [abs_of_nonpos (by linarith : (n : ℝ) * q - k ≤ 0)]
      convert he using 1
      ring

theorem offset_bound_of_quadratic {z σ : ℝ} (hσ : 0 < σ) (_hz : 0 ≤ z)
    (hquad : z ^ 2 - z ≤ σ ^ 2) : z ≤ σ + 1 / 2 + 1 / (8 * σ) := by
  let U := σ + 1 / 2 + 1 / (8 * σ)
  have hU : U ^ 2 - U = σ ^ 2 + 1 / (64 * σ ^ 2) := by
    dsimp [U]
    field_simp
    ring
  have hUhalf : 1 / 2 < U := by
    have he : 0 < 1 / (8 * σ) := by positivity
    dsimp [U]
    linarith
  have hUquad : σ ^ 2 ≤ U ^ 2 - U := by
    rw [hU]
    exact le_add_of_nonneg_right (by positivity)
  change z ≤ U
  by_contra he
  have he' : U < z := lt_of_not_ge he
  nlinarith

theorem maximum_offset_bound (n k : ℕ) (hk : k ≤ n) {q σ : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hσ : 0 < σ) (hσsq : σ ^ 2 = (n : ℝ) * q * (1 - q))
    (hmax : ∀ j ≤ n, weightedDeviation n q j ≤ weightedDeviation n q k) :
    |(n : ℝ) * q - k| ≤ σ + 1 / 2 + 1 / (8 * σ) := by
  apply offset_bound_of_quadratic hσ (abs_nonneg _)
  rw [hσsq]
  exact maximum_offset_quadratic n k hk hq hmax

#print axioms mass_succ_ratio
#print axioms exists_maximum
#print axioms maximum_offset_quadratic
#print axioms maximum_offset_bound
end ForestUnimodality.BinomialGradientMaximum
