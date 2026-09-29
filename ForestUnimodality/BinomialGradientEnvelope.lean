import ForestUnimodality.BinomialGradientMaximum

/-! Scalar assembly of the finite entropy bound at a localized binomial maximum. -/
namespace ForestUnimodality.BinomialGradientEnvelope
open Real

noncomputable def X (s : ℝ) : ℝ := 1 + 1 / (2 * s) + 1 / (8 * s ^ 2)
noncomputable def R (s η : ℝ) : ℝ := 1 - η * X s / s - (X s) ^ 2 / (4 * s ^ 2)
noncomputable def K (s η : ℝ) : ℝ := 1 + η * X s / (3 * s)

theorem X_pos {s : ℝ} (hs : 0 < s) : 0 < X s := by unfold X; positivity

theorem offset_le_scaled_X {s σ : ℝ} (hs : 0 < s) (hσ : s ≤ σ) :
    σ + 1 / 2 + 1 / (8 * σ) ≤ σ * X s := by
  have hσ0 : 0 < σ := hs.trans_le hσ
  have h1 : (1 : ℝ) / 2 ≤ σ / (2 * s) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have h2 : (1 : ℝ) / (8 * σ) ≤ σ / (8 * s ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [pow_le_pow_left₀ hs.le hσ 2]
  calc
    _ ≤ σ + σ / (2 * s) + σ / (8 * s ^ 2) := by linarith
    _ = _ := by unfold X; ring

theorem entropy_variance_bounds {q h s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (heta : |1 - 2 * q| ≤ η)
    (hh : |h| ≤ q * (1 - q) * X s / s) :
    q * (1 - q) * R s η ≤ (q + h) * (1 - (q + h)) ∧
      q * (1 - q) + η * |h| / 3 ≤ q * (1 - q) * K s η := by
  let v := q * (1 - q)
  have hv : 0 < v := mul_pos hq.1 (sub_pos.mpr hq.2)
  have hvq : v ≤ 1 / 4 := by dsimp [v]; nlinarith [sq_nonneg (q - 1 / 2)]
  have hx := X_pos hs
  have hh' : |h| ≤ v * X s / s := hh
  have hηh := mul_le_mul_of_nonneg_left hh' hη
  have habs : |(1 - 2 * q) * h| ≤ η * |h| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right heta (abs_nonneg h)
  have hsq0 := pow_le_pow_left₀ (abs_nonneg h) hh' 2
  have hsq : h ^ 2 ≤ v * (X s) ^ 2 / (4 * s ^ 2) := by
    rw [sq_abs] at hsq0
    have hv2 : v ^ 2 ≤ v / 4 := by nlinarith
    have hh2 := mul_le_mul_of_nonneg_right hv2 (show 0 ≤ (X s) ^ 2 / s ^ 2 by positivity)
    calc
      _ ≤ (v * X s / s) ^ 2 := hsq0
      _ ≤ _ := by convert! hh2 using 1 <;> ring
  constructor
  · dsimp [R]
    have hlow := (neg_abs_le ((1 - 2 * q) * h)).trans (le_refl _)
    dsimp [v] at hηh hsq
    ring_nf at hηh hsq ⊢
    nlinarith
  · dsimp [K]
    dsimp [v] at hηh
    ring_nf at hηh ⊢
    nlinarith

theorem quadratic_exp_bound {A : ℝ} (hA : 0 < A) (z : ℝ) :
    z ^ 2 * Real.exp (-z ^ 2 / A) ≤ A * Real.exp (-1) := by
  have he := mul_le_mul_of_nonneg_left (Real.mul_exp_neg_le_exp_neg_one (z ^ 2 / A)) hA.le
  convert! he using 1
  field_simp

theorem mass_deviation_sq_bound {D v p R K z mass entropy error : ℝ}
    (hD : 0 < D) (hv : 0 < v) (hR : 0 < R) (hK : 0 < K)
    (hp : v * R ≤ p) (hm0 : 0 ≤ mass)
    (hm : mass ≤ Real.exp (-D * entropy + error) / Real.sqrt (2 * Real.pi * D * p))
    (he : z ^ 2 / (2 * D ^ 2 * v * K) ≤ entropy) :
    (z * mass) ^ 2 ≤ K / (2 * Real.pi * R) * Real.exp (2 * error - 1) := by
  have hp0 : 0 < p := (mul_pos hv hR).trans_le hp
  have hB : 0 < 2 * Real.pi * D * p := by positivity
  have hA : 0 < D * v * K := by positivity
  have hmass := pow_le_pow_left₀ hm0 hm 2
  rw [div_pow, Real.sq_sqrt hB.le] at hmass
  have heq : Real.exp (-D * entropy + error) ^ 2 = Real.exp (-2 * D * entropy + 2 * error) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hmass
  have hrate : -2 * D * entropy ≤ -z ^ 2 / (D * v * K) := by
    have he' := (div_le_iff₀ (show 0 < 2 * D ^ 2 * v * K by positivity)).mp he
    apply (le_div_iff₀ hA).mpr
    nlinarith
  have hden : 2 * Real.pi * D * (v * R) ≤ 2 * Real.pi * D * p :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    (z * mass) ^ 2 = z ^ 2 * mass ^ 2 := mul_pow _ _ _
    _ ≤ z ^ 2 * (Real.exp (-2 * D * entropy + 2 * error) / (2 * Real.pi * D * p)) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg z)
    _ ≤ z ^ 2 * (Real.exp (-z ^ 2 / (D * v * K) + 2 * error) / (2 * Real.pi * D * p)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hB.le) (sq_nonneg z)
    _ = Real.exp (2 * error) * (z ^ 2 * Real.exp (-z ^ 2 / (D * v * K))) /
        (2 * Real.pi * D * p) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (2 * error) * ((D * v * K) * Real.exp (-1)) / (2 * Real.pi * D * p) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (quadratic_exp_bound hA z) (Real.exp_pos _).le) hB.le
    _ ≤ Real.exp (2 * error) * ((D * v * K) * Real.exp (-1)) /
        (2 * Real.pi * D * (v * R)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = K / (2 * Real.pi * R) * Real.exp (2 * error - 1) := by
      rw [show 2 * error - 1 = 2 * error + -1 by ring, Real.exp_add]
      field_simp

theorem displacement_of_localization {D v σ s h : ℝ} (hD : 0 < D) (hs : 0 < s)
    (hσ : s ≤ σ) (hσsq : σ ^ 2 = D * v)
    (hh : D * |h| ≤ σ * X s) : |h| ≤ v * X s / s := by
  have hσ0 : 0 < σ := hs.trans_le hσ
  have hx := X_pos hs
  apply (le_div_iff₀ hs).mpr
  apply (mul_le_mul_iff_of_pos_left hD).mp
  have h1 := mul_le_mul_of_nonneg_right hh hs.le
  have h2 := mul_le_mul_of_nonneg_left hσ (show 0 ≤ σ * X s by positivity)
  nlinarith [hσsq]

theorem interior_of_localization {D q qlo σ s z : ℝ} (hD : 0 < D) (hs : 0 < s)
    (hσ : s ≤ σ) (hqlo : 0 < qlo) (hv : q * (1 - q) ≤ 1 / 4)
    (hσsq : σ ^ 2 = D * (q * (1 - q)))
    (hx : X s < 4 * qlo * s) (hz : z ≤ σ * X s) : z < D * qlo := by
  have hσ0 : 0 < σ := hs.trans_le hσ
  have hDquad : 4 * σ ^ 2 ≤ D := by nlinarith [mul_le_mul_of_nonneg_left hv hD.le]
  have h1 := mul_lt_mul_of_pos_left hx hσ0
  have h2 := mul_le_mul_of_nonneg_left hσ (show 0 ≤ 4 * qlo * σ by positivity)
  have h3 := mul_le_mul_of_nonneg_left hDquad hqlo.le
  nlinarith

theorem maximum_weightedDeviation_sq_bound (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    {q s η qlo : ℝ} (hs : 0 < s) (hη : 0 ≤ η) (hqlo : 0 < qlo)
    (hq0 : qlo ≤ q) (hq1 : q ≤ 1 - qlo) (heta : |1 - 2 * q| ≤ η)
    (hvar : s ^ 2 ≤ (n : ℝ) * (q * (1 - q)))
    (hinterior : X s < 4 * qlo * s) (hR : 0 < R s η)
    (hmax : ∀ j ≤ n, BinomialGradientMaximum.weightedDeviation n q j ≤
      BinomialGradientMaximum.weightedDeviation n q k) :
    (BinomialGradientMaximum.weightedDeviation n q k) ^ 2 ≤
      K s η / (2 * Real.pi * R s η) * Real.exp (1 / (6 * n) - 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hqlo hq0, by linarith⟩
  have hv : 0 < q * (1 - q) := mul_pos hq.1 (sub_pos.mpr hq.2)
  have hv1 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  let σ := Real.sqrt ((n : ℝ) * (q * (1 - q)))
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (mul_pos hnR hv)
  have hσsq : σ ^ 2 = (n : ℝ) * (q * (1 - q)) := Real.sq_sqrt (mul_pos hnR hv).le
  have hσ : s ≤ σ := by nlinarith
  have hz0 := BinomialGradientMaximum.maximum_offset_bound n k hk hq hσ0
    (by simpa only [mul_assoc] using hσsq) hmax
  have hz : |(n : ℝ) * q - k| ≤ σ * X s := hz0.trans (offset_le_scaled_X hs hσ)
  have hint := interior_of_localization hnR hs hσ hqlo hv1 hσsq hinterior hz
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hkR : 0 < (k : ℝ) := by
    have ha := (abs_lt.mp hint).2
    nlinarith [mul_le_mul_of_nonneg_left hq0 hnR.le]
  have hknR' : (k : ℝ) < n := by
    have ha := (abs_lt.mp hint).1
    nlinarith [mul_le_mul_of_nonneg_left hq1 hnR.le]
  have hk0 : 0 < k := by exact_mod_cast hkR
  have hkn : k < n := by exact_mod_cast hknR'
  let p := (k : ℝ) / n
  let δ := p - q
  have hp0 : 0 < p := div_pos hkR hnR
  have hp1 : p < 1 := (div_lt_one hnR).mpr hknR'
  have hqd : q + δ = p := by dsimp [δ]; ring
  have hdev : |(n : ℝ) * q - k| = (n : ℝ) * |δ| := by
    have hid : (n : ℝ) * q - k = -(n : ℝ) * δ := by dsimp [δ, p]; field_simp; ring
    rw [hid, abs_mul, abs_neg, abs_of_pos hnR]
  have hδ := displacement_of_localization hnR hs hσ hσsq (by rwa [← hdev])
  have hb := entropy_variance_bounds hs hη hq heta hδ
  rw [hqd] at hb
  have hK : 0 < K s η := by unfold K; have := X_pos hs; positivity
  have hE := BernoulliEntropy.divergence_lower_asymmetry hq
    (show q + δ ∈ Set.Ioo (0 : ℝ) 1 by rw [hqd]; exact ⟨hp0, hp1⟩) heta
  rw [hqd] at hE
  have hE' : δ ^ 2 / (2 * (q * (1 - q)) * K s η) ≤ BernoulliEntropy.divergence q p := by
    have hd : 0 < 2 * (q * (1 - q) + η * |δ| / 3) := by positivity
    have hden : 2 * (q * (1 - q) + η * |δ| / 3) ≤ 2 * (q * (1 - q)) * K s η := by nlinarith [hb.2]
    exact (div_le_div_of_nonneg_left (sq_nonneg δ) hd hden).trans hE
  have hmass := BinomialEntropyBound.binomialMass_entropy_upper n k hk0 hkn hq
  have hdeneq : 2 * Real.pi * (k : ℝ) * (n - k : ℕ) / n =
      2 * Real.pi * (n : ℝ) * (p * (1 - p)) := by
    rw [Nat.cast_sub hk]
    dsimp [p]
    field_simp
  rw [hdeneq] at hmass
  have he := mass_deviation_sq_bound hnR hv hR hK hb.1
    (binomialMass_nonneg n k hq.1.le hq.2.le) hmass
    (z := |(n : ℝ) * q - k|) ?_
  · dsimp [BinomialGradientMaximum.weightedDeviation]
    convert! he using 1
    congr 2
    ring
  · rw [hdev, mul_pow, sq_abs]
    convert! hE' using 1
    field_simp

#print axioms entropy_variance_bounds
#print axioms mass_deviation_sq_bound
#print axioms maximum_weightedDeviation_sq_bound
end ForestUnimodality.BinomialGradientEnvelope
