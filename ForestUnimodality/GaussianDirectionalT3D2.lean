import ForestUnimodality.GaussianDirectionalFamily

import ForestUnimodality.GaussianDirectionalDataT3D2Negative

import ForestUnimodality.GaussianDirectionalDataT3D2Middle

import ForestUnimodality.GaussianDirectionalDataT3D2Positive

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ForestUnimodality.GaussianDirectionalT3D2

open GaussianDirectionalEnvelope GaussianDirectionalFamily RationalCompactification

theorem negative_identity (s x : ℝ) :
    evalSparse GaussianDirectionalDataT3D2Negative.terms s x =
      cleared3 (99 / 100) 1 (18/5) (3/2) (s + 2 / 3) (-x) := by
  norm_num [evalSparse, GaussianDirectionalDataT3D2Negative.terms, cleared3,
    quadratic, numerator3, denominator3]
  ring

theorem middle_identity (s x : ℝ) :
    evalSparse GaussianDirectionalDataT3D2Middle.terms s x =
      cleared3 (99 / 100) 1 (18/5) (3/2) (s + 2 / 3) ((s + 2 / 3) ^ 2 / (3/2) * x) := by
  norm_num [evalSparse, GaussianDirectionalDataT3D2Middle.terms, cleared3,
    quadratic, numerator3, denominator3]
  ring

theorem positive_identity (s x : ℝ) :
    evalSparse GaussianDirectionalDataT3D2Positive.terms s x =
      cleared2 (99 / 100) 1 (18/5) (3/2) (s + 2 / 3) ((s + 2 / 3) ^ 2 / (3/2) + x) := by
  norm_num [evalSparse, GaussianDirectionalDataT3D2Positive.terms, cleared2,
    quadratic, numerator2, denominator2]
  ring

theorem max_envelope_sq {s : ℝ} (hs : 2 / 3 ≤ s) (x : ℝ) :
    quadratic (99 / 100) 1 (18/5) (3/2) (s ^ 2) x ≤ kernel (s ^ 2) x (3/2) := by
  have hs0 : 0 < s := by linarith
  by_cases hx : x ≤ 0
  · apply lower_of_cleared3 hs0 (by nlinarith [sq_nonneg s])
    have h := GaussianDirectionalDataT3D2Negative.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
      (by linarith : 0 ≤ -x) (by simp)
    simpa only [negative_identity, sub_add_cancel, neg_neg] using h
  · by_cases hupper : x ≤ s ^ 2 / (3/2)
    · apply lower_of_cleared3 hs0 (by nlinarith)
      have hz : 0 ≤ x / (s ^ 2 / (3/2)) := div_nonneg (by linarith) (by positivity)
      have hz1 : x / (s ^ 2 / (3/2)) ≤ 1 := (div_le_one (by positivity)).mpr hupper
      have h := GaussianDirectionalDataT3D2Middle.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
        hz (fun _ => hz1)
      rw [middle_identity, sub_add_cancel] at h
      have he : s ^ 2 / (3/2) * (x / (s ^ 2 / (3/2))) = x := by field_simp
      rwa [he] at h
    · apply lower_of_cleared2 hs0 (by nlinarith)
      have h := GaussianDirectionalDataT3D2Positive.region_nonneg (by linarith : 0 ≤ s - 2 / 3)
        (by linarith : 0 ≤ x - s ^ 2 / (3/2)) (by simp)
      rw [positive_identity, sub_add_cancel] at h
      have he : s ^ 2 / (3/2) + (x - s ^ 2 / (3/2)) = x := by ring
      rwa [he] at h

theorem envelope : HasEnvelope (3/2) 1 (18/5) := by
  apply from_endpoints (by norm_num)
  · exact zero_of_large_coeff (by norm_num) (by norm_num)
  · intro y hy x
    have hy0 : 0 ≤ y := by linarith
    have hs : 2 / 3 ≤ Real.sqrt y := by
      nlinarith [Real.sqrt_nonneg y, Real.sq_sqrt hy0]
    simpa only [Real.sq_sqrt hy0] using max_envelope_sq hs x

theorem badPrice_eq : badPrice (3/2) 1 (18/5) = ((863/1200) : ℝ) := by
  norm_num [badPrice]

/-- The common actual hard-core layer budget specialized to this proved envelope. -/
theorem actual_layer_lower {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z m k nu theta R D epsilon : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu)
    (ht : |theta| ≤ (3/2))
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (htail : hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ epsilon) :
    99 / 100 - 1 * R - (18/5) * D / m - (863/1200) * epsilon ≤
      hardCoreLayerExpectation G S I z (fun j M =>
        if (4 / 9) * m ≤ (M : ℝ) then
          kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta else 0) := by
  simpa only [badPrice_eq] using envelope.actual_layer_lower (by norm_num) (by norm_num)
    (by norm_num) G S I hIS hI hz hm hm0 hmean hnu ht hvarL hvarM htail
#print axioms envelope
#print axioms actual_layer_lower
end ForestUnimodality.GaussianDirectionalT3D2
