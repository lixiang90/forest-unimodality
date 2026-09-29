import ForestUnimodality.GaussianDirectionalT1
import ForestUnimodality.GaussianDirectionalT3D2

namespace ForestUnimodality.GaussianDirectionalT7D5
open GaussianDirectionalFamily GaussianDirectionalEnvelope
theorem envelope : HasEnvelope (7/5) (24/25) (7/2) := by
  have h : HasEnvelope (7/5) (479/500) (171/50) := by
    intro y theta hy ht x
    have hi := interpolate (s := (4/5)) GaussianDirectionalT1.envelope GaussianDirectionalT3D2.envelope
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (y := y) (theta := theta)
    norm_num at hi
    exact hi hy ht x
  intro y theta hy ht x
  exact h.weaken (a' := (24/25)) (B' := (7/2)) (by norm_num) (by norm_num) hy ht x
theorem badPrice_eq : badPrice (7/5) (24/25) (7/2) = ((45227/64800) : ℝ) := by
  norm_num [badPrice]

/-- The common actual hard-core layer budget specialized to this proved envelope. -/
theorem actual_layer_lower {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z m k nu theta R D epsilon : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu)
    (ht : |theta| ≤ (7/5))
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (htail : hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ epsilon) :
    99 / 100 - (24/25) * R - (7/2) * D / m - (45227/64800) * epsilon ≤
      hardCoreLayerExpectation G S I z (fun j M =>
        if (4 / 9) * m ≤ (M : ℝ) then
          kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta else 0) := by
  simpa only [badPrice_eq] using envelope.actual_layer_lower (by norm_num) (by norm_num)
    (by norm_num) G S I hIS hI hz hm hm0 hmean hnu ht hvarL hvarM htail
#print axioms envelope
#print axioms actual_layer_lower
end ForestUnimodality.GaussianDirectionalT7D5
