import ForestUnimodality.AffineLaplace
import ForestUnimodality.MarkedMixtureVariance

/-! Genuine fixed-independent-set tilts and lower-tail pricing on the same
finite layer distribution. The affine variance bound along the path remains
an explicit source obligation. -/
namespace ForestUnimodality
open Finset Set
variable {V : Type*} [DecidableEq V]

theorem independent_tilt_weight_eq (B J : Finset V) (z u : ℝ) :
    heterogeneousWeight (independentTiltActivities B z (Real.exp (-u))) J =
      FiniteTilt.tilt (heterogeneousWeight (fun _ => z))
        (fun J => -((J ∩ B).card : ℝ)) u J := by
  classical
  let a : V → ℝ := fun v => if v ∈ B then -1 else 0
  have ha : independentTiltActivities B z (Real.exp (-u)) = tiltedActivities (fun _ => z) a u := by
    funext v
    by_cases hv : v ∈ B <;> simp [independentTiltActivities, tiltedActivities, a, hv, mul_comm]
  have hs : markedSum a J = -((J ∩ B).card : ℝ) := by
    simp only [markedSum, a, ← sum_filter]
    have hf : J.filter (fun v => v ∈ B) = J ∩ B := by ext v; simp
    rw [hf]
    simp
  rw [ha, heterogeneousWeight_tilt]
  simp only [FiniteTilt.tilt, hs]

theorem log_hardCoreLayerLaplace_le_affine (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z u A C : ℝ}
    (hz : 0 < z) (hu : 0 ≤ u) (hC : 0 < C)
    (hsource : ∀ t ∈ Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J => ((J ∩ B).card : ℝ)) ≤ A*(B.card : ℝ) +
        C*heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
          (fun J => ((J ∩ B).card : ℝ))) :
    Real.log (hardCoreLayerLaplace G S B z (Real.exp (-u))) ≤
      -hardCoreOccupiedMass G S B z * AffineLaplace.decayIntegral C u +
        A*(B.card : ℝ)/C*(u-AffineLaplace.decayIntegral C u) := by
  let w : Finset V → ℝ := heterogeneousWeight (fun _ => z)
  let X : Finset V → ℝ := fun J => ((J ∩ B).card : ℝ)
  have hweight (t : ℝ) : heterogeneousWeight (independentTiltActivities B z (Real.exp (-t))) =
      FiniteTilt.tilt w (fun J => -X J) t := by funext J; exact independent_tilt_weight_eq B J z t
  have hw : ∀ J ∈ independentSubsets G S, 0 ≤ w J := by
    intro J _
    exact heterogeneousWeight_nonneg (fun _ _ => hz.le)
  have hZ : FiniteTilt.total (independentSubsets G S) w = partitionFunction G S z := by
    simp only [FiniteTilt.total, w, heterogeneousWeight, prod_const, partitionFunction]
  have hm : FiniteTilt.mean (independentSubsets G S) w X = hardCoreOccupiedMass G S B z := by
    rw [hardCoreOccupiedMass_eq_intersection_expectation]
    simp only [FiniteTilt.mean, FiniteTilt.numerator, hZ, w, X, heterogeneousWeight, prod_const]
    congr 1
    apply sum_congr rfl
    intro J _
    ring
  have hs : ∀ t ∈ Icc 0 u, FiniteTilt.variance (independentSubsets G S)
      (FiniteTilt.tilt w (fun J => -X J) t) X ≤
        A*(B.card : ℝ)+C*FiniteTilt.mean (independentSubsets G S)
          (FiniteTilt.tilt w (fun J => -X J) t) X := by
    intro t ht
    simpa only [heterogeneousVariance, heterogeneousMean, hweight t] using hsource t ht
  have h := FiniteTilt.log_laplace_le_of_affine_variance (independentSubsets G S) w X hw
    (hZ ▸ partitionFunction_pos G S hz.le) hC hu hs
  rw [hm, hZ, ← hweight u] at h
  rw [hardCoreLayerLaplace_eq_heterogeneous_ratio G S B hBS hB hz]
  exact h

theorem hardCoreLayerLaplace_le_exp_affine (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z u A C : ℝ}
    (hz : 0 < z) (hu : 0 ≤ u) (hC : 0 < C)
    (hsource : ∀ t ∈ Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J => ((J ∩ B).card : ℝ)) ≤ A*(B.card : ℝ) +
        C*heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
          (fun J => ((J ∩ B).card : ℝ))) :
    hardCoreLayerLaplace G S B z (Real.exp (-u)) ≤
      Real.exp (-hardCoreOccupiedMass G S B z * AffineLaplace.decayIntegral C u +
        A*(B.card : ℝ)/C*(u-AffineLaplace.decayIntegral C u)) := by
  have hp : 0 < hardCoreLayerLaplace G S B z (Real.exp (-u)) := by
    rw [hardCoreLayerLaplace_eq_heterogeneous_ratio G S B hBS hB hz]
    apply div_pos _ (partitionFunction_pos G S hz.le)
    apply heterogeneousPartition_pos
    intro v _
    unfold independentTiltActivities
    split_ifs <;> positivity
  exact (Real.log_le_iff_le_exp hp).mp (log_hardCoreLayerLaplace_le_affine G S B hBS hB hz hu hC hsource)

noncomputable def hardCoreAvailableLowerTail (G : SimpleGraph V) (S B : Finset V)
    (z threshold : ℝ) : ℝ := hardCoreLayerExpectation G S B z
      (fun _ m => if (m : ℝ) < threshold then 1 else 0)

/-- Exponential Markov bound on the actual available-count law. The cutoff
is real and strict; no floor or independence approximation is introduced. -/
theorem hardCoreAvailableLowerTail_le_laplace (G : SimpleGraph V) (S B : Finset V)
    {z t : ℝ} (hz : 0 ≤ z) (ht0 : 0 < 1-z/(1+z)+z/(1+z)*t)
    (ht1 : 1-z/(1+z)+z/(1+z)*t ≤ 1) (threshold : ℝ) :
    hardCoreAvailableLowerTail G S B z threshold ≤
      Real.exp (-threshold*Real.log (1-z/(1+z)+z/(1+z)*t)) *
        hardCoreLayerLaplace G S B z t := by
  let r := 1-z/(1+z)+z/(1+z)*t
  have hp (m : ℕ) : Real.exp (threshold*Real.log r) *
      (if (m : ℝ) < threshold then 1 else 0) ≤ r^m := by
    split_ifs with hm
    · rw [mul_one]
      calc
        Real.exp (threshold*Real.log r) ≤ Real.exp ((m : ℝ)*Real.log r) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_right hm.le (Real.log_nonpos ht0.le ht1)
        _ = r^m := by rw [← Real.log_pow, Real.exp_log (pow_pos ht0 _)]
    · simpa only [mul_zero] using pow_nonneg ht0.le m
  have hs : Real.exp (threshold*Real.log r)*hardCoreAvailableLowerTail G S B z threshold ≤
      hardCoreLayerLaplace G S B z t := by
    simp only [hardCoreAvailableLowerTail, hardCoreLayerLaplace, hardCoreLayerExpectation, mul_sum]
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro m _
    have h := mul_le_mul_of_nonneg_left (hp m) (hardCoreLayerWeight_nonneg G S B hz j m)
    calc
      _ = hardCoreLayerWeight G S B z j m *
          (Real.exp (threshold*Real.log r) * (if (m : ℝ) < threshold then 1 else 0)) := by ring
      _ ≤ _ := h
  have hh := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-threshold*Real.log r)).le
  have he : Real.exp (-threshold*Real.log r)*Real.exp (threshold*Real.log r)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [← mul_assoc, he, one_mul] at hh
  exact hh

theorem hardCoreAvailableLowerTail_le_exp_affine (G : SimpleGraph V) (S B : Finset V)
    (hBS : B ⊆ S) (hB : G.IsIndepSet (B : Set V)) {z u A C : ℝ}
    (hz : 0 < z) (hu : 0 ≤ u) (hC : 0 < C)
    (hsource : ∀ t ∈ Icc 0 u,
      heterogeneousVariance G S (independentTiltActivities B z (Real.exp (-t)))
        (fun J => ((J ∩ B).card : ℝ)) ≤ A*(B.card : ℝ) +
        C*heterogeneousMean G S (independentTiltActivities B z (Real.exp (-t)))
          (fun J => ((J ∩ B).card : ℝ))) (threshold : ℝ) :
    hardCoreAvailableLowerTail G S B z threshold ≤
      Real.exp (-threshold*Real.log (1-z/(1+z)+z/(1+z)*Real.exp (-u)) -
        hardCoreOccupiedMass G S B z * AffineLaplace.decayIntegral C u +
          A*(B.card : ℝ)/C*(u-AffineLaplace.decayIntegral C u)) := by
  have hq0 : 0 < z/(1+z) := by positivity
  have hq1 : z/(1+z) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have ht0 : 0 < 1-z/(1+z)+z/(1+z)*Real.exp (-u) := by positivity
  have ht1 : 1-z/(1+z)+z/(1+z)*Real.exp (-u) ≤ 1 := by nlinarith
  have h := hardCoreAvailableLowerTail_le_laplace G S B hz.le ht0 ht1 threshold
  have hL := hardCoreLayerLaplace_le_exp_affine G S B hBS hB hz hu hC hsource
  have hh := h.trans (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)
  rw [← Real.exp_add] at hh
  convert hh using 1
  congr 1
  ring

#print axioms independent_tilt_weight_eq
#print axioms log_hardCoreLayerLaplace_le_affine
#print axioms hardCoreLayerLaplace_le_exp_affine
#print axioms hardCoreAvailableLowerTail_le_exp_affine
end ForestUnimodality
