import ForestUnimodality.GaussianDirectionalT3D5
import ForestUnimodality.GaussianDirectionalT3D4
import ForestUnimodality.GaussianDirectionalT9D10
import ForestUnimodality.GaussianDirectionalT1
import ForestUnimodality.GaussianDirectionalT11D10
import ForestUnimodality.GaussianDirectionalT5D4
import ForestUnimodality.GaussianDirectionalT7D5
import ForestUnimodality.GaussianDirectionalT3D2
import ForestUnimodality.GaussianDirectionalT33D20

/-! The ten exact source parameter families, all with genuine Gaussian
semantics. Rational convex interpolation covers the source budget's
intermediate parameters without treating a saved acceptance flag as evidence. -/
namespace ForestUnimodality.GaussianDirectionalCatalogue
open GaussianDirectionalEnvelope GaussianDirectionalFamily

def parameters (i : Fin 10) : ℚ × ℚ × ℚ := match i.val with
  | 0 => (1/2, 3/5, 2)
  | 1 => (3/5, 16/25, 21/10)
  | 2 => (3/4, 69/100, 23/10)
  | 3 => (9/10, 3/4, 13/5)
  | 4 => (1, 79/100, 27/10)
  | 5 => (11/10, 21/25, 3)
  | 6 => (5/4, 9/10, 16/5)
  | 7 => (7/5, 24/25, 7/2)
  | 8 => (3/2, 1, 18/5)
  | _ => (33/20, 107/100, 4)

def thetaMax (i : Fin 10) : ℚ := (parameters i).1
def xQuadratic (i : Fin 10) : ℚ := (parameters i).2.1
def yQuadratic (i : Fin 10) : ℚ := (parameters i).2.2
def price (i : Fin 10) : ℚ :=
  max 0 (99 / 100 + 5 / 18 - 25 * yQuadratic i / 81 + thetaMax i ^ 2 / (4 * xQuadratic i))

theorem source_lower_bounds (i : Fin 10) :
    (1 / 2 : ℝ) ≤ thetaMax i ∧ (3 / 5 : ℝ) ≤ xQuadratic i ∧ (2 : ℝ) ≤ yQuadratic i := by
  fin_cases i <;> norm_num [thetaMax, xQuadratic, yQuadratic, parameters]

theorem envelope (i : Fin 10) :
    HasEnvelope (thetaMax i : ℝ) (xQuadratic i : ℝ) (yQuadratic i : ℝ) := by
  fin_cases i
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalFamily.half
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT3D5.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT3D4.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT9D10.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT1.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT11D10.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT5D4.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT7D5.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT3D2.envelope
  · simpa [HasEnvelope, thetaMax, xQuadratic, yQuadratic, parameters] using @GaussianDirectionalT33D20.envelope

theorem badPrice_eq (i : Fin 10) :
    badPrice (thetaMax i : ℝ) (xQuadratic i : ℝ) (yQuadratic i : ℝ) = (price i : ℝ) := by
  fin_cases i <;> norm_num [thetaMax, xQuadratic, yQuadratic, parameters, badPrice, price]

theorem interpolated_envelope (i j : Fin 10) (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasEnvelope (((1 - s) * thetaMax i + s * thetaMax j : ℚ) : ℝ)
      (((1 - s) * xQuadratic i + s * xQuadratic j : ℚ) : ℝ)
      (((1 - s) * yQuadratic i + s * yQuadratic j : ℚ) : ℝ) := by
  have hi := source_lower_bounds i
  have hj := source_lower_bounds j
  intro y theta hy ht x
  have h := interpolate (s := (s : ℝ)) (@envelope i) (@envelope j)
    (by linarith : (0 : ℝ) < thetaMax i) (by linarith : (0 : ℝ) < thetaMax j)
    (by exact_mod_cast hs0) (by exact_mod_cast hs1) (y := y) (theta := theta)
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] at ht ⊢
  exact h hy ht x

variable {V : Type*} [DecidableEq V]

theorem actual_layer_lower (i : Fin 10)
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    {z m k nu theta R D epsilon : ℝ}
    (hz : 0 < z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hmean : hardCoreMean G S z = k) (hnu : 0 < nu) (ht : |theta| ≤ (thetaMax i : ℝ))
    (hvarL : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤ R * (nu * m))
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * m)
    (htail : hardCoreAvailableLowerTail G S I z ((4 / 9) * m) ≤ epsilon) :
    99 / 100 - (xQuadratic i : ℝ) * R - (yQuadratic i : ℝ) * D / m - (price i : ℝ) * epsilon ≤
      hardCoreLayerExpectation G S I z (fun j M =>
        if (4 / 9) * m ≤ (M : ℝ) then
          kernel ((M : ℝ) / m) ((k - binomialLayerMean j M z) / Real.sqrt (nu * m)) theta else 0) := by
  obtain ⟨hti, hai, hBi⟩ := source_lower_bounds i
  simpa only [badPrice_eq] using (@envelope i).actual_layer_lower (by linarith) (by linarith)
    (by linarith) G S I hIS hI hz hm hm0 hmean hnu ht hvarL hvarM htail

#print axioms envelope
#print axioms interpolated_envelope
#print axioms actual_layer_lower
end ForestUnimodality.GaussianDirectionalCatalogue

