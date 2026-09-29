import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N01
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 2, coeff := fun i => (#[(13/25), (3/5), (13/25)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 1 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 2, coeff := fun i => (#[(1/10), (1/50), (1/10)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 1 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(1:ℝ)*q-0| * binomialMass 1 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 1 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 2, coeff := fun i => (#[(1/10), (1/50), (1/10)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 1 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 2, coeff := fun i => (#[(13/25), (3/5), (13/25)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 1 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(1:ℝ)*q-1| * binomialMass 1 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 1 1 positive negative positive_check negative_check hq
end J01
theorem bound (j : Fin 2) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(1:ℝ)*q-(j:ℕ)| * binomialMass 1 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N01
