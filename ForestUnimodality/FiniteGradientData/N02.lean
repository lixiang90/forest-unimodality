import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N02
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 3, coeff := fun i => (#[(151/250), (467/750), (131/250), (109/250)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 2 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .split (.leaf { degree := 3, coeff := fun i => (#[(2/125), (1/150), (2/75), (3/50)] : Array ℚ)[i.val]! }) (.leaf { degree := 3, coeff := fun i => (#[(3/50), (7/75), (7/50), (23/125)] : Array ℚ)[i.val]! })
theorem negative_check : negative.check (targetPolynomial 2 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(2:ℝ)*q-0| * binomialMass 2 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 2 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 3, coeff := fun i => (#[(71/500), (317/1500), (613/1500), (239/500)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 2 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 3, coeff := fun i => (#[(239/500), (613/1500), (317/1500), (71/500)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 2 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(2:ℝ)*q-1| * binomialMass 2 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 2 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .split (.leaf { degree := 3, coeff := fun i => (#[(23/125), (7/50), (7/75), (3/50)] : Array ℚ)[i.val]! }) (.leaf { degree := 3, coeff := fun i => (#[(3/50), (2/75), (1/150), (2/125)] : Array ℚ)[i.val]! })
theorem positive_check : positive.check (targetPolynomial 2 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 3, coeff := fun i => (#[(109/250), (131/250), (467/750), (151/250)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 2 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(2:ℝ)*q-2| * binomialMass 2 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 2 2 positive negative positive_check negative_check hq
end J02
theorem bound (j : Fin 3) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(2:ℝ)*q-(j:ℕ)| * binomialMass 2 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N02
