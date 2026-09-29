import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N03
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 4, coeff := fun i => (#[(6187/10000), (5893/10000), (4927/10000), (4153/10000), (3667/10000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 3 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 4, coeff := fun i => (#[(13/10000), (307/10000), (1273/10000), (2047/10000), (2533/10000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 3 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(3:ℝ)*q-0| * binomialMass 3 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 3 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 4, coeff := fun i => (#[(2659/10000), (3961/10000), (5519/10000), (5701/10000), (5179/10000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 3 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 4, coeff := fun i => (#[(3541/10000), (2239/10000), (681/10000), (499/10000), (1021/10000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 3 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(3:ℝ)*q-1| * binomialMass 3 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 3 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 4, coeff := fun i => (#[(1021/10000), (499/10000), (681/10000), (2239/10000), (3541/10000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 3 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 4, coeff := fun i => (#[(5179/10000), (5701/10000), (5519/10000), (3961/10000), (2659/10000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 3 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(3:ℝ)*q-2| * binomialMass 3 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 3 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 4, coeff := fun i => (#[(2533/10000), (2047/10000), (1273/10000), (307/10000), (13/10000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 3 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 4, coeff := fun i => (#[(3667/10000), (4153/10000), (4927/10000), (5893/10000), (6187/10000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 3 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(3:ℝ)*q-3| * binomialMass 3 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 3 3 positive negative positive_check negative_check hq
end J03
theorem bound (j : Fin 4) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(3:ℝ)*q-(j:ℕ)| * binomialMass 3 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
  · simpa using J03.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N03
