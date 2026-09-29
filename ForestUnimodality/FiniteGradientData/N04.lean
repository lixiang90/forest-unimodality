import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N04
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 5, coeff := fun i => (#[(14953/25000), (13581/25000), (457/1000), (9829/25000), (8857/25000), (8317/25000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 4 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 5, coeff := fun i => (#[(547/25000), (1919/25000), (163/1000), (5671/25000), (6643/25000), (7183/25000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 4 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(4:ℝ)*q-0| * binomialMass 4 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 4 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 5, coeff := fun i => (#[(1226/3125), (1618/3125), (1898/3125), (1826/3125), (322/625), (1394/3125)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 4 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 5, coeff := fun i => (#[(1423/6250), (639/6250), (79/6250), (223/6250), (131/1250), (1087/6250)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 4 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(4:ℝ)*q-1| * binomialMass 4 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 4 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 5, coeff := fun i => (#[(1229/12500), (1481/12500), (2789/12500), (4961/12500), (6269/12500), (6521/12500)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 4 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 5, coeff := fun i => (#[(6521/12500), (6269/12500), (4961/12500), (2789/12500), (1481/12500), (1229/12500)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 4 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(4:ℝ)*q-2| * binomialMass 4 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 4 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 5, coeff := fun i => (#[(1087/6250), (131/1250), (223/6250), (79/6250), (639/6250), (1423/6250)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 4 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 5, coeff := fun i => (#[(1394/3125), (322/625), (1826/3125), (1898/3125), (1618/3125), (1226/3125)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 4 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(4:ℝ)*q-3| * binomialMass 4 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 4 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 5, coeff := fun i => (#[(7183/25000), (6643/25000), (5671/25000), (163/1000), (1919/25000), (547/25000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 4 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 5, coeff := fun i => (#[(8317/25000), (8857/25000), (9829/25000), (457/1000), (13581/25000), (14953/25000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 4 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(4:ℝ)*q-4| * binomialMass 4 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 4 4 positive negative positive_check negative_check hq
end J04
theorem bound (j : Fin 5) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(4:ℝ)*q-(j:ℕ)| * binomialMass 4 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
  · simpa using J03.bound hq
  · simpa using J04.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N04
