import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N05
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 6, coeff := fun i => (#[(112421/200000), (298847/600000), (84981/200000), (74789/200000), (68741/200000), (65429/200000), (63701/200000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 5 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 6, coeff := fun i => (#[(11579/200000), (73153/600000), (39019/200000), (49211/200000), (55259/200000), (58571/200000), (60299/200000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 5 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-0| * binomialMass 5 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 5 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 6, coeff := fun i => (#[(19603/40000), (13957/24000), (14741/24000), (22627/40000), (19699/40000), (17107/40000), (3047/8000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 5 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 6, coeff := fun i => (#[(5197/40000), (923/24000), (139/24000), (2173/40000), (5101/40000), (7693/40000), (1913/8000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 5 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-1| * binomialMass 5 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 5 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 6, coeff := fun i => (#[(3113/20000), (4681/20000), (22219/60000), (2053/4000), (2293/4000), (11177/20000), (10169/20000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 5 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 6, coeff := fun i => (#[(9287/20000), (7719/20000), (14981/60000), (427/4000), (187/4000), (1223/20000), (2231/20000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 5 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-2| * binomialMass 5 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 5 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 6, coeff := fun i => (#[(2231/20000), (1223/20000), (187/4000), (427/4000), (14981/60000), (7719/20000), (9287/20000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 5 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 6, coeff := fun i => (#[(10169/20000), (11177/20000), (2293/4000), (2053/4000), (22219/60000), (4681/20000), (3113/20000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 5 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-3| * binomialMass 5 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 5 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 6, coeff := fun i => (#[(1913/8000), (7693/40000), (5101/40000), (2173/40000), (139/24000), (923/24000), (5197/40000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 5 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 6, coeff := fun i => (#[(3047/8000), (17107/40000), (19699/40000), (22627/40000), (14741/24000), (13957/24000), (19603/40000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 5 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-4| * binomialMass 5 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 5 4 positive negative positive_check negative_check hq
end J04
namespace J05
def positive : Cover := .leaf { degree := 6, coeff := fun i => (#[(60299/200000), (58571/200000), (55259/200000), (49211/200000), (39019/200000), (73153/600000), (11579/200000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 5 5 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 6, coeff := fun i => (#[(63701/200000), (65429/200000), (68741/200000), (74789/200000), (84981/200000), (298847/600000), (112421/200000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 5 5 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-5| * binomialMass 5 5 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 5 5 positive negative positive_check negative_check hq
end J05
theorem bound (j : Fin 6) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(5:ℝ)*q-(j:ℕ)| * binomialMass 5 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
  · simpa using J03.bound hq
  · simpa using J04.bound hq
  · simpa using J05.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N05
