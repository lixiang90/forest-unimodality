import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N07
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(48294403/100000000), (21264801/50000000), (37705993/100000000), (4328789/12500000), (32879983/100000000), (15972311/50000000), (31464373/100000000), (7806133/25000000), (31107163/100000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(13705597/100000000), (9735199/50000000), (24294007/100000000), (3421211/12500000), (29120017/100000000), (15027689/50000000), (30535627/100000000), (7693867/25000000), (30892837/100000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-0| * binomialMass 7 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(58176919/100000000), (14926589/25000000), (56376169/100000000), (24974003/50000000), (43638619/100000000), (4850807/12500000), (35564269/100000000), (16780853/50000000), (32393119/100000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(3823081/100000000), (573411/25000000), (5623831/100000000), (6025997/50000000), (18361381/100000000), (2899193/12500000), (26435731/100000000), (14219147/50000000), (29606881/100000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-1| * binomialMass 7 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(34176523/100000000), (22609361/50000000), (55363633/100000000), (7577489/12500000), (59297143/100000000), (27029351/50000000), (47849053/100000000), (10595773/25000000), (38251363/100000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(27823477/100000000), (8390639/50000000), (6636367/100000000), (172511/12500000), (2702857/100000000), (3970649/50000000), (14150947/100000000), (4904227/25000000), (23748637/100000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-2| * binomialMass 7 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(2115899/20000000), (707249/5000000), (4589909/20000000), (3588943/10000000), (9751119/20000000), (1406947/2500000), (11503529/20000000), (5443033/10000000), (9895139/20000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(10284101/20000000), (2392751/5000000), (7810091/20000000), (2611057/10000000), (2648881/20000000), (143053/2500000), (896471/20000000), (756967/10000000), (2504861/20000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-3| * binomialMass 7 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(2504861/20000000), (756967/10000000), (896471/20000000), (143053/2500000), (2648881/20000000), (2611057/10000000), (7810091/20000000), (2392751/5000000), (10284101/20000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(9895139/20000000), (5443033/10000000), (11503529/20000000), (1406947/2500000), (9751119/20000000), (3588943/10000000), (4589909/20000000), (707249/5000000), (2115899/20000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-4| * binomialMass 7 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 4 positive negative positive_check negative_check hq
end J04
namespace J05
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(23748637/100000000), (4904227/25000000), (14150947/100000000), (3970649/50000000), (2702857/100000000), (172511/12500000), (6636367/100000000), (8390639/50000000), (27823477/100000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 5 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(38251363/100000000), (10595773/25000000), (47849053/100000000), (27029351/50000000), (59297143/100000000), (7577489/12500000), (55363633/100000000), (22609361/50000000), (34176523/100000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 5 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-5| * binomialMass 7 5 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 5 positive negative positive_check negative_check hq
end J05
namespace J06
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(29606881/100000000), (14219147/50000000), (26435731/100000000), (2899193/12500000), (18361381/100000000), (6025997/50000000), (5623831/100000000), (573411/25000000), (3823081/100000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 6 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(32393119/100000000), (16780853/50000000), (35564269/100000000), (4850807/12500000), (43638619/100000000), (24974003/50000000), (56376169/100000000), (14926589/25000000), (58176919/100000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 6 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-6| * binomialMass 7 6 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 6 positive negative positive_check negative_check hq
end J06
namespace J07
def positive : Cover := .leaf { degree := 8, coeff := fun i => (#[(30892837/100000000), (7693867/25000000), (30535627/100000000), (15027689/50000000), (29120017/100000000), (3421211/12500000), (24294007/100000000), (9735199/50000000), (13705597/100000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 7 7 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 8, coeff := fun i => (#[(31107163/100000000), (7806133/25000000), (31464373/100000000), (15972311/50000000), (32879983/100000000), (4328789/12500000), (37705993/100000000), (21264801/50000000), (48294403/100000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 7 7 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-7| * binomialMass 7 7 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 7 7 positive negative positive_check negative_check hq
end J07
theorem bound (j : Fin 8) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(7:ℝ)*q-(j:ℕ)| * binomialMass 7 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
  · simpa using J03.bound hq
  · simpa using J04.bound hq
  · simpa using J05.bound hq
  · simpa using J06.bound hq
  · simpa using J07.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N07
