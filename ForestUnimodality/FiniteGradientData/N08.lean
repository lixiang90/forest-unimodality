import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N08
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(56044403/125000000), (448398703/1125000000), (135191489/375000000), (42128207/125000000), (40485923/125000000), (39617447/125000000), (39174683/125000000), (38954687/125000000), (38847443/125000000), (38795927/125000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(21455597/125000000), (249101297/1125000000), (97308511/375000000), (35371793/125000000), (37014077/125000000), (37882553/125000000), (38325317/125000000), (38545313/125000000), (38652557/125000000), (38704073/125000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-0| * binomialMass 8 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(36669403/62500000), (323436283/562500000), (297082907/562500000), (29139867/62500000), (25720843/62500000), (23226547/62500000), (21598963/62500000), (20611627/62500000), (20042683/62500000), (19727107/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(2080597/62500000), (25313717/562500000), (51667093/562500000), (9610133/62500000), (13029157/62500000), (15523453/62500000), (17151037/62500000), (18138373/62500000), (18707317/62500000), (19022893/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-1| * binomialMass 8 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(26786887/62500000), (98243309/187500000), (332512063/562500000), (37924783/62500000), (35771527/62500000), (32122063/62500000), (28405447/62500000), (25344943/62500000), (23117767/62500000), (21625423/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(11963113/62500000), (18006691/187500000), (16237937/562500000), (825217/62500000), (2978473/62500000), (6627937/62500000), (10344553/62500000), (13405057/62500000), (15632233/62500000), (17124577/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-2| * binomialMass 8 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(9845431/62500000), (14282479/62500000), (21082111/62500000), (28721799/62500000), (312513119/562500000), (111487357/187500000), (36295471/62500000), (33492439/62500000), (30096151/62500000), (26959759/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(28904569/62500000), (24467521/62500000), (17667889/62500000), (10028201/62500000), (36236881/562500000), (4762643/187500000), (2454529/62500000), (5257561/62500000), (8653849/62500000), (11790241/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-3| * binomialMass 8 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(576133/6250000), (417667/6250000), (473233/6250000), (841167/6250000), (13712197/56250000), (21162803/56250000), (3033833/6250000), (3401767/6250000), (3457333/6250000), (3298867/6250000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(3298867/6250000), (3457333/6250000), (3401767/6250000), (3033833/6250000), (21162803/56250000), (13712197/56250000), (841167/6250000), (473233/6250000), (417667/6250000), (576133/6250000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-4| * binomialMass 8 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 4 positive negative positive_check negative_check hq
end J04
namespace J05
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(11790241/62500000), (8653849/62500000), (5257561/62500000), (2454529/62500000), (4762643/187500000), (36236881/562500000), (10028201/62500000), (17667889/62500000), (24467521/62500000), (28904569/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 5 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(26959759/62500000), (30096151/62500000), (33492439/62500000), (36295471/62500000), (111487357/187500000), (312513119/562500000), (28721799/62500000), (21082111/62500000), (14282479/62500000), (9845431/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 5 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-5| * binomialMass 8 5 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 5 positive negative positive_check negative_check hq
end J05
namespace J06
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(17124577/62500000), (15632233/62500000), (13405057/62500000), (10344553/62500000), (6627937/62500000), (2978473/62500000), (825217/62500000), (16237937/562500000), (18006691/187500000), (11963113/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 6 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(21625423/62500000), (23117767/62500000), (25344943/62500000), (28405447/62500000), (32122063/62500000), (35771527/62500000), (37924783/62500000), (332512063/562500000), (98243309/187500000), (26786887/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 6 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-6| * binomialMass 8 6 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 6 positive negative positive_check negative_check hq
end J06
namespace J07
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(19022893/62500000), (18707317/62500000), (18138373/62500000), (17151037/62500000), (15523453/62500000), (13029157/62500000), (9610133/62500000), (51667093/562500000), (25313717/562500000), (2080597/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 7 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(19727107/62500000), (20042683/62500000), (20611627/62500000), (21598963/62500000), (23226547/62500000), (25720843/62500000), (29139867/62500000), (297082907/562500000), (323436283/562500000), (36669403/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 7 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-7| * binomialMass 8 7 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 7 positive negative positive_check negative_check hq
end J07
namespace J08
def positive : Cover := .leaf { degree := 9, coeff := fun i => (#[(38704073/125000000), (38652557/125000000), (38545313/125000000), (38325317/125000000), (37882553/125000000), (37014077/125000000), (35371793/125000000), (97308511/375000000), (249101297/1125000000), (21455597/125000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 8 8 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 9, coeff := fun i => (#[(38795927/125000000), (38847443/125000000), (38954687/125000000), (39174683/125000000), (39617447/125000000), (40485923/125000000), (42128207/125000000), (135191489/375000000), (448398703/1125000000), (56044403/125000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 8 8 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-8| * binomialMass 8 8 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 8 8 positive negative positive_check negative_check hq
end J08
theorem bound (j : Fin 9) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(8:ℝ)*q-(j:ℕ)| * binomialMass 8 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
  · simpa using J03.bound hq
  · simpa using J04.bound hq
  · simpa using J05.bound hq
  · simpa using J06.bound hq
  · simpa using J07.bound hq
  · simpa using J08.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N08
