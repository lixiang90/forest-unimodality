import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N06
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(2608841/5000000), (2291909/5000000), (1991441/5000000), (1792109/5000000), (1676441/5000000), (1613909/5000000), (11070887/35000000), (1565309/5000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(491159/5000000), (808091/5000000), (1108559/5000000), (1307891/5000000), (1423559/5000000), (1486091/5000000), (10629113/35000000), (1534691/5000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-0| * binomialMass 6 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(345013/625000), (47114/78125), (371963/625000), (166931/312500), (290113/625000), (445321/1093750), (1608241/4375000), (107081/312500)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(42487/625000), (2647/156250), (15537/625000), (26819/312500), (97387/625000), (116402/546875), (1104259/4375000), (86669/312500)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-1| * binomialMass 6 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(245173/1000000), (352777/1000000), (481773/1000000), (578977/1000000), (4182211/7000000), (3913039/7000000), (498973/1000000), (440977/1000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(374827/1000000), (267223/1000000), (138227/1000000), (41023/1000000), (157789/7000000), (426961/7000000), (121027/1000000), (179023/1000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-2| * binomialMass 6 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(10967/125000), (9833/125000), (15467/125000), (205931/875000), (336569/875000), (62033/125000), (67667/125000), (66533/125000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(66533/125000), (67667/125000), (62033/125000), (336569/875000), (205931/875000), (15467/125000), (9833/125000), (10967/125000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-3| * binomialMass 6 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(179023/1000000), (121027/1000000), (426961/7000000), (157789/7000000), (41023/1000000), (138227/1000000), (267223/1000000), (374827/1000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(440977/1000000), (498973/1000000), (3913039/7000000), (4182211/7000000), (578977/1000000), (481773/1000000), (352777/1000000), (245173/1000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-4| * binomialMass 6 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 4 positive negative positive_check negative_check hq
end J04
namespace J05
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(86669/312500), (1104259/4375000), (116402/546875), (97387/625000), (26819/312500), (15537/625000), (2647/156250), (42487/625000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 5 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(107081/312500), (1608241/4375000), (445321/1093750), (290113/625000), (166931/312500), (371963/625000), (47114/78125), (345013/625000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 5 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-5| * binomialMass 6 5 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 5 positive negative positive_check negative_check hq
end J05
namespace J06
def positive : Cover := .leaf { degree := 7, coeff := fun i => (#[(1534691/5000000), (10629113/35000000), (1486091/5000000), (1423559/5000000), (1307891/5000000), (1108559/5000000), (808091/5000000), (491159/5000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 6 6 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 7, coeff := fun i => (#[(1565309/5000000), (11070887/35000000), (1613909/5000000), (1676441/5000000), (1792109/5000000), (1991441/5000000), (2291909/5000000), (2608841/5000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 6 6 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-6| * binomialMass 6 6 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 6 6 positive negative positive_check negative_check hq
end J06
theorem bound (j : Fin 7) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(6:ℝ)*q-(j:ℕ)| * binomialMass 6 (j:ℕ) q ≤ 31/100 := by
  fin_cases j
  · simpa using J00.bound hq
  · simpa using J01.bound hq
  · simpa using J02.bound hq
  · simpa using J03.bound hq
  · simpa using J04.bound hq
  · simpa using J05.bound hq
  · simpa using J06.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N06
