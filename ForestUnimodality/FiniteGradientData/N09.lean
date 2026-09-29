import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N09
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(4189547389/10000000000), (3774481717/10000000000), (3478006237/10000000000), (3300120949/10000000000), (128084101/400000000), (3150759541/10000000000), (3124754653/10000000000), (3111895093/10000000000), (3105649021/10000000000), (620531441/2000000000), (3101240029/10000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(2010452611/10000000000), (2425518283/10000000000), (2721993763/10000000000), (2899879051/10000000000), (119915899/400000000), (3049240459/10000000000), (3075245347/10000000000), (3088104907/10000000000), (3094350979/10000000000), (619468559/2000000000), (3098759971/10000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-0| * binomialMass 9 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(5746043659/10000000000), (5449568179/10000000000), (4929089003/10000000000), (873062999/2000000000), (3903919627/10000000000), (3580377331/10000000000), (3374253931/10000000000), (3251196787/10000000000), (636218063/2000000000), (3142534963/10000000000), (3121907179/10000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(453956341/10000000000), (750431821/10000000000), (1270910997/10000000000), (366937001/2000000000), (2296080373/10000000000), (2619622669/10000000000), (2825746069/10000000000), (2948803213/10000000000), (603781937/2000000000), (3057465037/10000000000), (3078092821/10000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-1| * binomialMass 9 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(1241948881/2500000000), (1419834169/2500000000), (1505482641/2500000000), (1476305689/2500000000), (1359501841/2500000000), (1212387769/2500000000), (1076838481/2500000000), (970800409/2500000000), (896020561/2500000000), (846967609/2500000000), (816472081/2500000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(308051119/2500000000), (130165831/2500000000), (44517359/2500000000), (73694311/2500000000), (190498159/2500000000), (337612231/2500000000), (473161519/2500000000), (579199591/2500000000), (653979439/2500000000), (703032391/2500000000), (733527919/2500000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-2| * binomialMass 9 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(574879051/2500000000), (803588707/2500000000), (215656463/500000000), (1329350083/2500000000), (1482101899/2500000000), (1503043939/2500000000), (1421960203/2500000000), (10332863/20000000), (1155559627/2500000000), (1038299491/2500000000), (948282571/2500000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(975120949/2500000000), (746411293/2500000000), (94343537/500000000), (220649917/2500000000), (67898101/2500000000), (46956061/2500000000), (128039797/2500000000), (2067137/20000000), (394440373/2500000000), (511700509/2500000000), (601717429/2500000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-3| * binomialMass 9 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(435040427/5000000000), (93542647/1000000000), (702646283/5000000000), (1156830419/5000000000), (1759321259/5000000000), (2348120083/5000000000), (549687631/1000000000), (2894497427/5000000000), (2827193771/5000000000), (2633453651/5000000000), (2395408907/5000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(2664959573/5000000000), (526457353/1000000000), (2397353717/5000000000), (1943169581/5000000000), (1340678741/5000000000), (751879917/5000000000), (70312369/1000000000), (205502573/5000000000), (272806229/5000000000), (466546349/5000000000), (704591093/5000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-4| * binomialMass 9 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 4 positive negative positive_check negative_check hq
end J04
namespace J05
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(704591093/5000000000), (466546349/5000000000), (272806229/5000000000), (205502573/5000000000), (70312369/1000000000), (751879917/5000000000), (1340678741/5000000000), (1943169581/5000000000), (2397353717/5000000000), (526457353/1000000000), (2664959573/5000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 5 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(2395408907/5000000000), (2633453651/5000000000), (2827193771/5000000000), (2894497427/5000000000), (549687631/1000000000), (2348120083/5000000000), (1759321259/5000000000), (1156830419/5000000000), (702646283/5000000000), (93542647/1000000000), (435040427/5000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 5 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-5| * binomialMass 9 5 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 5 positive negative positive_check negative_check hq
end J05
namespace J06
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(601717429/2500000000), (511700509/2500000000), (394440373/2500000000), (2067137/20000000), (128039797/2500000000), (46956061/2500000000), (67898101/2500000000), (220649917/2500000000), (94343537/500000000), (746411293/2500000000), (975120949/2500000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 6 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(948282571/2500000000), (1038299491/2500000000), (1155559627/2500000000), (10332863/20000000), (1421960203/2500000000), (1503043939/2500000000), (1482101899/2500000000), (1329350083/2500000000), (215656463/500000000), (803588707/2500000000), (574879051/2500000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 6 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-6| * binomialMass 9 6 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 6 positive negative positive_check negative_check hq
end J06
namespace J07
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(733527919/2500000000), (703032391/2500000000), (653979439/2500000000), (579199591/2500000000), (473161519/2500000000), (337612231/2500000000), (190498159/2500000000), (73694311/2500000000), (44517359/2500000000), (130165831/2500000000), (308051119/2500000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 7 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(816472081/2500000000), (846967609/2500000000), (896020561/2500000000), (970800409/2500000000), (1076838481/2500000000), (1212387769/2500000000), (1359501841/2500000000), (1476305689/2500000000), (1505482641/2500000000), (1419834169/2500000000), (1241948881/2500000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 7 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-7| * binomialMass 9 7 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 7 positive negative positive_check negative_check hq
end J07
namespace J08
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(3078092821/10000000000), (3057465037/10000000000), (603781937/2000000000), (2948803213/10000000000), (2825746069/10000000000), (2619622669/10000000000), (2296080373/10000000000), (366937001/2000000000), (1270910997/10000000000), (750431821/10000000000), (453956341/10000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 8 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(3121907179/10000000000), (3142534963/10000000000), (636218063/2000000000), (3251196787/10000000000), (3374253931/10000000000), (3580377331/10000000000), (3903919627/10000000000), (873062999/2000000000), (4929089003/10000000000), (5449568179/10000000000), (5746043659/10000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 8 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-8| * binomialMass 9 8 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 8 positive negative positive_check negative_check hq
end J08
namespace J09
def positive : Cover := .leaf { degree := 10, coeff := fun i => (#[(3098759971/10000000000), (619468559/2000000000), (3094350979/10000000000), (3088104907/10000000000), (3075245347/10000000000), (3049240459/10000000000), (119915899/400000000), (2899879051/10000000000), (2721993763/10000000000), (2425518283/10000000000), (2010452611/10000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 9 9 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 10, coeff := fun i => (#[(3101240029/10000000000), (620531441/2000000000), (3105649021/10000000000), (3111895093/10000000000), (3124754653/10000000000), (3150759541/10000000000), (128084101/400000000), (3300120949/10000000000), (3478006237/10000000000), (3774481717/10000000000), (4189547389/10000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 9 9 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-9| * binomialMass 9 9 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 9 9 positive negative positive_check negative_check hq
end J09
theorem bound (j : Fin 10) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(9:ℝ)*q-(j:ℕ)| * binomialMass 9 (j:ℕ) q ≤ 31/100 := by
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
  · simpa using J09.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N09
