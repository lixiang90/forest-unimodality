import ForestUnimodality.FiniteGradientCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.FiniteGradientData.N10
open FiniteGradientCertificate
namespace J00
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(3947425747/10000000000), (39709151373/110000000000), (37195698137/110000000000), (35723203253/110000000000), (34922719457/110000000000), (34507048733/110000000000), (34297787177/110000000000), (34194767813/110000000000), (34144901297/110000000000), (34121080493/110000000000), (34109821817/110000000000), (3100413343/10000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 0 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(2252574253/10000000000), (28490848627/110000000000), (31004301863/110000000000), (32476796747/110000000000), (33277280543/110000000000), (33692951267/110000000000), (33902212823/110000000000), (34005232187/110000000000), (34055098703/110000000000), (34078919507/110000000000), (34090178183/110000000000), (3099586657/10000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 0 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-0| * binomialMass 10 0 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 0 positive negative positive_check negative_check hq
end J00
namespace J01
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(276060821/500000000), (2817606593/5500000000), (506532143/1100000000), (90435661/220000000), (2051241007/5500000000), (1909010569/5500000000), (1820271667/5500000000), (353609513/1100000000), (347720651/1100000000), (156594323/500000000), (1713995131/5500000000), (155413343/500000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 1 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(33939179/500000000), (592393407/5500000000), (175467857/1100000000), (45964339/220000000), (1358758993/5500000000), (1500989431/5500000000), (1589728333/5500000000), (328390487/1100000000), (334279349/1100000000), (153405677/500000000), (1696004869/5500000000), (154586657/500000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 1 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-1| * binomialMass 10 1 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 1 positive negative positive_check negative_check hq
end J01
namespace J02
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(1086948881/2000000000), (47035661/80000000), (2616608903/4400000000), (12423739519/22000000000), (11276359243/22000000000), (10049671879/22000000000), (1799728727/4400000000), (1641941699/4400000000), (7667986651/22000000000), (665382437/2000000000), (7105344451/22000000000), (126893401/400000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 2 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(153051119/2000000000), (2564339/80000000), (111391097/4400000000), (1216260481/22000000000), (2363640757/22000000000), (3590328121/22000000000), (928271273/4400000000), (1086058301/4400000000), (5972013349/22000000000), (574617563/2000000000), (6534655549/22000000000), (121106599/400000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 2 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-2| * binomialMass 10 2 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 2 positive negative positive_check negative_check hq
end J02
namespace J03
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(31/100), (279831983/687500000), (173269483/343750000), (396304493/687500000), (378627/625000), (81244399/137500000), (17092331/31250000), (338655209/687500000), (9476506/21484375), (54856891/137500000), (25277531/68750000), (21625423/62500000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 3 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(31/100), (146418017/687500000), (39855517/343750000), (29945507/687500000), (8873/625000), (4005601/137500000), (2282669/31250000), (87594791/687500000), (7687613/42968750), (30393109/137500000), (17347469/68750000), (17124577/62500000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 3 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-3| * binomialMass 10 3 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 3 positive negative positive_check negative_check hq
end J03
namespace J04
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(109879051/1000000000), (147997327/1000000000), (2461127201/11000000000), (725124361/2200000000), (195316081/440000000), (5907057269/11000000000), (6451688753/11000000000), (6490307069/11000000000), (1232218501/2200000000), (1129834177/2200000000), (5106068801/11000000000), (420270727/1000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 4 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(510120949/1000000000), (472002673/1000000000), (4358872799/11000000000), (638875639/2200000000), (77483919/440000000), (912942731/11000000000), (368311247/11000000000), (329692931/11000000000), (131781499/2200000000), (234165823/2200000000), (1713931199/11000000000), (199729273/1000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 4 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-4| * binomialMass 10 4 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 4 positive negative positive_check negative_check hq
end J04
namespace J05
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(130201637/1250000000), (966630493/13750000000), (71857337/1250000000), (1095358393/13750000000), (1999432207/13750000000), (3434577493/13750000000), (5090422507/13750000000), (6525567793/13750000000), (7429641607/13750000000), (703142663/1250000000), (7558369507/13750000000), (644798363/1250000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 5 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(644798363/1250000000), (7558369507/13750000000), (703142663/1250000000), (7429641607/13750000000), (6525567793/13750000000), (5090422507/13750000000), (3434577493/13750000000), (1999432207/13750000000), (1095358393/13750000000), (71857337/1250000000), (966630493/13750000000), (130201637/1250000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 5 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-5| * binomialMass 10 5 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 5 positive negative positive_check negative_check hq
end J05
namespace J06
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(199729273/1000000000), (1713931199/11000000000), (234165823/2200000000), (131781499/2200000000), (329692931/11000000000), (368311247/11000000000), (912942731/11000000000), (77483919/440000000), (638875639/2200000000), (4358872799/11000000000), (472002673/1000000000), (510120949/1000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 6 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(420270727/1000000000), (5106068801/11000000000), (1129834177/2200000000), (1232218501/2200000000), (6490307069/11000000000), (6451688753/11000000000), (5907057269/11000000000), (195316081/440000000), (725124361/2200000000), (2461127201/11000000000), (147997327/1000000000), (109879051/1000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 6 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-6| * binomialMass 10 6 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 6 positive negative positive_check negative_check hq
end J06
namespace J07
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(17124577/62500000), (17347469/68750000), (30393109/137500000), (7687613/42968750), (87594791/687500000), (2282669/31250000), (4005601/137500000), (8873/625000), (29945507/687500000), (39855517/343750000), (146418017/687500000), (31/100)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 7 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(21625423/62500000), (25277531/68750000), (54856891/137500000), (9476506/21484375), (338655209/687500000), (17092331/31250000), (81244399/137500000), (378627/625000), (396304493/687500000), (173269483/343750000), (279831983/687500000), (31/100)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 7 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-7| * binomialMass 10 7 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 7 positive negative positive_check negative_check hq
end J07
namespace J08
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(121106599/400000000), (6534655549/22000000000), (574617563/2000000000), (5972013349/22000000000), (1086058301/4400000000), (928271273/4400000000), (3590328121/22000000000), (2363640757/22000000000), (1216260481/22000000000), (111391097/4400000000), (2564339/80000000), (153051119/2000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 8 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(126893401/400000000), (7105344451/22000000000), (665382437/2000000000), (7667986651/22000000000), (1641941699/4400000000), (1799728727/4400000000), (10049671879/22000000000), (11276359243/22000000000), (12423739519/22000000000), (2616608903/4400000000), (47035661/80000000), (1086948881/2000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 8 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-8| * binomialMass 10 8 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 8 positive negative positive_check negative_check hq
end J08
namespace J09
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(154586657/500000000), (1696004869/5500000000), (153405677/500000000), (334279349/1100000000), (328390487/1100000000), (1589728333/5500000000), (1500989431/5500000000), (1358758993/5500000000), (45964339/220000000), (175467857/1100000000), (592393407/5500000000), (33939179/500000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 9 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(155413343/500000000), (1713995131/5500000000), (156594323/500000000), (347720651/1100000000), (353609513/1100000000), (1820271667/5500000000), (1909010569/5500000000), (2051241007/5500000000), (90435661/220000000), (506532143/1100000000), (2817606593/5500000000), (276060821/500000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 9 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-9| * binomialMass 10 9 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 9 positive negative positive_check negative_check hq
end J09
namespace J10
def positive : Cover := .leaf { degree := 11, coeff := fun i => (#[(3099586657/10000000000), (34090178183/110000000000), (34078919507/110000000000), (34055098703/110000000000), (34005232187/110000000000), (33902212823/110000000000), (33692951267/110000000000), (33277280543/110000000000), (32476796747/110000000000), (31004301863/110000000000), (28490848627/110000000000), (2252574253/10000000000)] : Array ℚ)[i.val]! }
theorem positive_check : positive.check (targetPolynomial 10 10 true) (3/10) (7/10) = true := by
  decide +kernel
def negative : Cover := .leaf { degree := 11, coeff := fun i => (#[(3100413343/10000000000), (34109821817/110000000000), (34121080493/110000000000), (34144901297/110000000000), (34194767813/110000000000), (34297787177/110000000000), (34507048733/110000000000), (34922719457/110000000000), (35723203253/110000000000), (37195698137/110000000000), (39709151373/110000000000), (3947425747/10000000000)] : Array ℚ)[i.val]! }
theorem negative_check : negative.check (targetPolynomial 10 10 false) (3/10) (7/10) = true := by
  decide +kernel
theorem bound {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-10| * binomialMass 10 10 q ≤ 31/100 := by
  simpa using weightedDeviation_le_of_checks 10 10 positive negative positive_check negative_check hq
end J10
theorem bound (j : Fin 11) {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(10:ℝ)*q-(j:ℕ)| * binomialMass 10 (j:ℕ) q ≤ 31/100 := by
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
  · simpa using J10.bound hq
#print axioms bound
end ForestUnimodality.FiniteGradientData.N10
