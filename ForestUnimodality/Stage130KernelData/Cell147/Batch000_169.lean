import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell147.Parameters
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch000_049
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch050_099
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch100_149
import ForestUnimodality.BinomialMassData.Q94503_178928.Batch150_199
import ForestUnimodality.BinomialMassData.Q28_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q28_53.Batch050_099
import ForestUnimodality.BinomialMassData.Q28_53.Batch100_149
import ForestUnimodality.BinomialMassData.Q28_53.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree000.table
  base := (439707948148695213169645513/5000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78695609751235125889357036250000000000)
      linear := (-5670146925041817274545930000000000000)
      constant := (109926987037173803292411378250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree000.table
  base := (439707948148695213169645513/5000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78695609751235125889357036250000000000)
      linear := (-5670146925041817274545930000000000000)
      constant := (109926987037173803292411378250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree001.table
  base := (239534682973189440175449778190335627281691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-44420247219329324987340695415055843125000000000)
      constant := (29968564642972431007417204225016797953471641765899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree001.table
  base := (478963715680733737318202234260335141713521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-1995968099632866546910489607680000000000000)
      constant := (1345969972195834911291091532649601413073280489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49919836057822463971/100000000000000000000)
  directionHi := (12479959014455615993/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree002.table
  base := (277926761579378047573478033969515287159993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-172008143461312092173474087957585212500000000000)
      constant := (34851223158446534550440074237896000156948235823577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree002.table
  base := (277820859379924423734876795700241304235223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-3864516657566193376027383076400000000000000)
      constant := (782507741424234886018947927009337823596741407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49919836057822463971/100000000000000000000)
  centralHi := (12479959014455615993/25000000000000000000)
  directionLo := (70597309184413988407/100000000000000000000)
  directionHi := (8824663648051748551/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree003.table
  base := (86993383822397846954426686298215345889797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-127587896241982767186133392542529369375000000000)
      constant := (10982675913361889212807485853723538918096419383733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree003.table
  base := (173905039567169055813227856992751907909819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-5733065215499520205144276545120000000000000)
      constant := (493143413876297887529609704117760109318681571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70597309184413988407/100000000000000000000)
  centralHi := (8824663648051748551/12500000000000000000)
  directionLo := (43231846178828679307/50000000000000000000)
  directionHi := (17292738471531471723/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree004.table
  base := (11794617606776040374223577336745189744719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-169171720753309488285529741106266132500000000000)
      constant := (7556840641436250331433433883297364727475492942955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree004.table
  base := (23577572290324669016886814697611312893897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-7601613773432847034261170013840000000000000)
      constant := (339313528584542309514157706853550889594783365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43231846178828679307/50000000000000000000)
  centralHi := (17292738471531471723/20000000000000000000)
  directionLo := (99839672115644927943/100000000000000000000)
  directionHi := (12479959014455615993/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree005.table
  base := (21472869870395345462216872711397798174513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-105377772632318104692463044835001447812500000000)
      constant := (2826400128854153697595979655549297529541056728857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree005.table
  base := (42925138052015917968010678561278305371469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-4735081165683086931689031741280000000000000)
      constant := (126914738553344788578576110923030759788456421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99839672115644927943/100000000000000000000)
  centralHi := (12479959014455615993/12500000000000000000)
  directionLo := (55812073425468075873/50000000000000000000)
  directionHi := (111624146850936151747/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree006.table
  base := (33078831665866479297742318848888328496929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-252339369775962930484322438233739658750000000000)
      constant := (4541144382494788963223662561113456321530703809281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree006.table
  base := (13225546977895913045805436729151344400571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-11338710889299500692494956951280000000000000)
      constant := (203925542327263559001247518475650632106019695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55812073425468075873/50000000000000000000)
  centralHi := (111624146850936151747/100000000000000000000)
  directionLo := (122278126385053966621/100000000000000000000)
  directionHi := (61139063192526983311/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree007.table
  base := (26500697404658167234480951001964086578373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-293923194287289651583718786797476421875000000000)
      constant := (3862743882676785775616093482496534368159492081397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree007.table
  base := (10595722803953726014139934213879668568007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-13207259447232827521611850420000000000000000)
      constant := (173473503025216345820703560237299945037658315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122278126385053966621/100000000000000000000)
  centralHi := (61139063192526983311/50000000000000000000)
  directionLo := (132075471698113207547/100000000000000000000)
  directionHi := (33018867924528301887/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree008.table
  base := (43551623585478690409091884148591082741827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-671014037597232745366230270722426370000000000000)
      constant := (6876145429488980156859506520568102310149603546403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree008.table
  base := (2720836505745302911913292232307089591197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-1884476000645769293841092986090000000000000)
      constant := (19301606388449181890436663692941229323344746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132075471698113207547/100000000000000000000)
  centralHi := (33018867924528301887/25000000000000000000)
  directionLo := (70597309184413988407/50000000000000000000)
  directionHi := (28238923673765595363/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree009.table
  base := (2271134428481560172620480789120405065899/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-94272710827485773445627870981237487031250000000)
      constant := (793799930771842373745526588011669928389032093722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree009.table
  base := (36322902933484676921465263130718856898041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-16944356563099481179845637357440000000000000)
      constant := (142616766211944809040368441502989269026597169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70597309184413988407/50000000000000000000)
  centralHi := (28238923673765595363/20000000000000000000)
  directionLo := (29951901634693478383/20000000000000000000)
  directionHi := (37439877043366847979/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree010.table
  base := (30580151100295345744398704671034913617781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-837349335642539629763815664977373422500000000000)
      constant := (6050600174919030905916248581678747173980083173909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree010.table
  base := (30567001723510013669741765736800740066111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-18812905121032808008962530826160000000000000)
      constant := (135893754120255263902943445900273278845705799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29951901634693478383/20000000000000000000)
  centralHi := (37439877043366847979/25000000000000000000)
  directionLo := (19732547795614989339/12500000000000000000)
  directionHi := (157860382364919914713/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree011.table
  base := (1615064425380049580746996195648374611139/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-115064623083149133995326045263105868593750000000)
      constant := (740268431758027529158144664604453016998648158442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree011.table
  base := (12914734389091022347284372201653673429851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-10340726839483067419039712147440000000000000)
      constant := (66509248106338888203752416107005168664451459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19732547795614989339/12500000000000000000)
  centralHi := (157860382364919914713/100000000000000000000)
  directionLo := (16556536579985135963/10000000000000000000)
  directionHi := (165565365799851359631/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree012.table
  base := (21860111950945133953170538857670151887259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1003684633687846514161401059232320475000000000000)
      constant := (5932441023370927871660358428865019438697996150651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree012.table
  base := (546245947043878762842394621729176621271/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-2818750279612432708399539720450000000000000)
      constant := (16657417861147862678551398348106285645751195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16556536579985135963/10000000000000000000)
  centralHi := (165565365799851359631/100000000000000000000)
  directionLo := (172927384715314717229/100000000000000000000)
  directionHi := (17292738471531471723/10000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree013.table
  base := (18469835261633660892685760356232918210721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1086852282710499956360193756359794001250000000000)
      constant := (6060526005748708817425829729498749745981875081569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree013.table
  base := (1846066301954433341756191889614625147261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-12209275397416394248156605616160000000000000)
      constant := (68072969147260240199752874915797410193280745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172927384715314717229/100000000000000000000)
  centralHi := (17292738471531471723/10000000000000000000)
  directionLo := (89994264284617514071/50000000000000000000)
  directionHi := (179988528569235028143/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree014.table
  base := (3110891052413990337896370759815252390441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1170019931733153398558986453487267527500000000000)
      constant := (6291927331105383957641198684422103636304149723245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree014.table
  base := (777312878477116851698121523545192887669/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-6571774838191528831357526175260000000000000)
      constant := (35338329676868032542816368518192234107311105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89994264284617514071/50000000000000000000)
  centralHi := (179988528569235028143/100000000000000000000)
  directionLo := (186782923332295572483/100000000000000000000)
  directionHi := (46695730833073893121/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree015.table
  base := (13028969451490954490533062559288486348091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1253187580755806840757779150614741053750000000000)
      constant := (6616014630131803917486561066035140664283549085499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree015.table
  base := (6510824563434098583532666312981543762983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-14077823955349721077273499084880000000000000)
      constant := (74321398321363611158799154058365156430219247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186782923332295572483/100000000000000000000)
  centralHi := (46695730833073893121/25000000000000000000)
  directionLo := (19333869369735091289/10000000000000000000)
  directionHi := (193338693697350912891/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree016.table
  base := (10827997920174321333256146960420210586829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1336355229778460282956571847742214580000000000000)
      constant := (7024611524727225728881065800436575931261224870381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree016.table
  base := (10821473356791338636245786951481344722377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-30024196468632768983663891638480000000000000)
      constant := (157830763684027571156129080870231097325156993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19333869369735091289/10000000000000000000)
  centralHi := (193338693697350912891/100000000000000000000)
  directionLo := (99839672115644927943/50000000000000000000)
  directionHi := (199679344231289855887/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree017.table
  base := (4449811562641054770638704576943937699141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-709761439400556862577682272434844053125000000000)
      constant := (3755612616757100335453062930821075070556315448949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree017.table
  base := (4446910680953812635339642672027997610637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-15946372513283047906390392553600000000000000)
      constant := (84385703869282479091505874535406645288279333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99839672115644927943/50000000000000000000)
  centralHi := (199679344231289855887/100000000000000000000)
  directionLo := (205824756879919139839/100000000000000000000)
  directionHi := (40200147828109207/19531250000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree018.table
  base := (900219514284512852791250714306446498133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-187836315977970895919269655249645204062500000000)
      constant := (1008824016699469270134921894906043824653758684037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree018.table
  base := (7196609783361790616295095356584522575919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-33761293584499422641897678575920000000000000)
      constant := (181346516651314939928761625274565923915756471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205824756879919139839/100000000000000000000)
  centralHi := (40200147828109207/19531250000000000)
  directionLo := (211791927553241965221/100000000000000000000)
  directionHi := (105895963776620982611/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree019.table
  base := (2849916304312071366243072133292879350539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-792929088423210304776474969562317579375000000000)
      constant := (4349194816980500397168084412936928477452215464571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree019.table
  base := (1423819689920388812863221933027303226011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-8907460535608187367753643011160000000000000)
      constant := (48864752942850470874497756149673694761864899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211791927553241965221/100000000000000000000)
  centralHi := (105895963776620982611/50000000000000000000)
  directionLo := (13599720040885372511/6250000000000000000)
  directionHi := (217595520654165960177/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree020.table
  base := (4365242826594244832817410871098776820341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1669025825869074051751742636252108685000000000000)
      constant := (9391039809926137061788167706702883300801890265749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree020.table
  base := (4361222582629851763731706238147167397057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-37498390700366076300131465513360000000000000)
      constant := (211028539664387866529209480986155393218333113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13599720040885372511/6250000000000000000)
  centralHi := (217595520654165960177/100000000000000000000)
  directionLo := (223248293701872303493/100000000000000000000)
  directionHi := (111624146850936151747/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree021.table
  base := (3174191800557177280621741166595544786693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-1752193474891727493950535333379582211250000000000)
      constant := (10145566874998679687724523253454249408395753079877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree021.table
  base := (39633129103100344960371272072467043999/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-4920867407287425391156044872760000000000000)
      constant := (28498533953109129248970637536255599265931910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223248293701872303493/100000000000000000000)
  centralHi := (111624146850936151747/50000000000000000000)
  directionLo := (22876142741475737839/10000000000000000000)
  directionHi := (228761427414757378391/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree022.table
  base := (526707732801083598178681663566689207479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-458840280978595234037332007626763934375000000000)
      constant := (2739872143372932173025924361624901597404451218231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree022.table
  base := (262964685209227148350689845681858996799/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-5154435977029091244795656556350000000000000)
      constant := (30785308051326160239568326846440341922008391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22876142741475737839/10000000000000000000)
  centralHi := (228761427414757378391/100000000000000000000)
  directionLo := (117072392886706194303/50000000000000000000)
  directionHi := (234144785773412388607/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree023.table
  base := (57328661075813100920766854060848075433/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-479632193234258594587030181908632315937500000000)
      constant := (2957682636008496653945647910104577079197125293685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree023.table
  base := (45753645589697794257348605317044871093/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-43104036374166056787482145919520000000000000)
      constant := (265864536646606755426227757559909476072505925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117072392886706194303/50000000000000000000)
  centralHi := (234144785773412388607/100000000000000000000)
  directionLo := (239407123404707931701/100000000000000000000)
  directionHi := (119703561702353965851/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree024.table
  base := (34942633686385372186179937889305289713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-250212052744960977568364178095250348750000000000)
      constant := (1594694657601319165195045533604270659659004736657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree024.table
  base := (277147739468654648630099581981888217349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-44972584932099383616599039388240000000000000)
      constant := (286695517494439870537359035332187124002533341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239407123404707931701/100000000000000000000)
  centralHi := (119703561702353965851/50000000000000000000)
  directionLo := (244556252770107933243/100000000000000000000)
  directionHi := (61139063192526983311/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree025.table
  base := (-505885402523132761535211379413632771201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-2084864070982341262745706121889476316250000000000)
      constant := (13738515547860035919837342416924958877132761523711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree025.table
  base := (-253989339082456853220585877639330043031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-23420566745016355222857966428480000000000000)
      constant := (154371388862614431125985781331711121909125921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244556252770107933243/100000000000000000000)
  centralHi := (61139063192526983311/25000000000000000000)
  directionLo := (124799590144556159929/50000000000000000000)
  directionHi := (249599180289112319859/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree026.table
  base := (-121944103620480222079548655145305344249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-1084015860002497352472249409508474921250000000000)
      constant := (7386193985428317837748093655618466818636879856195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree026.table
  base := (-1221269210762855437459911721851867741443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-48709682047966037274832826325680000000000000)
      constant := (331978982685802422572703745277638103514286613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124799590144556159929/50000000000000000000)
  centralHi := (249599180289112319859/100000000000000000000)
  directionLo := (127271109087094730807/50000000000000000000)
  directionHi := (50908443634837892323/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree027.table
  base := (-233660601553157033909391804976638710151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-281399921128456018392911439518052921093750000000)
      constant := (1982269271477727896882718305776095731464060889661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree027.table
  base := (-116929956810482859365984472324827404499/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-6322278825737420512993714974300000000000000)
      constant := (44547652964413201740937968627899119641524618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127271109087094730807/50000000000000000000)
  centralHi := (50908443634837892323/20000000000000000000)
  directionLo := (64847769268243018961/25000000000000000000)
  directionHi := (51878215414594415169/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree028.table
  base := (-1231128595363191868565012152946246528677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-1167183509025150794671042106635948447500000000000)
      constant := (8497479343190382314045137977829563863718130533947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree028.table
  base := (-153977883806263227883514857688804137761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-6555847395479086366633326657890000000000000)
      constant := (47741286901060928315790984486144298354058702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64847769268243018961/25000000000000000000)
  centralHi := (51878215414594415169/20000000000000000000)
  directionLo := (132075471698113207547/50000000000000000000)
  directionHi := (52830188679245283019/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree029.table
  base := (-3004094752929246255237124044204890922571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-2417534667072955031540876910399370421250000000000)
      constant := (18182084100542311376836438678830731620742844673781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree029.table
  base := (-601060649714133044677539191614170696409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-54315327721766017762183506731840000000000000)
      constant := (408610091645840781328460636875378972568935595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132075471698113207547/50000000000000000000)
  centralHi := (52830188679245283019/20000000000000000000)
  directionLo := (268826544316509569223/100000000000000000000)
  directionHi := (33603318039563696153/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree030.table
  base := (-874902369784366466093322749757178233669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-625175579023902118434917401881710986875000000000)
      constant := (4854732157633406570520415662805555636523244764859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree030.table
  base := (-350065982707708338591507969739961388329/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-28091938139849672295650200100280000000000000)
      constant := (218203551999167702514854708891402242300919195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268826544316509569223/100000000000000000000)
  centralHi := (33603318039563696153/12500000000000000000)
  directionLo := (273422202758291293843/100000000000000000000)
  directionHi := (68355550689572823461/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree031.table
  base := (-988209655783789795646661175062723590517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-645967491279565478984615576163579368437500000000)
      constant := (5176246844864876100814110466753755037761151859187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree031.table
  base := (-1976875297998868389603210946480304400673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-29026212418816335710208646834640000000000000)
      constant := (232654999369337967693449167024696824938509543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273422202758291293843/100000000000000000000)
  centralHi := (68355550689572823461/25000000000000000000)
  directionLo := (277941884201061044501/100000000000000000000)
  directionHi := (138970942100530522251/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree032.table
  base := (-2183585046364087823868261888146664229461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-1333518807070457679068627500890895500000000000000)
      constant := (11019918328650483549225575091730360794409028594571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree032.table
  base := (-4367961170591808234897062771079755302071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-59920973395565998249534187138000000000000000)
      constant := (495309265673599327825963714979396967356482561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277941884201061044501/100000000000000000000)
  centralHi := (138970942100530522251/50000000000000000000)
  directionLo := (70597309184413988407/25000000000000000000)
  directionHi := (282389236737655953629/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree033.table
  base := (-4745447392071402437495480053650746809467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-2750205263163568800336047698909264526250000000000)
      constant := (23423120856881434800373406059811879066297489117637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree033.table
  base := (-4746132991527501417233517194712480829209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-61789521953499325078651080606720000000000000)
      constant := (526396923196268598254037100322772641350751919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70597309184413988407/25000000000000000000)
  centralHi := (282389236737655953629/100000000000000000000)
  directionLo := (2294141004312553001/800000000000000000)
  directionHi := (143383812769534562563/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree034.table
  base := (-5090057493820161626597633328734549578867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-2833372912186222242534840396036738052500000000000)
      constant := (24854541464620375957226540663464498845052977781037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree034.table
  base := (-5090651182289193116770447825183733346337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-63658070511432651907767974075440000000000000)
      constant := (558566271494816132266450442663858893030139367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2294141004312553001/800000000000000000)
  centralHi := (143383812769534562563/50000000000000000000)
  directionLo := (291080162651726650737/100000000000000000000)
  directionHi := (145540081325863325369/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree035.table
  base := (-5403004443491049606936166742032089603287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-2916540561208875684733633093164211578750000000000)
      constant := (26333847855609552283221148768285817368431027559657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree035.table
  base := (-2701759068824822745398321618033861424977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-32763309534682989368442433772080000000000000)
      constant := (295905842921162620481689767449742883257239607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291080162651726650737/100000000000000000000)
  centralHi := (145540081325863325369/50000000000000000000)
  directionLo := (14766486643866535731/5000000000000000000)
  directionHi := (295329732877330714621/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree036.table
  base := (-5685971031586240258275041020338420214189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-2999708210231529126932425790291685105000000000000)
      constant := (27860829580928667859564802005166776659071253110579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree036.table
  base := (-5686415179504466965520242380549527457263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-67395167627299305566001761012880000000000000)
      constant := (626128443405591160275605714710156377372548233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14766486643866535731/5000000000000000000)
  centralHi := (295329732877330714621/100000000000000000000)
  directionLo := (29951901634693478383/10000000000000000000)
  directionHi := (299519016346934783831/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree037.table
  base := (-2970185241052814094907426408325182153033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-1541437929627091284565609243709579315625000000000)
      constant := (14717654951753226665188509529094241863582429469863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree037.table
  base := (-2970377114615241574116873164149470977667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-34631858092616316197559327240800000000000000)
      constant := (330756289048733193536122173295584136023733397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29951901634693478383/10000000000000000000)
  centralHi := (299519016346934783831/100000000000000000000)
  directionLo := (303650508291152475223/100000000000000000000)
  directionHi := (37956313536394059403/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree038.table
  base := (-308369489227725930558947951305385561883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-791510877069209002832502796136658039375000000000)
      constant := (7764285094760481715838316257895032482984983211065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree038.table
  base := (-6167721124051734380956952167492937990577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-71132264743165959224235547950320000000000000)
      constant := (697960758901188592032561820521832337184469207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303650508291152475223/100000000000000000000)
  centralHi := (37956313536394059403/12500000000000000000)
  directionLo := (307726536420756424077/100000000000000000000)
  directionHi := (153863268210378212039/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree039.table
  base := (-6368026028940344430190613174795890292663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-3249211157299489453528803881674105683750000000000)
      constant := (32726196311968271892839379737052023316832317270793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree039.table
  base := (-398019496072394317522606504288636900923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-9125101662637410756669055177380000000000000)
      constant := (91933773480895852099265865778406437890614586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307726536420756424077/100000000000000000000)
  centralHi := (153863268210378212039/50000000000000000000)
  directionLo := (9742164883171171027/3125000000000000000)
  directionHi := (62349855252295494573/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree040.table
  base := (-6543116880239056046718252441367732319119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-3332378806322142895727596578801579210000000000000)
      constant := (34442372944331642864538470753813239147582192929809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree040.table
  base := (-6543363438216022318225269913328861172217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-74869361859032612882469334887760000000000000)
      constant := (774038514449409786820317318227859228967242447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9742164883171171027/3125000000000000000)
  centralHi := (62349855252295494573/20000000000000000000)
  directionLo := (12628830589193593177/4000000000000000000)
  directionHi := (157860382364919914713/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree041.table
  base := (-1338673228560660209912545061057777046313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-3415546455344796337926389275929052736250000000000)
      constant := (36205582258719341695198021848255376502943646929715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree041.table
  base := (-1673394661206461570834785790554160164279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-19184477604241484927896557089120000000000000)
      constant := (203415940982869092808204422848213364098540289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12628830589193593177/4000000000000000000)
  centralHi := (157860382364919914713/50000000000000000000)
  directionLo := (319642912190517287967/100000000000000000000)
  directionHi := (9988841005953665249/3125000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree042.table
  base := (-3409682604966351268769510742282121047607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-1749357052183724890062590986528263131250000000000)
      constant := (19007875147893759748093816950352244678340748907177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree042.table
  base := (-3409774130094150480533744564955103675093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-39303229487449633270351560912600000000000000)
      constant := (427172138504038154696370052676721113776663763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319642912190517287967/100000000000000000000)
  centralHi := (9988841005953665249/3125000000000000000)
  directionLo := (40439689149722279923/12500000000000000000)
  directionHi := (64703502639555647877/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree043.table
  base := (-3460805532085684408867505693930982277077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-1790940876695051611161987335091999894375000000000)
      constant := (19936407451576584081331121379877158121508350216347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree043.table
  base := (-6921768662535474657711489335313969697009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-80475007532832593369820015293920000000000000)
      constant := (896078659352755665247684541223023059121101719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40439689149722279923/12500000000000000000)
  centralHi := (64703502639555647877/20000000000000000000)
  directionLo := (65469251218481027971/20000000000000000000)
  directionHi := (20459141005775321241/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree044.table
  base := (-875065173195659703969725248872096282991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-458131175301594583065345920913934164375000000000)
      constant := (5222090480745396527718886198530454300380971148401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree044.table
  base := (-7000657003534682409159667365346487006553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-82343556090765920198936908762640000000000000)
      constant := (938865739186480950861840136245941717998592623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65469251218481027971/20000000000000000000)
  centralHi := (20459141005775321241/6250000000000000000)
  directionLo := (16556536579985135963/5000000000000000000)
  directionHi := (331130731599702719261/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree045.table
  base := (-1411289446911118324671660004247712336073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-3748217051435410106721560064438946841250000000000)
      constant := (43727433220778151758660796947565903901228884266515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree045.table
  base := (-7056563882293552721687884481460994947751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-84212104648699247028053802231360000000000000)
      constant := (982704531676358837761077996138776065191767441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16556536579985135963/5000000000000000000)
  centralHi := (331130731599702719261/100000000000000000000)
  directionLo := (334872440552808455239/100000000000000000000)
  directionHi := (8371811013820211381/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree046.table
  base := (-1772420925113974564112061037684156437593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-957846175114515887230088190391605091875000000000)
      constant := (11431226530969835041099439214572024987401371530023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree046.table
  base := (-443111499116068176174747059111227605537/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-10760081650829071732146336962510000000000000)
      constant := (128449276130809988284073393532153123312093134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334872440552808455239/100000000000000000000)
  centralHi := (8371811013820211381/2500000000000000000)
  directionLo := (338572800847667184051/100000000000000000000)
  directionHi := (84643200211916796013/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree047.table
  base := (-7100478843110004326903375900827980954683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-3914552349480716991119145458693893893750000000000)
      constant := (47769111533029429541255021778253231230413424363013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree047.table
  base := (-3550282511864770918194999054225123283891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-43974600882282950343143794584400000000000000)
      constant := (536767037740423365904803643246361628695550181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338572800847667184051/100000000000000000000)
  centralHi := (84643200211916796013/25000000000000000000)
  directionLo := (342233153721076498079/100000000000000000000)
  directionHi := (2138957210756728113/625000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree048.table
  base := (-1772260300577741717300469728114632934521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-999429999625842608329484538955341855000000000000)
      constant := (12465005842087116002688223669919110864286233280231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree048.table
  base := (-1772278807733777928711016429695551223511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-22454437580624806878851120659380000000000000)
      constant := (280130886511819079971406929083865196613157601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342233153721076498079/100000000000000000000)
  centralHi := (2138957210756728113/625000000000000000)
  directionLo := (345854769430629434459/100000000000000000000)
  directionHi := (17292738471531471723/5000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree049.table
  base := (-7055546105180824515222106090049573363999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4080887647526023875516730852948840946250000000000)
      constant := (51997619703516153580950409638169143603438086563489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree049.table
  base := (-7055609669750128081047162792283361112163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-91686298880432554344521376106240000000000000)
      constant := (1168562128995834466196717217078876038635934133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345854769430629434459/100000000000000000000)
  centralHi := (17292738471531471723/5000000000000000000)
  directionLo := (174719426202378623901/50000000000000000000)
  directionHi := (349438852404757247803/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree050.table
  base := (-7000140964546219031324967922752379165317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4164055296548677317715523550076314472500000000000)
      constant := (54181882103159726386960413798383333382582459456987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree050.table
  base := (-1750048880769123549579750121995453779779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-23388711859591470293409567393740000000000000)
      constant := (304412352722437431119052680019314770332600789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174719426202378623901/50000000000000000000)
  centralHi := (349438852404757247803/100000000000000000000)
  directionLo := (88246636480517485509/25000000000000000000)
  directionHi := (352986545922069942037/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree051.table
  base := (-6922949730215160564075688485587423139619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4247222945571330759914316247203787998750000000000)
      constant := (56412795066179531031746645132326454651902784705309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree051.table
  base := (-6922996541299123444103909534428491724833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-95423395996299208002755163043680000000000000)
      constant := (1267785044114190873046867100314110366744944103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88246636480517485509/25000000000000000000)
  centralHi := (352986545922069942037/100000000000000000000)
  directionLo := (44562367046441472361/12500000000000000000)
  directionHi := (356498936371531778889/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree052.table
  base := (-3412038314488826194087924179626271883987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-2165195297296992101056554472165630762500000000000)
      constant := (29345172779013234797733298672542056233776018497357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree052.table
  base := (-6824116778391063465294200672046145667643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-97291944554232534831872056512400000000000000)
      constant := (1318968736381547621068565856919582376819590813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44562367046441472361/12500000000000000000)
  centralHi := (356498936371531778889/100000000000000000000)
  directionLo := (89994264284617514071/25000000000000000000)
  directionHi := (71995411427694011257/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree053.table
  base := (-6703609307293711854640169827557068977759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (7835696)
      previous := (3917848)
      next := (3917848)
      square := (28028857933877912317760516887090000000000000)
      linear := (-1571220449845723618480563062107061250000000000)
      constant := (21721083167561067870869076410240725989853691561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree053.table
  base := (-837955466396857710303874847693266746681/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78695609751235125889357036250000000000)
      linear := (-4412624292994208867078539960000000000000)
      constant := (61018166692472651870639327612306733253319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89994264284617514071/25000000000000000000)
  centralHi := (71995411427694011257/20000000000000000000)
  directionLo := (363421892155815521871/100000000000000000000)
  directionHi := (22713868259738470117/6250000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree054.table
  base := (-6561621472308168749274808115062990402541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4496725892639291086510694338586208577500000000000)
      constant := (63385317027359373131155662780734312243227568238451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree054.table
  base := (-1640412744332202747990610537730509977869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-25257260417524797122526460862460000000000000)
      constant := (356119838507396495901516904853914997472165979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363421892155815521871/100000000000000000000)
  centralHi := (22713868259738470117/6250000000000000000)
  directionLo := (73366875831032379973/20000000000000000000)
  directionHi := (183417189577580949933/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree055.table
  base := (-3199087555733634818882736020756999927287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-2289946770830972264354743517856841051875000000000)
      constant := (32901360517474559015323609549294256035861856873657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree055.table
  base := (-6398200392366650638808773331156609378403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-102897590228032515319222736918560000000000000)
      constant := (1478805898922251179836766843529581084256065973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73366875831032379973/20000000000000000000)
  centralHi := (183417189577580949933/50000000000000000000)
  directionLo := (185107706324043240269/50000000000000000000)
  directionHi := (370215412648086480539/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree056.table
  base := (-6213322358126680922312381594667468205521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4663061190684597970908279732841155630000000000000)
      constant := (68266728120677454852232276602572275733793796761231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree056.table
  base := (-6213344012938072196933218781955219552407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-104766138785965842148339630387280000000000000)
      constant := (1534179730420292037897841939320207788277288737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185107706324043240269/50000000000000000000)
  centralHi := (370215412648086480539/100000000000000000000)
  directionLo := (186782923332295572483/50000000000000000000)
  directionHi := (373565846664591144967/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree057.table
  base := (-3003553529865895324317281302781126894411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-2373114419853625706553536214984314578125000000000)
      constant := (35388666400502634705753252642339041633557209634021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree057.table
  base := (-3003562801496367839126744447815755408841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-53317343671949584488728261928000000000000000)
      constant := (795300362795386981407908029147765543056565631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186782923332295572483/50000000000000000000)
  centralHi := (373565846664591144967/100000000000000000000)
  directionLo := (376886497272418470109/100000000000000000000)
  directionHi := (37688649727241847011/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree058.table
  base := (-5779566096082794492205749330494002241011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4829396488729904855305865127096102682500000000000)
      constant := (73334530463763594815195150105891806195455559496621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree058.table
  base := (-5779581970285915298658392437337239261769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-108503235901832495806573417324720000000000000)
      constant := (1648068781040712389318257536634239694913690879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376886497272418470109/100000000000000000000)
  centralHi := (37688649727241847011/10000000000000000000)
  directionLo := (380178144898299705969/100000000000000000000)
  directionHi := (38017814489829970597/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree059.table
  base := (-5530730487587327368684367203586917106903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-4912564137752558297504657824223576208750000000000)
      constant := (75938317229556103669047410282877268460970664947433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree059.table
  base := (-276537203654887372764713498402221700439/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-27592946114941455658922577698360000000000000)
      constant := (426645952452074603566395575925140796217334245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380178144898299705969/100000000000000000000)
  centralHi := (38017814489829970597/10000000000000000000)
  directionLo := (7668830729396820859/2000000000000000000)
  directionHi := (383441536469841042951/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree060.table
  base := (-328789145438539556312209363144163825621/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-624466473346901467462931315168881216875000000000)
      constant := (9823586229404269706460723117009650180786730264662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree060.table
  base := (-1315159487663648027143739416432319381277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-28060083254424787366201801065540000000000000)
      constant := (441536434687336298132246973417641614857992907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7668830729396820859/2000000000000000000)
  centralHi := (383441536469841042951/100000000000000000000)
  directionLo := (386677387394701825781/100000000000000000000)
  directionHi := (193338693697350912891/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree061.table
  base := (-248463778146001915807654636636607533513/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-1269724858949466295475560804619630815312500000000)
      constant := (20321411383980848402201516689588235834156647350715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree061.table
  base := (-4969285505382827714822903853832212483657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-114108881575632476293924097730880000000000000)
      constant := (1826754506339937027024664549203705315133407487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386677387394701825781/100000000000000000000)
  centralHi := (193338693697350912891/50000000000000000000)
  directionLo := (194943191695960609579/50000000000000000000)
  directionHi := (389886383391921219159/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree062.table
  base := (-931339331670291860456782874567410747521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5162067084820518624101035915605996787500000000000)
      constant := (84029182022643723465002095002902385596340828616155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree062.table
  base := (-4656705160627119641431254761175441491581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-115977430133565803123040991199600000000000000)
      constant := (1888410060828898752735604922543218184850148971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194943191695960609579/50000000000000000000)
  centralHi := (389886383391921219159/100000000000000000000)
  directionLo := (393069182188672804773/100000000000000000000)
  directionHi := (196534591094336402387/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree063.table
  base := (-172916205791289687500745415193067181709/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5245234733843172066299828612733470313750000000000)
      constant := (86819297353037277230335802914185259007077870332475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree063.table
  base := (-864582482737657248773415641544866064523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-117845978691499129952157884668320000000000000)
      constant := (1951112358684312370901302020182822356123774465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393069182188672804773/100000000000000000000)
  centralHi := (196534591094336402387/50000000000000000000)
  directionLo := (396226415094339622641/100000000000000000000)
  directionHi := (198113207547169811321/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree064.table
  base := (-991978521975183858809896695571143308951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-1332100595716456377124655327465235960000000000000)
      constant := (22413997473278936653180665240534515254636818813961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree064.table
  base := (-99198007521605617744393169940189115527/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-14964315906179057097659347267130000000000000)
      constant := (251857670410902136040207505832190043872423285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396226415094339622641/100000000000000000000)
  centralHi := (198113207547169811321/50000000000000000000)
  directionLo := (399358688462579711773/100000000000000000000)
  directionHi := (199679344231289855887/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree065.table
  base := (-718346895866644258311697387729375962753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5411570031888478950697414006988417366250000000000)
      constant := (92539258268271965475494165411942848498303946433915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree065.table
  base := (-3591739788513618492085682546836135714271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-121583075807365783610391671605760000000000000)
      constant := (2079657043833111363177402895984337294778612761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399358688462579711773/100000000000000000000)
  centralHi := (199679344231289855887/50000000000000000000)
  directionLo := (80493317010194497173/20000000000000000000)
  directionHi := (201233292525486242933/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree066.table
  base := (-127775022643264225942308907604043588123/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5494737680911132392896206704115890892500000000000)
      constant := (95469101322080600685760403819340389740421528771325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree066.table
  base := (-3194380101924720841157368557930860579227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-123451624365299110439508565074480000000000000)
      constant := (2145499374408160492088268139668292212632951357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80493317010194497173/20000000000000000000)
  centralHi := (201233292525486242933/50000000000000000000)
  directionLo := (405550665286880698853/100000000000000000000)
  directionHi := (202775332643440349427/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree067.table
  base := (-2775845127592101872481326037486892100373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5577905329933785835094999401243364418750000000000)
      constant := (98445518081648084096953927693006025643049528410603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree067.table
  base := (-2775849001891954159127119380436141085943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-125320172923232437268625458543200000000000000)
      constant := (2212388333212292942526654813959714879689586113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405550665286880698853/100000000000000000000)
  centralHi := (202775332643440349427/50000000000000000000)
  directionLo := (81722293689463076233/20000000000000000000)
  directionHi := (204305734223657690583/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree068.table
  base := (-1168074854394313250663918571699415109781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-2830536489478219638646896049185418972500000000000)
      constant := (50734253864234787581476995258729852858834409238091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree068.table
  base := (-584038254330993505280925684256558189097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-31797180370291441024435588002980000000000000)
      constant := (570080975476451075245506552581403328046826527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81722293689463076233/20000000000000000000)
  centralHi := (204305734223657690583/50000000000000000000)
  directionLo := (411649513759838279679/100000000000000000000)
  directionHi := (40200147828109207/9765625000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree069.table
  base := (-1875294816076570239340079315275943258133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5744240627979092719492584795498311471250000000000)
      constant := (104538069573916829495442634677955813823590204425963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree069.table
  base := (-468824410220013871717400285995990849279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-32264317509774772731714811370160000000000000)
      constant := (587326516264953665952905468844437261704375289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411649513759838279679/100000000000000000000)
  centralHi := (40200147828109207/9765625000000000)
  directionLo := (414665301430866237117/100000000000000000000)
  directionHi := (207332650715433118559/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree070.table
  base := (-87080317637911544111507563802518395673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-728426034625218270211422186578223124687500000000)
      constant := (13456775379827552242312177887110251969208225867806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree070.table
  base := (-696643746758375977453994000365870285967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-65462909298516208877988069474680000000000000)
      constant := (1209667404847028536259467017518572270366718697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414665301430866237117/100000000000000000000)
  centralHi := (207332650715433118559/50000000000000000000)
  directionLo := (16706372544285777603/4000000000000000000)
  directionHi := (104414828401786110019/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree071.table
  base := (-890124404950099157764187680577484474133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5910575926024399603890170189753258523750000000000)
      constant := (110816907635127037310425251723411572110392305801963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree071.table
  base := (-445063231444916799096425318904952138687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-66397183577482872292546516209040000000000000)
      constant := (1245205062444053234344067469446155989442428217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16706372544285777603/4000000000000000000)
  centralHi := (104414828401786110019/25000000000000000000)
  directionLo := (210316007637810881799/50000000000000000000)
  directionHi := (420632015275621763599/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree072.table
  base := (-365816063749965594789309838480417766773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-5993743575047053046088962886880732050000000000000)
      constant := (114026182953311240335464892946827338290080847441003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree072.table
  base := (-365817819769061070473662606993445013507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-134662915712899071414209925886800000000000000)
      constant := (2562532001454370594642842315736315412957058837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210316007637810881799/50000000000000000000)
  centralHi := (420632015275621763599/100000000000000000000)
  directionLo := (423583855106483930443/100000000000000000000)
  directionHi := (105895963776620982611/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree073.table
  base := (44909295538247747711295553648062376267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-1519227806017426622071938896002051394062500000000)
      constant := (29320507162025944853035365955967077341586779872563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree073.table
  base := (44908921009628166692326709100195965523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-34132866067708099560831704838880000000000000)
      constant := (658925107915755859653564522307742450467154107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423583855106483930443/100000000000000000000)
  centralHi := (105895963776620982611/25000000000000000000)
  directionLo := (213257633121836136281/50000000000000000000)
  directionHi := (426515266243672272563/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree074.table
  base := (373116505586875088557198961341950165713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3080039436546179965243274140567839551250000000000)
      constant := (60292222214584209108210983598162812454878158100657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree074.table
  base := (746231733317364334114347592817918437921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-138400012828765725072443712824240000000000000)
      constant := (2709915409010624595710486675706625532892120089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213257633121836136281/50000000000000000000)
  centralHi := (426515266243672272563/100000000000000000000)
  directionLo := (10735666676170794407/2500000000000000000)
  directionHi := (429426667046831776281/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree075.table
  base := (666984734970848693448796688155361775869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3121623261057506686342670489131576314375000000000)
      constant := (61966715026108812930837865869789688621397965920941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree075.table
  base := (1333968380152779241243606241542924523461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-140268561386699051901560606292960000000000000)
      constant := (2785176928025481632366425224904494074986401949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10735666676170794407/2500000000000000000)
  centralHi := (429426667046831776281/100000000000000000000)
  directionLo := (216159230894143396537/50000000000000000000)
  directionHi := (17292738471531471723/4000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree076.table
  base := (1942844914882226114483851128321524329923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-6326414171137666814884133675390626155000000000000)
      constant := (127328985311706801924922474535967653433526237789347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree076.table
  base := (388568797128418653778566740338952837581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-142137109944632378730677499761680000000000000)
      constant := (2861484984103916965071060461156380592603825145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216159230894143396537/50000000000000000000)
  centralHi := (17292738471531471723/4000000000000000000)
  directionLo := (13599720040885372511/3125000000000000000)
  directionHi := (435191041308331920353/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree077.table
  base := (1286428981535258491127135731803659390389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3204790910080160128541463186259049840625000000000)
      constant := (65385555017344037584689938975188339188977256101221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree077.table
  base := (2572857170859959234274764110713659913493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-144005658502565705559794393230400000000000000)
      constant := (2938839573372529293587942954654354670697001837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13599720040885372511/3125000000000000000)
  centralHi := (435191041308331920353/100000000000000000000)
  directionLo := (43804478363184526309/10000000000000000000)
  directionHi := (438044783631845263091/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree078.table
  base := (3224007450884981742628761289182796734047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-6492749469182973699281719069645573207500000000000)
      constant := (134259804075639524379437170054025279701682036721983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree078.table
  base := (201500423475476544632972422583481460577/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-18234275882562379048613910837390000000000000)
      constant := (377155086571540040295016275058713998845521586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43804478363184526309/10000000000000000000)
  centralHi := (438044783631845263091/100000000000000000000)
  directionLo := (440880054548978211723/100000000000000000000)
  directionHi := (110220013637244552931/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree079.table
  base := (974073099805471247803730271733852627443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-1643979279551406785370127941693261683437500000000)
      constant := (34448766828028734181857457251923613986841282081627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree079.table
  base := (1948145911854948326649996008663000500591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-73871377809216179609014090083920000000000000)
      constant := (1548344169480606967047851202895134368406160119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440880054548978211723/100000000000000000000)
  centralHi := (110220013637244552931/25000000000000000000)
  directionLo := (110924302040611764277/25000000000000000000)
  directionHi := (443697208162447057109/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree080.table
  base := (2294855992114725369927515375063595085769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3329542383614140291839652231950260130000000000000)
      constant := (70688449820541915048268190141715265568929182312041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree080.table
  base := (4589711493819969974145074987751863172373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-149611304176365686047145073636560000000000000)
      constant := (3177182510232046953331549178821394983651195757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110924302040611764277/25000000000000000000)
  centralHi := (443697208162447057109/100000000000000000000)
  directionLo := (223248293701872303493/50000000000000000000)
  directionHi := (446496587403744606987/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree081.table
  base := (2652132756342627877896906519581134647811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3371126208125467012939048580513996893125000000000)
      constant := (72502650487926081236963360423798157825849344878579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree081.table
  base := (5304265094857538093160420137656150471197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-151479852734299012876261967105280000000000000)
      constant := (3258723204443574798874612312977396126673592373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223248293701872303493/50000000000000000000)
  centralHi := (446496587403744606987/100000000000000000000)
  directionLo := (89855704904080435149/20000000000000000000)
  directionHi := (224639262260201087873/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree082.table
  base := (6039952401279890979191638731326177715487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-6825420065273587468076889858155467312500000000000)
      constant := (148680271243471557233685336247649670656953241606143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree082.table
  base := (6039952045344562180243398575655480031601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-153348401292232339705378860574000000000000000)
      constant := (3341310419962425659651133523702376243408767209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89855704904080435149/20000000000000000000)
  centralHi := (224639262260201087873/50000000000000000000)
  directionLo := (226021670768130932181/50000000000000000000)
  directionHi := (452043341536261864363/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree083.table
  base := (3398386079593462824801150745210979268371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3454293857148120455137841277641470419375000000000)
      constant := (76200905191279755878608471253598621260527227372419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree083.table
  base := (169919296400498453910914899601136934617/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-19402118731270708316811969255340000000000000)
      constant := (428118019426783136787915179272237968246695765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226021670768130932181/50000000000000000000)
  centralHi := (452043341536261864363/100000000000000000000)
  directionLo := (227395675343282068959/50000000000000000000)
  directionHi := (454791350686564137919/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree084.table
  base := (7574724373397657336070022644509418344777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-6991755363318894352474475252410414365000000000000)
      constant := (156169918341465368765953152163929092017010037438953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree084.table
  base := (75747241152125833918186336875049932277/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-39271374602024748340903161877860000000000000)
      constant := (877406102410677257930931722926250381494152325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227395675343282068959/50000000000000000000)
  centralHi := (454791350686564137919/100000000000000000000)
  directionLo := (22876142741475737839/5000000000000000000)
  directionHi := (457522854829514756781/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree085.table
  base := (523363043523870936666975365585062810947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-884365376542693474334158493692235986406250000000)
      constant := (19998074384590898144655954726973681671426784914666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree085.table
  base := (261681514891722676377078571068028768849/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-19869255870754040024091192622520000000000000)
      constant := (449418897709344417910458074569220371246787364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22876142741475737839/5000000000000000000)
  centralHi := (457522854829514756781/100000000000000000000)
  directionLo := (460238147835866715699/100000000000000000000)
  directionHi := (4602381478358667157/1000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree086.table
  base := (4597012417852994948649503085890677821381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3579045330682100618436030323332680708750000000000)
      constant := (81922920275886671625310227581321937688596166134309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree086.table
  base := (4597012324264950288943695077261002579061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-80411297761982823510923217224440000000000000)
      constant := (1841062235345849724932648469922586156244582349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460238147835866715699/100000000000000000000)
  centralHi := (4602381478358667157/1000000000000000000)
  directionLo := (462937514957935741373/100000000000000000000)
  directionHi := (231468757478967870687/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree087.table
  base := (10035372545296793316472300714816678106101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-7241258310386854679070853343792834943750000000000)
      constant := (167753654735830075813729217053239917120009291342389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree087.table
  base := (10035372385957440858285460854540124154949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-162691144081898973850963327917600000000000000)
      constant := (3769944276004663687724620718047763208751251741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462937514957935741373/100000000000000000000)
  centralHi := (231468757478967870687/50000000000000000000)
  directionLo := (116405308294840244939/25000000000000000000)
  directionHi := (465621233179360979757/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree088.table
  base := (10897851618091738316532369658905531622201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-7324425959409508121269646040920308470000000000000)
      constant := (171708037603002239033193013996753452616445798115289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree088.table
  base := (2724462870616706540181393409668236055559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-41139923159958075170020055346580000000000000)
      constant := (964702649258502080417504171781838075080065231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116405308294840244939/25000000000000000000)
  centralHi := (465621233179360979757/100000000000000000000)
  directionLo := (117072392886706194303/25000000000000000000)
  directionHi := (468289571546824777213/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree089.table
  base := (2945365469963474161986547602192017746499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-1851898402108040390867109684511945499062500000000)
      constant := (43927247282874962924298895424698332653289299604011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree089.table
  base := (11781461764428636626946720083431125827369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-166428241197765627509197114855040000000000000)
      constant := (3948723433292008311319629674422358032449079521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117072392886706194303/25000000000000000000)
  centralHi := (468289571546824777213/100000000000000000000)
  directionLo := (58867848935607004887/12500000000000000000)
  directionHi := (470942791484856039097/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree090.table
  base := (12686203183967972272715633372383116430569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-7490761257454815005667231435175255522500000000000)
      constant := (179756509302987279803641149489625603891315713119241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree090.table
  base := (6343101542873027173180492741070006206047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-84148394877849477169157004161880000000000000)
      constant := (2019841392184138847581309113760865647432786023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58867848935607004887/12500000000000000000)
  centralHi := (470942791484856039097/100000000000000000000)
  directionLo := (236790573547379872069/50000000000000000000)
  directionHi := (473581147094759744139/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree091.table
  base := (1361207540706140801168574497490154564651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3786964453238734223933012066151364524375000000000)
      constant := (91925299051017807197540658711680458981404013866695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree091.table
  base := (3403018830872233188518955725889247161441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-42541334578408070291857725448120000000000000)
      constant := (1032922162479376422874549795523902895276487769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236790573547379872069/50000000000000000000)
  centralHi := (473581147094759744139/100000000000000000000)
  directionLo := (476204885438640095317/100000000000000000000)
  directionHi := (238102442719320047659/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree092.table
  base := (3639769611329944942046866765269407638553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-1914274138875030472516204207357550643750000000000)
      constant := (46997813878915469160789341621248239851141384879417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree092.table
  base := (909942398388767540993525557592863720517/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-21504235858945700999568474407650000000000000)
      constant := (528092628706142224007734909892476708381864506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476204885438640095317/100000000000000000000)
  centralHi := (238102442719320047659/50000000000000000000)
  directionLo := (478814246809415863403/100000000000000000000)
  directionHi := (119703561702353965851/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree093.table
  base := (310544244227727475719928743562026136431/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-3870132102261387666131804763278838050625000000000)
      constant := (96089240766470640282398303668411257478577784843975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree093.table
  base := (15527212150905324483861527147212736253677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-173902435429498934825664688729920000000000000)
      constant := (4318839923318693317901255461818440576136578693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478814246809415863403/100000000000000000000)
  centralHi := (119703561702353965851/25000000000000000000)
  directionLo := (481409464987663159227/100000000000000000000)
  directionHi := (120352366246915789807/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree094.table
  base := (16516476631753308454495422649288735461571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-7823431853545428774462402223685149627500000000000)
      constant := (196412276144680968048302751885709401502311498397219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree094.table
  base := (16516476580310740477587281807954368926449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-175770983987432261654781582198640000000000000)
      constant := (4413985330720459862573409366905743822314395241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481409464987663159227/100000000000000000000)
  centralHi := (120352366246915789807/25000000000000000000)
  directionLo := (483990767486062644013/100000000000000000000)
  directionHi := (241995383743031322007/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree095.table
  base := (17526871644566256505266965472562192306159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-7906599502568082216661194920812623153750000000000)
      constant := (200692639343145468533048746995234817917285788592751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree095.table
  base := (17526871600816310155286463037373663384837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-177639532545365588483898475667360000000000000)
      constant := (4510177251681346232363000721887182620448007133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483990767486062644013/100000000000000000000)
  centralHi := (241995383743031322007/50000000000000000000)
  directionLo := (486558375782174594401/100000000000000000000)
  directionHi := (243279187891087297201/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree096.table
  base := (3711679439555437225143869495808245678607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-7989767151590735658859987617940096680000000000000)
      constant := (205019571121825681757096128625566559552765248259115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree096.table
  base := (4639599290143396757605659840135131154451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-44877020275824728828253842284020000000000000)
      constant := (1151853921513927535272337172687419583412852859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486558375782174594401/100000000000000000000)
  centralHi := (243279187891087297201/50000000000000000000)
  directionLo := (489112505540215866487/100000000000000000000)
  directionHi := (61139063192526983311/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree097.table
  base := (19611053247589940701660430947115194596959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8072934800613389101058780315067570206250000000000)
      constant := (209393071475244482754110057885422374372189065993951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree097.table
  base := (1961105321595653957084108038552931923349/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-90688314830616121071066131302400000000000000)
      constant := (2352850316860503033089315317911155928863436705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489112505540215866487/100000000000000000000)
  centralHi := (61139063192526983311/12500000000000000000)
  directionLo := (98330673364493455711/20000000000000000000)
  directionHi := (122913341705616819639/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree098.table
  base := (5171209939288056986689285531131220649213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-2039025612409010635814393253048760933125000000000)
      constant := (53453285099698285670570769721886353296844638532157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree098.table
  base := (20684839730257865696823621324207275739889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-183245178219165568971249156073520000000000000)
      constant := (4805032094574123196088918232215218237553348201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98330673364493455711/20000000000000000000)
  centralHi := (122913341705616819639/25000000000000000000)
  directionLo := (9883623285817958377/2000000000000000000)
  directionHi := (494181164290897918851/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree099.table
  base := (1361234793465934499100479643610041178439/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1029908762332336998182045713665314657343750000000)
      constant := (27284972236074209982135679251833423978941617377842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree099.table
  base := (871190266903680764189726509767527466717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-185113726777098895800366049542240000000000000)
      constant := (4905410068528304031253322957622824616350201325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9883623285817958377/2000000000000000000)
  centralHi := (494181164290897918851/100000000000000000000)
  directionLo := (49669609739955407889/10000000000000000000)
  directionHi := (496696097399554078891/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree100.table
  base := (915832161456240673620890914586420655371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8322437747681349427655158406449990785000000000000)
      constant := (222792983941383030088608287155706531415618559135475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree100.table
  base := (4579160803394433457703412976511553287643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-186982275335032222629482943010960000000000000)
      constant := (5006834555510551559162258676951104765924945935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49669609739955407889/10000000000000000000)
  centralHi := (496696097399554078891/100000000000000000000)
  directionLo := (499198360578224639717/100000000000000000000)
  directionHi := (249599180289112319859/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree101.table
  base := (24032981758050942060362883905088698388651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8405605396704002869853951103577464311250000000000)
      constant := (227352758554415577270371823818956207384105129959339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree101.table
  base := (12016490870766750145294487745197317454941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-94425411946482774729299918239840000000000000)
      constant := (2554652777729723764322474798366419264730929269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499198360578224639717/100000000000000000000)
  centralHi := (249599180289112319859/50000000000000000000)
  directionLo := (100337628681572309897/20000000000000000000)
  directionHi := (250844071703930774743/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree102.table
  base := (6297822460479254207502112118464618256027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-2122193261431664078013185950176234459375000000000)
      constant := (57989775431345283406848057724898122010749120290203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree102.table
  base := (5038257965575936710269627521790888818753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-190719372450898876287716729948400000000000000)
      constant := (5212823068323316635923449100670913033459385885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100337628681572309897/20000000000000000000)
  centralHi := (250844071703930774743/50000000000000000000)
  directionLo := (504165630788203300481/100000000000000000000)
  directionHi := (252082815394101650241/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree103.table
  base := (26370728272461408969338392412128652215903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8571940694749309754251536497832411363750000000000)
      constant := (236612013452335920509610873434924089579512359353567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree103.table
  base := (1648170516283308039822378751551570172851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-24073490126104025389604202927140000000000000)
      constant := (664673386757335221660959035618356721231076918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504165630788203300481/100000000000000000000)
  centralHi := (252082815394101650241/50000000000000000000)
  directionLo := (253315501549010418813/50000000000000000000)
  directionHi := (506631003098020837627/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree104.table
  base := (27571297036606750111360148560984235781927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8655108343771963196450329194959884890000000000000)
      constant := (241311493733644488911586896509258920276443306055303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree104.table
  base := (13785648513235626113605715892788988183919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-97228234783382764972975258442920000000000000)
      constant := (2711498816314482094794735706547644267808628471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253315501549010418813/50000000000000000000)
  centralHi := (506631003098020837627/100000000000000000000)
  directionLo := (127271109087094730807/25000000000000000000)
  directionHi := (509084436348378923229/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree105.table
  base := (28792996123350330868864912840776015434139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8738275992794616638649121892087358416250000000000)
      constant := (246057542567930845619740463948094934846032348994971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree105.table
  base := (28792996114739099162510117829463457622691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-196325018124698856775067410354560000000000000)
      constant := (5529654684003389730387220723727762852462139019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127271109087094730807/25000000000000000000)
  centralHi := (509084436348378923229/100000000000000000000)
  directionLo := (511526102329281475401/100000000000000000000)
  directionHi := (255763051164640737701/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree106.table
  base := (1877239095214702378463703042741179950869/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55651250000000000000000000000000000000000000
      center := (979462)
      previous := (489731)
      next := (489731)
      square := (3503607241734739039720064610886250000000000)
      linear := (-392552671850181117873260706177235312500000000)
      constant := (11162787466804793778980902832047371024091527498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree106.table
  base := (30035825516119697536664274896205746786057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (176)
      previous := (88)
      next := (88)
      square := (629564878009881007114856290000000000000)
      linear := (-70556627512507007335060271920000000000000)
      constant := (2006891508777525269987850176976205746786057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511526102329281475401/100000000000000000000)
  centralHi := (255763051164640737701/50000000000000000000)
  directionLo := (51395616875004663679/10000000000000000000)
  directionHi := (513956168750046636791/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree107.table
  base := (31299785229073615725087748851970983899097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-8904611290839923523046707286342305468750000000000)
      constant := (255689345890989984171137756334055753336943610881433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree107.table
  base := (3129978522285935829936917098993169432117/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-100031057620282755216650598646000000000000000)
      constant := (2873054162532610168036558345557039064674083265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51395616875004663679/10000000000000000000)
  centralHi := (513956168750046636791/100000000000000000000)
  directionLo := (64546849921717022033/12500000000000000000)
  directionHi := (103274959874747235253/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree108.table
  base := (8146218808428447054160847421123002503041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-2246944734965644241311374995867444748750000000000)
      constant := (65143775094492367879772599733242135829957278406049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree108.table
  base := (32584875228435483806049245869719236205017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-201930663798498837262418090760720000000000000)
      constant := (5855904914712523311635344606974761334499892753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64546849921717022033/12500000000000000000)
  centralHi := (103274959874747235253/20000000000000000000)
  directionLo := (518782154145944151689/100000000000000000000)
  directionHi := (51878215414594415169/10000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree109.table
  base := (33891095531844293042632000463232391965127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9070946588885230407444292680597252521250000000000)
      constant := (265507423414286527162793088737571341524476800940103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree109.table
  base := (33891095527361355585184333151364084140813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-203799212356432164091534984229440000000000000)
      constant := (5966748017082565217896054747334981712351543717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518782154145944151689/100000000000000000000)
  centralHi := (51878215414594415169/10000000000000000000)
  directionLo := (32573649332389465663/6250000000000000000)
  directionHi := (521178389318231450609/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree110.table
  base := (35218446118828973483793563027661126952031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9154114237907883849643085377724726047500000000000)
      constant := (270486314999361355712011251418577420771316374372159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree110.table
  base := (17609223057510935174478497128905748297603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-102833880457182745460325938849080000000000000)
      constant := (3039318816081191114859883963615896246967966827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32573649332389465663/6250000000000000000)
  centralHi := (521178389318231450609/100000000000000000000)
  directionLo := (20942546302659030863/4000000000000000000)
  directionHi := (65445457195809471447/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree111.table
  base := (18283463495384104029992444983219683964979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-4618640943465268645920939037426099786875000000000)
      constant := (137755887566353136248572378155746756021655673885731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree111.table
  base := (3656692698753531778938951877499831130891/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-103768154736149408874884385583440000000000000)
      constant := (3095786879970535311425687379056045128233364095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20942546302659030863/4000000000000000000)
  centralHi := (65445457195809471447/12500000000000000000)
  directionLo := (105187621620878143001/20000000000000000000)
  directionHi := (262969054052195357503/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree112.table
  base := (37936538144382134352558730298077276596713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9320449535953190734040670771979673100000000000000)
      constant := (280583803813911099600127274137319747703696586859657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree112.table
  base := (18968269070818535808088446082336832802533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-104702429015116072289442832317800000000000000)
      constant := (3152778200204730031020704227068964163342315197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105187621620878143001/20000000000000000000)
  centralHi := (262969054052195357503/50000000000000000000)
  directionLo := (132075471698113207547/25000000000000000000)
  directionHi := (528301886792452830189/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree113.table
  base := (4915909947114047657386179908135502710411/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1175452148121980522029932933638393328281250000000)
      constant := (35712800130328859567552135887773599433973091202479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree113.table
  base := (39327279574581719854928125190079870451717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-211273406588165471408002558104320000000000000)
      constant := (6420585553559838685053804726543254356098873053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132075471698113207547/25000000000000000000)
  centralHi := (528301886792452830189/100000000000000000000)
  directionLo := (106131027248492326647/20000000000000000000)
  directionHi := (132663784060615408309/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree114.table
  base := (8147830257207875256343951770378533108377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9486784833998497618438256166234620152500000000000)
      constant := (290867566818575518766733712923732700080047296196765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree114.table
  base := (40739151284060711198061239654799719782257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-213141955146098798237119451573040000000000000)
      constant := (6536661219385721771265565798574332412868359913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106131027248492326647/20000000000000000000)
  centralHi := (132663784060615408309/25000000000000000000)
  directionLo := (26649899795897234753/5000000000000000000)
  directionHi := (532997995917944695061/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree115.table
  base := (21086076634906379693682948568147007269043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-4784976241510575530318524431681046839375000000000)
      constant := (148039650570750557624986834744988826010730959349027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree115.table
  base := (10543038317033264411149182207737476850651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-53752625926008031266559086260440000000000000)
      constant := (1663445849470414271345485058958134572473478659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26649899795897234753/5000000000000000000)
  centralHi := (532997995917944695061/100000000000000000000)
  directionLo := (6691632527882597883/1250000000000000000)
  directionHi := (535330602230607830641/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree116.table
  base := (10906571381648206554214438773654697093969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-2413280033010951125708960390122391801250000000000)
      constant := (75334401002800651350217017938236043049302798121841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree116.table
  base := (10906571381291755907063424197289808019533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-54219763065491362973838309627620000000000000)
      constant := (1692988022260765270549311250413067070726868197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6691632527882597883/1250000000000000000)
  centralHi := (535330602230607830641/100000000000000000000)
  directionLo := (537653088633019138447/100000000000000000000)
  directionHi := (33603318039563696153/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree117.table
  base := (45101548055001252644350903823117441704193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9736287781066457945034634257617040731250000000000)
      constant := (306642475427507616708562443740432512281708978237377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree117.table
  base := (45101548053791059967736824704899033434457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-218747600819898778724470131979200000000000000)
      constant := (6891167292866081080061221545455421384917389713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537653088633019138447/100000000000000000000)
  centralHi := (33603318039563696153/6250000000000000000)
  directionLo := (269982792853852542213/50000000000000000000)
  directionHi := (539965585707705084427/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree118.table
  base := (46597940853879629729027396121083827418837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9819455430089111387233426954744514257500000000000)
      constant := (311993915390271279142865061733493381078945194194293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree118.table
  base := (23298970426426258541511282735799709866573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-110308074688916052776793512723960000000000000)
      constant := (3505714504673739643151791861709821385015203557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269982792853852542213/50000000000000000000)
  centralHi := (539965585707705084427/100000000000000000000)
  directionLo := (271134110626413472843/50000000000000000000)
  directionHi := (542268221252826945687/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree119.table
  base := (6014432990281821403808658011850434301871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1237827884888970603679027456483998472968750000000)
      constant := (39673990487421482689743702940115055065080410566419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree119.table
  base := (24057731960691452128020304509844259938299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-111242348967882716191351959458320000000000000)
      constant := (3566368619242267605248636017279752526166681891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271134110626413472843/50000000000000000000)
  centralHi := (542268221252826945687/100000000000000000000)
  directionLo := (544561120364596676391/100000000000000000000)
  directionHi := (68070140045574584549/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree120.table
  base := (9930823451861670407573627535160909583847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-9985790728134418271631012348999461310000000000000)
      constant := (322836500954707099549315965965027707939155542370915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree120.table
  base := (9930823451713731442880324031344515241493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-224353246493698759211820812385360000000000000)
      constant := (7255091980274963550601144836319433716566769185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544561120364596676391/100000000000000000000)
  centralHi := (68070140045574584549/12500000000000000000)
  directionLo := (546844405516582587687/100000000000000000000)
  directionHi := (68355550689572823461/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree121.table
  base := (51213900864354200948596719115798628961177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-10068958377157071713829805046126934836250000000000)
      constant := (328327646556191105981303603751963383033418208958553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree121.table
  base := (25606950431863270411512823543752280048897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-113110897525816043020468852927040000000000000)
      constant := (3689246617358422549560381272053360154657351673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546844405516582587687/100000000000000000000)
  centralHi := (68355550689572823461/12500000000000000000)
  directionLo := (549118196636047103689/100000000000000000000)
  directionHi := (54911819663604710369/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree122.table
  base := (26397407368407755076108984509601880924939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5076063013089862578014298871627204181250000000000)
      constant := (166932680351875885267892935934121558783552343696171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree122.table
  base := (10558962947256590418965487535835885477063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-228090343609565412870054599322800000000000000)
      constant := (7502941001808568605265402684680175011525349835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549118196636047103689/100000000000000000000)
  centralHi := (54911819663604710369/10000000000000000000)
  directionLo := (8615353299647675447/1562500000000000000)
  directionHi := (551382611177451228609/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree123.table
  base := (27198429438104170339511121223725450061321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5117646837601189299113695220190940944375000000000)
      constant := (169724821698664286026251847819739015099186479174969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree123.table
  base := (54396858875756505212922920542157055679509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-229958892167498739699171492791520000000000000)
      constant := (7628435281548781856275437901506439169403740781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8615353299647675447/1562500000000000000)
  centralHi := (551382611177451228609/100000000000000000000)
  directionLo := (276818882096626600577/50000000000000000000)
  directionHi := (110727552838650640231/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree124.table
  base := (28010016641063350723746689261685543985209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5159230662112516020213091568754677707500000000000)
      constant := (172540247318435368747132053320563789773539761098201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree124.table
  base := (56020033281743378272386797975690912878437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-231827440725432066528288386260240000000000000)
      constant := (7754976073936350516419933033344115774275529533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276818882096626600577/50000000000000000000)
  centralHi := (110727552838650640231/20000000000000000000)
  directionLo := (277941884201061044501/50000000000000000000)
  directionHi := (555883768402122089003/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree125.table
  base := (7208042244278770291167127439263170442981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1300203621655960685328121979329603617656250000000)
      constant := (43844739302791961605397801006692153166909146559209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree125.table
  base := (57664337953904983926990972544556690067117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-233695989283365393357405279728960000000000000)
      constant := (7882563378970323493843333354497659742398531653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277941884201061044501/50000000000000000000)
  centralHi := (555883768402122089003/100000000000000000000)
  directionLo := (139530183563670189683/25000000000000000000)
  directionHi := (558120734254680758733/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree126.table
  base := (5932977289223343131498344098641634276057/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5242398311135169462411884265882151233750000000000)
      constant := (178240951376843879813163013514607742846958491774365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree126.table
  base := (14832443222989398882243990345420943439739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-58891134460324680046630543299420000000000000)
      constant := (2002799299162475950098020619398367430122226851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139530183563670189683/25000000000000000000)
  centralHi := (558120734254680758733/100000000000000000000)
  directionLo := (560348769996886717449/100000000000000000000)
  directionHi := (11206975399937734349/2000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree127.table
  base := (30508169047948792243113629284588281260927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5283982135646496183511280614445887996875000000000)
      constant := (181126229815448529070287160200830286867008712536303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree127.table
  base := (61016338095663618750563652724980433617037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-237433086399232047015639066666400000000000000)
      constant := (8140877526974424033599451686691830038030256933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560348769996886717449/100000000000000000000)
  centralHi := (11206975399937734349/2000000000000000000)
  directionLo := (140641995432788434019/25000000000000000000)
  directionHi := (562567981731153736077/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree128.table
  base := (784050419562783585446349536906223551453/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1331391490039455726152669240752406190000000000000)
      constant := (46008698131742323077009196454724767022644773875170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree128.table
  base := (62724033564824247818778538982552014980441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-239301634957165373844755960135120000000000000)
      constant := (8271604369943325748049152780967108610080058769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140641995432788434019/25000000000000000000)
  centralHi := (562567981731153736077/100000000000000000000)
  directionLo := (564778473475311907257/100000000000000000000)
  directionHi := (282389236737655953629/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree129.table
  base := (64452859299441583487735773343888674175473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-10734299569338299251420146623146723046250000000000)
      constant := (373933279022791434749486158229197154329529962213297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree129.table
  base := (32226429649636643423922328577794561313873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-120585091757549350336936426801920000000000000)
      constant := (4201688862778071049749020540177824922730669257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564778473475311907257/100000000000000000000)
  centralHi := (282389236737655953629/50000000000000000000)
  directionLo := (566980347219498841269/100000000000000000000)
  directionHi := (56698034721949884127/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree130.table
  base := (129302373630888038692593142533022801687/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1352183402295119086702367415034274571562500000000)
      constant := (47480442692179768800908275462529984509455677958352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree130.table
  base := (8275351912358993943865383145017534902611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-30379841509129003437873718384070000000000000)
      constant := (1067024699226560405360548249567954255541434299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566980347219498841269/100000000000000000000)
  centralHi := (56698034721949884127/10000000000000000000)
  directionLo := (56917370298107004099/10000000000000000000)
  directionHi := (569173702981070040991/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree131.table
  base := (16993475390906381577432241862519605350467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-2725158716845901533954433004350417524687500000000)
      constant := (96450093149466042493959812326027755509691147056363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree131.table
  base := (67973901563504495894417297880870393139913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-244907280630965354332106640541280000000000000)
      constant := (8670063974712024047599815059022084934330015617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56917370298107004099/10000000000000000000)
  centralHi := (569173702981070040991/100000000000000000000)
  directionLo := (285679319428806051573/50000000000000000000)
  directionHi := (571358638857612103147/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree132.table
  base := (34883059046588580465492667087043193812427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5491901258203129789008262357264571812500000000000)
      constant := (195901886102028682964775752756532616283172582469803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree132.table
  base := (6976611809307453289792390961279335908251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-123387914594449340580611767005000000000000000)
      constant := (4402488434127246881308187494402848272831385295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285679319428806051573/50000000000000000000)
  centralHi := (571358638857612103147/100000000000000000000)
  directionLo := (573535251078138250251/100000000000000000000)
  directionHi := (143383812769534562563/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree133.table
  base := (71579464887588958223265683219039547082891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11066970165428913020215317411656617151250000000000)
      constant := (397853740356007655790924578937285341055423101602699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree133.table
  base := (1789486622187548487923474190823485974911/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-31080547218354000998792553434840000000000000)
      constant := (1117617034304958415287756779859455860517624995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573535251078138250251/100000000000000000000)
  centralHi := (143383812769534562563/25000000000000000000)
  directionLo := (287851817026270894959/50000000000000000000)
  directionHi := (575703634052541789919/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree134.table
  base := (14682788389358806465831186739878550784717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11150137814451566462414110108784090677500000000000)
      constant := (403950277053706674848808937759820404079267535148065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree134.table
  base := (73413941946720252992799836035374141354959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-250512926304765334819457320947440000000000000)
      constant := (9077942193267358032767769464972165963066079831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287851817026270894959/50000000000000000000)
  centralHi := (575703634052541789919/100000000000000000000)
  directionLo := (577863880419379410297/100000000000000000000)
  directionHi := (288931940209689705149/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree135.table
  base := (15053909854147406303295962830141776849767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11233305463474219904612902805911564203750000000000)
      constant := (410093382297147500843863352613402633250552266445315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree135.table
  base := (75269549270674480736042503543030806223639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-252381474862698661648574214416160000000000000)
      constant := (9215994624737411419829716259417973534682201951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577863880419379410297/100000000000000000000)
  centralHi := (288931940209689705149/50000000000000000000)
  directionLo := (36251005068253296167/6250000000000000000)
  directionHi := (580016081092052738673/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree136.table
  base := (77146286859372286370553112611687649801063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11316473112496873346811695503039037730000000000000)
      constant := (416283056086324422382424486853784126744231890436807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree136.table
  base := (38573143429659629081897028272079900561597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-127125011710315994238845553942440000000000000)
      constant := (4677546784424850027187302303938832440677525973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36251005068253296167/6250000000000000000)
  centralHi := (580016081092052738673/100000000000000000000)
  directionLo := (291080162651726650737/50000000000000000000)
  directionHi := (23286413012138132059/4000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree137.table
  base := (39522077356331126104006716610731674549019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5699820380759763394505244100083255628125000000000)
      constant := (211259649210616372072788186226394652417656027841291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree137.table
  base := (1580883094252345986158116157316998107929/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-128059285989282657653404000676800000000000000)
      constant := (4747619512802059600058952424041266192129314025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291080162651726650737/50000000000000000000)
  centralHi := (23286413012138132059/4000000000000000000)
  directionLo := (116859340129826583263/20000000000000000000)
  directionHi := (146074175162283229079/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree138.table
  base := (1619263056611523981189529797759038930961/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5741404205271090115604640448646992391250000000000)
      constant := (214401054650934311529525412473556165543817848473225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree138.table
  base := (20240788207634523439673276363091106402359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-64496780134124660533981223705580000000000000)
      constant := (2409107748750145788329703198102002917884226431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116859340129826583263/20000000000000000000)
  centralHi := (146074175162283229079/25000000000000000000)
  directionLo := (146606323282264652203/25000000000000000000)
  directionHi := (586425293129058608813/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree139.table
  base := (82903281213089109962261106584929419358497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11565976059564833673408073594421458308750000000000)
      constant := (435131488728228930514278604392994578611235655128033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree139.table
  base := (82903281213056810870601874336605829981007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-259855669094431968965041788291040000000000000)
      constant := (9778669477039022164693967044271525776416648663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146606323282264652203/25000000000000000000)
  centralHi := (586425293129058608813/100000000000000000000)
  directionLo := (73568273398501046061/12500000000000000000)
  directionHi := (588546187188008368489/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree140.table
  base := (21216134965045188631668265970183330977687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-2912285927146871778901716572887232958750000000000)
      constant := (110376859175077784127265570210514617946668656621943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree140.table
  base := (42432269930076689175340169624412164375891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-130862108826182647897079340879880000000000000)
      constant := (4960977235859689925586233033470173769731877819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73568273398501046061/12500000000000000000)
  centralHi := (588546187188008368489/100000000000000000000)
  directionLo := (14766486643866535731/2500000000000000000)
  directionHi := (590659465754661429241/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree141.table
  base := (10855866096479363746941139747867908067227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1466538919701267569725707373584550670156250000000)
      constant := (55991244152264151528897144620782686732332675329503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree141.table
  base := (86846928771811707563364211923936635099307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-263592766210298622623275575228480000000000000)
      constant := (10066285979041611019777009774677858007993953363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14766486643866535731/2500000000000000000)
  centralHi := (590659465754661429241/100000000000000000000)
  directionLo := (148191302569858567913/25000000000000000000)
  directionHi := (592765210279434271653/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree142.table
  base := (44425223974019353131498441794194931372669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-5907739503316397000002225842901939443750000000000)
      constant := (227199519140816774079634014039969086136121678706141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree142.table
  base := (88850447948019042271431808494960580015169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-265461314768231949452392468697200000000000000)
      constant := (10211663999005679838237242457501704269262609721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148191302569858567913/25000000000000000000)
  centralHi := (592765210279434271653/100000000000000000000)
  directionLo := (594863500771111188329/100000000000000000000)
  directionHi := (59486350077111118833/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree143.table
  base := (90875097388782075586920872064549882537903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11898646655655447442203244382931352413750000000000)
      constant := (460914691890870885219141975676159842353207984811567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree143.table
  base := (1817501947775308224480534433503438720431/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-133664931663082638140754681082960000000000000)
      constant := (5179044265805779148654754233671738984142266975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594863500771111188329/100000000000000000000)
  centralHi := (59486350077111118833/10000000000000000000)
  directionLo := (9327412747379937837/1562500000000000000)
  directionHi := (596954415832316021569/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree144.table
  base := (92920877094057289729258361550649237455839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-11981814304678100884402037080058825940000000000000)
      constant := (467476914045824256923799696378848967704466885406271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree144.table
  base := (92920877094043168108593240615882076140047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-269198411884098603110626255634640000000000000)
      constant := (10505559576859224918501838812429212751877392023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9327412747379937837/1562500000000000000)
  centralHi := (596954415832316021569/100000000000000000000)
  directionLo := (29951901634693478383/5000000000000000000)
  directionHi := (599038032693869567661/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree145.table
  base := (47493893531929285642591706831698463569137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6032490976850377163300414888593149733125000000000)
      constant := (237042852373246470376972956099922844841295295640993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree145.table
  base := (94987787063846604997166960517724805765119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-271066960442031929939743149103360000000000000)
      constant := (10654077134748663668244581479677488979394219271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29951901634693478383/5000000000000000000)
  centralHi := (599038032693869567661/100000000000000000000)
  directionLo := (4808915417984601097/800000000000000000)
  directionHi := (300557213624037568563/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree146.table
  base := (9707582729818176705119866632056087790633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6074074801361703884399811237156886496250000000000)
      constant := (240370531996438208656036765012149044586944134832685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree146.table
  base := (48537913649085813808376194315341201486361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-136467754499982628384430021286040000000000000)
      constant := (5401820602639931522862446064976753434975188049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4808915417984601097/800000000000000000)
  centralHi := (300557213624037568563/50000000000000000000)
  directionLo := (120636734816194571723/20000000000000000000)
  directionHi := (75397959260121607327/12500000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree147.table
  base := (99184997797024073702169511370198272331219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-12231317251746061210998415171441246518750000000000)
      constant := (487442991784974336015773714900508963073495399387091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree147.table
  base := (2479624944925387065604318656811644677903/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (61798)
      previous := (30899)
      next := (30899)
      square := (221055967791219468623203914826250000000000)
      linear := (-34350507194737322949747117005100000000000000)
      constant := (1369281473556601914600223398992339549501147635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120636734816194571723/20000000000000000000)
  centralHi := (75397959260121607327/12500000000000000000)
  directionLo := (18913932703237547197/3125000000000000000)
  directionHi := (121049169300720302061/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree148.table
  base := (50657649280191903726030218617769705824257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6157242450384357326598603934284360022500000000000)
      constant := (247095744061393243145812640207416954291624404224673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree148.table
  base := (50657649280188264311528440432813988633531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-138336303057915955213546914754760000000000000)
      constant := (5552954442133757935396430049021534494071588579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18913932703237547197/3125000000000000000)
  centralHi := (121049169300720302061/20000000000000000000)
  directionLo := (607301016582304950447/100000000000000000000)
  directionHi := (37956313536394059403/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree149.table
  base := (25866682397065052677502713300037713402567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-3099413137447842023849000141424048392812500000000)
      constant := (125246638251578193348925582505509403878277308433263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree149.table
  base := (103466729588254043971036978640347560543357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-278541154673765237256210722978240000000000000)
      constant := (11258612492723962680604699659387136297566289813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607301016582304950447/100000000000000000000)
  centralHi := (37956313536394059403/6250000000000000000)
  directionLo := (609349255168118593341/100000000000000000000)
  directionHi := (304674627584059296671/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree150.table
  base := (5281964544032664492576953087910611221257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-3120205049703505384398698315705916774375000000000)
      constant := (126957046608888299531330981185547403347735644288365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree150.table
  base := (52819645440324032763950139652598576147501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-140204851615849282042663808223480000000000000)
      constant := (5706181306911077924888224116156149400398330309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609349255168118593341/100000000000000000000)
  centralHi := (304674627584059296671/50000000000000000000)
  directionLo := (611390631925269833109/100000000000000000000)
  directionHi := (61139063192526983311/10000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree151.table
  base := (53916491218781839578590863691490248237741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6281993923918337489896792979975570311875000000000)
      constant := (257358194205253919901644931240039936674286446224349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree151.table
  base := (107832982437559253423297244799298473629663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-282278251789631890914444509915680000000000000)
      constant := (11567159247562097232612293964405549412425723367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611390631925269833109/100000000000000000000)
  centralHi := (61139063192526983311/10000000000000000000)
  directionLo := (153356303839706212759/25000000000000000000)
  directionHi := (613425215358824851037/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree152.table
  base := (27511951064748131688898678022520361384751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-3161788874214832105498094664269653537500000000000)
      constant := (130412789732794210503495787899059266229997292452239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree152.table
  base := (27511951064747194425841785234120689968241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-71036700086891304435890350846100000000000000)
      constant := (2930750598485947528942960513334485018120788969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153356303839706212759/25000000000000000000)
  centralHi := (613425215358824851037/100000000000000000000)
  directionLo := (123090614568302569631/20000000000000000000)
  directionHi := (153863268210378212039/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree153.table
  base := (7017734771558837441780096246271286054497/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1591290393235247733023896419275760959531250000000)
      constant := (66079062249695050081662699164900903838838043506566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree153.table
  base := (22456751268987644674523423887647677502291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-286015348905498544572678296853120000000000000)
      constant := (11879892052967238951532753088295131630519677095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123090614568302569631/20000000000000000000)
  centralHi := (153863268210378212039/25000000000000000000)
  directionLo := (308737135319878709759/50000000000000000000)
  directionHi := (617474270639757419519/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree154.table
  base := (114540838695412200810388471877644330847091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-12813490794904635306389964051333561202500000000000)
      constant := (535660405609658753923873033909493466627765387596499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree154.table
  base := (114540838695409510900204040896256011851129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-287883897463431871401795190321840000000000000)
      constant := (12037828224632449134492888690679183137289821361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308737135319878709759/50000000000000000000)
  centralHi := (617474270639757419519/100000000000000000000)
  directionLo := (309744436969471763037/50000000000000000000)
  directionHi := (24779554957557741043/4000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree155.table
  base := (116819051310407108063997266022464802863421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-12896658443927288748588756748461034728750000000000)
      constant := (542734881767472173965485675787263613360530479551869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree155.table
  base := (5840952565520241486246536893364717830851/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-72438111505341299557728020947640000000000000)
      constant := (3049202727234856703696461504285507461934302295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309744436969471763037/50000000000000000000)
  centralHi := (24779554957557741043/4000000000000000000)
  directionLo := (155374236716986830239/25000000000000000000)
  directionHi := (621496946867947320957/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree156.table
  base := (29779598547482128086254186525675030380661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 312648722500000000000000000000000000000000000000
      center := (5502617516)
      previous := (2751308758)
      next := (2751308758)
      square := (19683265484065763925147322983958952500000000000)
      linear := (-3244956523237485547696887361397127063750000000000)
      constant := (137463981617750239964967999980179921478996190142229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree156.table
  base := (29779598547481645671168577299809151328511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-72905248644824631265007244314820000000000000)
      constant := (3089210026472044685495805459586843906081787399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155374236716986830239/25000000000000000000)
  centralHi := (621496946867947320957/100000000000000000000)
  directionLo := (9742164883171171027/1562500000000000000)
  directionHi := (623498552522954945729/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree157.table
  base := (60719433666989486950934470001635191703471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6531496870986297816493171071357990890625000000000)
      constant := (278511769860122715895195689086746771189263279036319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree157.table
  base := (121438867333977339625305178745876013946677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-293489543137231851889145870728000000000000000)
      constant := (12517915815478712134782066174900525723176215693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9742164883171171027/1562500000000000000)
  centralHi := (623498552522954945729/100000000000000000000)
  directionLo := (312746876495297662853/50000000000000000000)
  directionHi := (625493752990595325707/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree158.table
  base := (61890235371280591386984990803766320690281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6573080695497624537592567419921727653750000000000)
      constant := (282118860757602963085999291053696700691952294126409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree158.table
  base := (61890235371279899360635309972390292670201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-147679045847582589359131382098360000000000000)
      constant := (6340019018855517286177200708943804332110594609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312746876495297662853/50000000000000000000)
  centralHi := (625493752990595325707/100000000000000000000)
  directionLo := (313741304685205479401/50000000000000000000)
  directionHi := (627482609370410958803/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree159.table
  base := (63071602207838963183419465282190411960071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (3917848)
      previous := (1958924)
      next := (1958924)
      square := (14014428966938956158880258443545000000000000)
      linear := (-2354811149878587133745804118364351875000000000)
      constant := (101726321085062796652937604325715638491030570991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree159.table
  base := (63071602207838377136592166144531741773427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (88)
      previous := (44)
      next := (44)
      square := (314782439004940503557428145000000000000)
      linear := (-52906130340530171866746112080000000000000)
      constant := (2286081661193512620842052589744531741773427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313741304685205479401/50000000000000000000)
  centralHi := (627482609370410958803/100000000000000000000)
  directionLo := (314732590898344853409/50000000000000000000)
  directionHi := (629465181796689706819/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree160.table
  base := (64263534176666031249764827184562380315921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6656248344520277979791360117049201180000000000000)
      constant := (289402895371138192730198273144680933270932738824369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree160.table
  base := (64263534176665534971975620889076691425317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-149547594405515916188248275567080000000000000)
      constant := (6503711010050539086709958102962216426213715453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314732590898344853409/50000000000000000000)
  centralHi := (629465181796689706819/100000000000000000000)
  directionLo := (631441529459679658851/100000000000000000000)
  directionHi := (157860382364919914713/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree161.table
  base := (26186412511105299409172617765612306151611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-13395664338063209401781512931225875886250000000000)
      constant := (586159678174387071171672982379304945593917953433895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree161.table
  base := (5237282502221026262401059036200322496041/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-300963737368965159205613444602880000000000000)
      constant := (13172683780258815557453708141234287647284479225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631441529459679658851/100000000000000000000)
  centralHi := (157860382364919914713/25000000000000000000)
  directionLo := (633411710626208241343/100000000000000000000)
  directionHi := (9897057978534503771/1562500000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree162.table
  base := (133358187022264165430597138388867523094793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-13478831987085862843980305628353349412500000000000)
      constant := (593560134152215215832752990850636930618961761140777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree162.table
  base := (133358187022263453743292659810152893102959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-302832285926898486034730338071600000000000000)
      constant := (13338992053058374313389895549134079476726211831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633411710626208241343/100000000000000000000)
  centralHi := (9897057978534503771/1562500000000000000)
  directionLo := (127075156531945179133/20000000000000000000)
  directionHi := (317687891329862947833/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree163.table
  base := (67902720876774008679590585915093892355133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6780999818054258143089549162740411469375000000000)
      constant := (300503579337880594166146385139093862657864095757037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree163.table
  base := (13580544175354741475589155643173509154181/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-152350417242415906431923615770160000000000000)
      constant := (6753173419249881368470917320858531936070472145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127075156531945179133/20000000000000000000)
  centralHi := (317687891329862947833/50000000000000000000)
  directionLo := (19916681313743557189/3125000000000000000)
  directionHi := (637333802039793830049/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree164.table
  base := (69136913374690502129306173469593857541897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6822583642565584864188945511304148232500000000000)
      constant := (304250375872512678887122203009636302650790934910633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree164.table
  base := (34568456687345123509664465245156722810597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (123596)
      previous := (61798)
      next := (61798)
      square := (442111935582438937246407829652500000000000)
      linear := (-76642345760691284923241031252260000000000000)
      constant := (3418687034145747281783457519457645234374966973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19916681313743557189/3125000000000000000)
  centralHi := (637333802039793830049/100000000000000000000)
  directionLo := (127857164876206915187/20000000000000000000)
  directionHi := (9988841005953665249/1562500000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree165.table
  base := (140763342009766068990096334787658590445559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-13728334934153823170576683719735769991250000000000)
      constant := (616040913360008092191326477222031869896527203359351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree165.table
  base := (140763342009765637006514172324844653226947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-308437931600698466522081018477760000000000000)
      constant := (13844195947308061757636399437694888630914494123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127857164876206915187/20000000000000000000)
  centralHi := (9988841005953665249/1562500000000000000)
  directionLo := (641231904451563337591/100000000000000000000)
  directionHi := (80153988056445417199/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree166.table
  base := (4477312110459566795756302374093146057133/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1726437822897059576596934552107905439687500000000)
      constant := (77953455440088719687052443159099941319514827390148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree166.table
  base := (143273987534705771733770353006620961665901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-310306480158631793351197911946480000000000000)
      constant := (14014690270674988853410279125191118281319515909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641231904451563337591/100000000000000000000)
  centralHi := (80153988056445417199/12500000000000000000)
  directionLo := (321586048095458708103/50000000000000000000)
  directionHi := (643172096190917416207/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree167.table
  base := (9112860207762756990504827847714597742197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156324361250000000000000000000000000000000000000
      center := (2751308758)
      previous := (1375654379)
      next := (1375654379)
      square := (9841632742032881962573661491979476250000000000)
      linear := (-1736833779024891256871783639248839630468750000000)
      constant := (78907617778391339579133030134411228866226022677166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree167.table
  base := (145805763324203802220809110575997653635627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-312175028716565120180314805415200000000000000)
      constant := (14186231106683778571792544165827337409062476243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321586048095458708103/50000000000000000000)
  centralHi := (643172096190917416207/100000000000000000000)
  directionLo := (322553226363750157019/50000000000000000000)
  directionHi := (645106452727500314039/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree168.table
  base := (74179334689131432551918406059240094216971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (11005235032)
      previous := (5502617516)
      next := (5502617516)
      square := (39366530968131527850294645967917905000000000000)
      linear := (-6988918940610891748586530905559095285000000000000)
      constant := (319470404739635664446217214442331556977336248387819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree168.table
  base := (14835866937826260298288418884526128011323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (247192)
      previous := (123596)
      next := (123596)
      square := (884223871164877874492815659305000000000000)
      linear := (-157021788637249223504715849441960000000000000)
      constant := (7179409227667219493648271162986129467919031535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell147.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322553226363750157019/50000000000000000000)
  centralHi := (645106452727500314039/100000000000000000000)
  directionLo := (647035026395556478769/100000000000000000000)
  directionHi := (64703502639555647877/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 94503
  qDenominator := 178928
  table := BinomialMassData.Q94503_178928.Degree169.table
  base := (150932705696885236638885098623170781661243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (22010470064)
      previous := (11005235032)
      next := (11005235032)
      square := (78733061936263055700589291935835810000000000000)
      linear := (-14061005530244436939371854508245664096250000000000)
      constant := (646667245277131949369369206173866435531668433184827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q94503_178928.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 28
  qDenominator := 53
  table := BinomialMassData.Q28_53.Degree169.table
  base := (150932705696885014743181900884786690243773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (494384)
      previous := (247192)
      next := (247192)
      square := (1768447742329755748985631318610000000000000)
      linear := (-315912125832431773838548592352640000000000000)
      constant := (14532452316626978079513703959040565812894758357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q28_53.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell147.Kernel169
