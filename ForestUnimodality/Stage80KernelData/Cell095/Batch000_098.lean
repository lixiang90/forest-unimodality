import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell095.Parameters
import ForestUnimodality.BinomialMassData.Q26_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q26_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch000_049
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree000.table
  base := (1944200537705991079839407141/50000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1193551981400388928289402200000000000000)
      linear := (-33559522600134705436203397000000000000)
      constant := (388840107541198215967881428200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree000.table
  base := (1944200537705991079839407141/50000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1193551981400388928289402200000000000000)
      linear := (-33559522600134705436203397000000000000)
      constant := (388840107541198215967881428200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree001.table
  base := (54901438191968069887727568155334871018787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-3252588172956781806663059669997000000000000)
      constant := (572045904015630240646849660679725998079459948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree001.table
  base := (219212798032982347918771360220806455329669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-3842786614875244580543578101217297000000000000)
      constant := (673114766865272650300046340390765478597220483669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9997582471123184849/20000000000000000000)
  directionHi := (24993956177807962123/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree002.table
  base := (25797073524072861597865932653530010288533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-6417888027630613244486554304397000000000000)
      constant := (338807305592209773981157809116801783802371665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree002.table
  base := (128566647782916558156478930872153436636259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-7582679699898953554085051151029197000000000000)
      constant := (398112750307744564831337254713494915380206730259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9997582471123184849/20000000000000000000)
  centralHi := (24993956177807962123/50000000000000000000)
  directionLo := (70693583608029649531/100000000000000000000)
  directionHi := (17673395902007412383/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree003.table
  base := (39689225981952271926784973261132400823327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-1064798653589382742478894326533000000000000)
      constant := (23762047065984335629008152333608527675883006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree003.table
  base := (79037281033683024600357480219818844408303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-11322572784922662527626524200841097000000000000)
      constant := (251085894952524815132528429705831619024701406303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70693583608029649531/100000000000000000000)
  centralHi := (17673395902007412383/25000000000000000000)
  directionLo := (86581603964226820861/100000000000000000000)
  directionHi := (43290801982113410431/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree004.table
  base := (51325388169572034510562167684536899590471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-12748487736978276120133543573197000000000000)
      constant := (146584792567754582887983995160368475834815071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree004.table
  base := (10214230146389482667304828073639783360339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-15062465869946371501167997250652997000000000000)
      constant := (172083005980543280089321078516986560112913671695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86581603964226820861/100000000000000000000)
  centralHi := (43290801982113410431/50000000000000000000)
  directionLo := (99975824711231848491/100000000000000000000)
  directionHi := (24993956177807962123/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree005.table
  base := (17368557166532577968953204231314447639151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-15913787591652107557957038207597000000000000)
      constant := (110744762500807936579627494113407756618863502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree005.table
  base := (3455233203895065698415277106412470230403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-18802358954970080474709470300464897000000000000)
      constant := (130088647720239820353034874304603480138858284030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99975824711231848491/100000000000000000000)
  centralHi := (24993956177807962123/25000000000000000000)
  directionLo := (111776370080458847857/100000000000000000000)
  directionHi := (55888185040229423929/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree006.table
  base := (24353766240135354344432687750330935661783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-2119898605147326555086725871333000000000000)
      constant := (10295269619084288147241194111593640406255287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree006.table
  base := (302726535520652783866179480291725003431/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-22542252039993789448250943350276797000000000000)
      constant := (108967370230330049214249306550532851679555954480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111776370080458847857/100000000000000000000)
  centralHi := (55888185040229423929/50000000000000000000)
  directionLo := (122444878578225700663/100000000000000000000)
  directionHi := (15305609822278212583/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree007.table
  base := (17423321849772859185587211844802053182969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-22244387300999770433604027476397000000000000)
      constant := (85164775451940139938229336412084140328902369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree007.table
  base := (4330159756299834353065936565974662703169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-26282145125017498421792416400088697000000000000)
      constant := (100294158066791249496556586715789962540315428676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122444878578225700663/100000000000000000000)
  centralHi := (15305609822278212583/12500000000000000000)
  directionLo := (66127792326126339281/50000000000000000000)
  directionHi := (132255584652252678563/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree008.table
  base := (12490952899232742531352469027349622773591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-25409687155673601871427522110797000000000000)
      constant := (84482800829953018872827714356312368834110191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree008.table
  base := (1241001811073439274226339359949363298203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-30022038210041207395333889449900597000000000000)
      constant := (99623731419583515138803103338798104216536962030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66127792326126339281/50000000000000000000)
  centralHi := (132255584652252678563/100000000000000000000)
  directionLo := (70693583608029649531/50000000000000000000)
  directionHi := (141387167216059299063/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree009.table
  base := (8776092211751668138651820394429372663207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-3174998556705270367694557416133000000000000)
      constant := (9842360831003976951191504783212088699666823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree009.table
  base := (2177418323379518237082382289260442926511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-33761931295064916368875362499712497000000000000)
      constant := (104575074368789299309218182732519120842502610044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70693583608029649531/50000000000000000000)
  centralHi := (141387167216059299063/100000000000000000000)
  directionLo := (149963737066847772737/100000000000000000000)
  directionHi := (74981868533423886369/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree010.table
  base := (1170108392061160956730452000138785632441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-31740286865021264747074511379597000000000000)
      constant := (96346372851099475988727174026024907149895205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree010.table
  base := (1158832448432724664744770520823586864877/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-37501824380088625342416835549524397000000000000)
      constant := (113843780300934480690187489339437223256498734385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149963737066847772737/100000000000000000000)
  centralHi := (74981868533423886369/50000000000000000000)
  directionLo := (19759457315077393009/12500000000000000000)
  directionHi := (158075658520619144073/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree011.table
  base := (433968360645888671537481556540383960951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-34905586719695096184898006013997000000000000)
      constant := (107147290715591429069204321328334309459468408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree011.table
  base := (3422692576294761450953213461175331545947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-41241717465112334315958308599336297000000000000)
      constant := (126691579536992997013394606296111475945205047947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19759457315077393009/12500000000000000000)
  centralHi := (158075658520619144073/100000000000000000000)
  directionLo := (8289557466837438329/5000000000000000000)
  directionHi := (165791149336748766581/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree012.table
  base := (748105393165644105652635095189667898307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-4230098508263214180302388960933000000000000)
      constant := (13401196384033387100656604886115628045221446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree012.table
  base := (145283943543408839138213491311842135829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-44981610550136043289499781649148197000000000000)
      constant := (142681797312316282655584223051982132002938498290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8289557466837438329/5000000000000000000)
  centralHi := (165791149336748766581/100000000000000000000)
  directionLo := (173163207928453641723/100000000000000000000)
  directionHi := (43290801982113410431/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree013.table
  base := (-3313257046087599652599384411798795303/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-41236186429042759060544995282797000000000000)
      constant := (136503762534843462440983189151531566670844850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree013.table
  base := (-204366742399766121330584823878768022001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-48721503635159752263041254698960097000000000000)
      constant := (161541652860899894398783948596636978115776911999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173163207928453641723/100000000000000000000)
  centralHi := (43290801982113410431/25000000000000000000)
  directionLo := (22529247643946638149/12500000000000000000)
  directionHi := (180233981151573105193/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree014.table
  base := (-1573289820368950368676754479487108950241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-44401486283716590498368489917197000000000000)
      constant := (154671735482395192205422075351962029620423159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree014.table
  base := (-803992775706189267338014287608473028771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-52461396720183461236582727748771997000000000000)
      constant := (183090069407849940649409675496314613670630170458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22529247643946638149/12500000000000000000)
  centralHi := (180233981151573105193/100000000000000000000)
  directionLo := (46759410378699673921/25000000000000000000)
  directionHi := (37407528302959739137/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree015.table
  base := (-1384250777294896967575514521534863704641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-5285198459821157992910220505733000000000000)
      constant := (19445098081336420139846259293922848778717502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree015.table
  base := (-2799650577286531304891340752874279434051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-56201289805207170210124200798583897000000000000)
      constant := (207199398337829424713855862746745567630920199949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46759410378699673921/25000000000000000000)
  centralHi := (37407528302959739137/20000000000000000000)
  directionLo := (193602352064976441253/100000000000000000000)
  directionHi := (96801176032488220627/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree016.table
  base := (-151293996771371800204192158236196847897/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-50732085993064253374015479185997000000000000)
      constant := (197425438384651712976307683304643299965497575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree016.table
  base := (-1905152565116400394145202970388489349483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-59941182890230879183665673848395797000000000000)
      constant := (233774767430789409273087783899727494531991545034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193602352064976441253/100000000000000000000)
  centralHi := (96801176032488220627/50000000000000000000)
  directionLo := (99975824711231848491/50000000000000000000)
  directionHi := (199951649422463696983/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree017.table
  base := (-289929880116552873687055548811736843889/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10741967832603500354604619800000000000000)
      linear := (-186496144801861885162072573773000000000000)
      constant := (767708879452689808736723753137109894479984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree017.table
  base := (-932786471791042713943617111933737446417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12662392970676726140222267939800000000000000)
      linear := (-220349743859012415768882861239473000000000000)
      constant := (909144098023599308352749166070584647154810235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99975824711231848491/50000000000000000000)
  centralHi := (199951649422463696983/100000000000000000000)
  directionLo := (206105442646322579027/100000000000000000000)
  directionHi := (51526360661580644757/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree018.table
  base := (-5357286819537696293266296374579307707113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-6340298411379101805518052050533000000000000)
      constant := (27587024982449027968913743695790580072644343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree018.table
  base := (-1344924577384904283294498802321597761489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-67420969060278297130748619948019597000000000000)
      constant := (294044265915456542764623468598350774266707858044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206105442646322579027/100000000000000000000)
  centralHi := (51526360661580644757/25000000000000000000)
  directionLo := (212080750824088948593/100000000000000000000)
  directionHi := (106040375412044474297/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree019.table
  base := (-5953239467766914598902601689952029131357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-60227985557085747687485963089197000000000000)
      constant := (276630774089751361401046596667652772229340443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree019.table
  base := (-746655508457187238996046909383071895659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-71160862145302006104290092997831497000000000000)
      constant := (327631676606388574149145824391600411728700882728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212080750824088948593/100000000000000000000)
  centralHi := (106040375412044474297/50000000000000000000)
  directionLo := (4357845167133960689/2000000000000000000)
  directionHi := (217892258356698034451/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree020.table
  base := (-6439693957984686502550708867479694273589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-63393285411759579125309457723597000000000000)
      constant := (306876810325302569004488075204125315194395011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree020.table
  base := (-1291502204679309108982789277392809214639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-74900755230325715077831566047643397000000000000)
      constant := (363465198086666047747185344097967412775538056805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4357845167133960689/2000000000000000000)
  centralHi := (217892258356698034451/100000000000000000000)
  directionLo := (111776370080458847857/50000000000000000000)
  directionHi := (44710548032183539143/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree021.table
  base := (-6827466652771510035227758433056342010407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-7395398362937045618125883595333000000000000)
      constant := (37665911132180333239096949595964717158992377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree021.table
  base := (-684330131783868340323199234383136831757/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-78640648315349424051373039097455297000000000000)
      constant := (401511710980929645420666464372904411656962062430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111776370080458847857/50000000000000000000)
  centralHi := (44710548032183539143/20000000000000000000)
  directionLo := (229073392202428265323/100000000000000000000)
  directionHi := (57268348050607066331/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree022.table
  base := (-7125637263640452074980873078250026965817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-69723885121107242000956446992397000000000000)
      constant := (372956327353067164893399444025555679861909983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree022.table
  base := (-713968120975400026835887019563892652461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-82380541400373133024914512147267197000000000000)
      constant := (441743418130724016195616533064839027136619215390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229073392202428265323/100000000000000000000)
  centralHi := (57268348050607066331/25000000000000000000)
  directionLo := (117232045956726633819/50000000000000000000)
  directionHi := (234464091913453267639/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree023.table
  base := (-11746966975288075635927423275712896221/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-72889184975781073438779941626797000000000000)
      constant := (408746297887760912602742198067925223080736875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree023.table
  base := (-1838571497551432010212617802452594342349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-86120434485396841998455985197079097000000000000)
      constant := (484136909726014000001699286991959060425054494604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117232045956726633819/50000000000000000000)
  centralHi := (234464091913453267639/100000000000000000000)
  directionLo := (47946721171931246523/20000000000000000000)
  directionHi := (29966700732457029077/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree024.table
  base := (-7482574823256494484163804228196842980439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-8450498314494989430733715140133000000000000)
      constant := (49594035271299376006011772570643112378653129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree024.table
  base := (-7493559313872362296256179674221159576971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-89860327570420550971997458246890997000000000000)
      constant := (528672429515111674725784738378254128515847337029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47946721171931246523/20000000000000000000)
  centralHi := (29966700732457029077/12500000000000000000)
  directionLo := (122444878578225700663/50000000000000000000)
  directionHi := (244889757156451401327/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree025.table
  base := (-7553256718607546727263264645324334954971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-79219784685128736314426930895597000000000000)
      constant := (485742189590760558649870820768061404782120429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree025.table
  base := (-1890736536867446782329897500862597371769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-93600220655444259945538931296702897000000000000)
      constant := (575333283224621173017504932005030246132235496924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122444878578225700663/50000000000000000000)
  centralHi := (244889757156451401327/100000000000000000000)
  directionLo := (62484890444519905307/25000000000000000000)
  directionHi := (249939561778079621229/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree026.table
  base := (-1511703504304439868952789904490696047557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-82385084539802567752250425529997000000000000)
      constant := (526921904280107134502865375354270497901521215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree026.table
  base := (-7567051151915734615346454687733949820003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-97340113740467968919080404346514797000000000000)
      constant := (624105352959564067416240355431471706617920981997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62484890444519905307/25000000000000000000)
  centralHi := (249939561778079621229/100000000000000000000)
  directionLo := (254889340545051468991/100000000000000000000)
  directionHi := (3982645946016429203/1562500000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree027.table
  base := (-937783187625187944964255216242318807713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-9505598266052933243341546684933000000000000)
      constant := (63319477344673597486882365916513758916567544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree027.table
  base := (-7509770218665342095661749472221281569489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-101080006825491677892621877396326697000000000000)
      constant := (674976693912843015378351291697974578736665156511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254889340545051468991/100000000000000000000)
  centralHi := (3982645946016429203/1562500000000000000)
  directionLo := (51948962378536092517/20000000000000000000)
  directionHi := (129872405946340231293/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree028.table
  base := (-738780964028130537756047102588163225529/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-88715684249150230627897414798797000000000000)
      constant := (614593758391229851826931110150297874503990710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree028.table
  base := (-46215003259592872320864317565728329229/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-104819899910515386866163350446138597000000000000)
      constant := (727937196946240220584298484484972091296889083360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51948962378536092517/20000000000000000000)
  centralHi := (129872405946340231293/50000000000000000000)
  directionLo := (2116089354436042857/800000000000000000)
  directionHi := (132255584652252678563/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree029.table
  base := (-1443590408408665400554293332090198513603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-91880984103824062065720909433197000000000000)
      constant := (661070002878534398384012961779604968330592985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree029.table
  base := (-1805933254643940118991009968625292115631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-108559792995539095839704823495950497000000000000)
      constant := (782978304979578907435227811251514499742732953476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2116089354436042857/800000000000000000)
  centralHi := (132255584652252678563/50000000000000000000)
  directionLo := (134596573199793459891/50000000000000000000)
  directionHi := (269193146399586919783/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree030.table
  base := (-6995065837864990706518930017361782284763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-10560698217610877055949378229733000000000000)
      constant := (78810873005415904636207636959722444919703493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree030.table
  base := (-7000130424177606435253699768245483329361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-112299686080562804813246296545762397000000000000)
      constant := (840092773928177965597136366565819177366695844639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134596573199793459891/50000000000000000000)
  centralHi := (269193146399586919783/100000000000000000000)
  directionLo := (136897535998810233711/50000000000000000000)
  directionHi := (273795071997620467423/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree031.table
  base := (-6721160994866354271368575477243442493691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-98211583813171724941367898701997000000000000)
      constant := (759272092977376811560044999619971806073909709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree031.table
  base := (-6725593048461459767131280862567606445897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-116039579165586513786787769595574297000000000000)
      constant := (899274470839205907882206816706947369319273352103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136897535998810233711/50000000000000000000)
  centralHi := (273795071997620467423/100000000000000000000)
  directionLo := (278320916985868876671/100000000000000000000)
  directionHi := (2174382163952100599/781250000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree032.table
  base := (-6397939961292160651198773795702074657727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-101376883667845556379191393336397000000000000)
      constant := (810988282596550831463504120391682903815252073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree032.table
  base := (-6401814451173833922545059908064822892223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-119779472250610222760329242645386197000000000000)
      constant := (960518203256786364303318294209291048947621389777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278320916985868876671/100000000000000000000)
  centralHi := (2174382163952100599/781250000000000000)
  directionLo := (452438935091389757/160000000000000000)
  directionHi := (141387167216059299063/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree033.table
  base := (-1506711187961190042456477653368596333021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-11615798169168820868557209774533000000000000)
      constant := (96049186136224932027111075100119902639027724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree033.table
  base := (-1507557129100189580558594596497139875333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-123519365335633931733870715695198097000000000000)
      constant := (1023819574890877684570454557351991860330356586668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452438935091389757/160000000000000000)
  centralHi := (141387167216059299063/50000000000000000000)
  directionLo := (143579347048244018119/50000000000000000000)
  directionHi := (287158694096488036239/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree034.table
  base := (-5609096806092291770931401020255718277593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10741967832603500354604619800000000000000)
      linear := (-372690253900322557975219316973000000000000)
      constant := (3182117971977442050204208669549698535501663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree034.table
  base := (-2806024643184689299847804163833074898691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12662392970676726140222267939800000000000000)
      linear := (-440343454742760002447793040640173000000000000)
      constant := (3768771153933555010187439778514284316799574362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143579347048244018119/50000000000000000000)
  centralHi := (287158694096488036239/100000000000000000000)
  directionLo := (291477112269339480869/100000000000000000000)
  directionHi := (29147711226933948087/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree035.table
  base := (-1029146147534647943531490426763093518377/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-110872783231867050692661877239597000000000000)
      constant := (976553847592846226690121128474715968793507115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree035.table
  base := (-1287076169058199034915206655897056772221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-130999151505681349680953661794821897000000000000)
      constant := (1156580917455658180425774977646878798407254567116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291477112269339480869/100000000000000000000)
  centralHi := (29147711226933948087/10000000000000000000)
  directionLo := (73933119421603718487/25000000000000000000)
  directionHi := (295732477686414873949/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree036.table
  base := (-4637622915050031230889653763967021502469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-12670898120726764681165041319333000000000000)
      constant := (115022850762861115287310080636701530785786459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree036.table
  base := (-2319932506989540644196162607228873304891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-134739044590705058654495134844633797000000000000)
      constant := (1226035068370978280345558668968256551436661778218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73933119421603718487/25000000000000000000)
  centralHi := (295732477686414873949/100000000000000000000)
  directionLo := (149963737066847772737/50000000000000000000)
  directionHi := (11997098965347821819/4000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree037.table
  base := (-4085515667579972552744850303789278735299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-117203382941214713568308866508397000000000000)
      constant := (1095585590921533831660279185000258086009487301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree037.table
  base := (-255466700118912856452558431671274401563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-138478937675728767628036607894445697000000000000)
      constant := (1297535056889586251907711865351306838966535046992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149963737066847772737/50000000000000000000)
  centralHi := (11997098965347821819/4000000000000000000)
  directionLo := (304064600244571958749/100000000000000000000)
  directionHi := (243251680195657567/80000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree038.table
  base := (-872509446917989206034040980874938266209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-120368682795888545006132361142797000000000000)
      constant := (1157692014271142077854071475519813142278361564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree038.table
  base := (-3491735172457260314545308107611230143129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-142218830760752476601578080944257597000000000000)
      constant := (1371078970033954533065925328176978484269936342871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304064600244571958749/100000000000000000000)
  centralHi := (243251680195657567/80000000000000000)
  directionLo := (19259136681509044789/6250000000000000000)
  directionHi := (2465169495233157733/800000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree039.table
  base := (-2851721896384850184867504016861974100737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-13725998072284708493772872864133000000000000)
      constant := (135724837951911185037504180995088889484887007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree039.table
  base := (-2853197207384572342744657598848451266373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-145958723845776185575119553994069497000000000000)
      constant := (1446665188091735319620805210617126788818849115627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19259136681509044789/6250000000000000000)
  centralHi := (2465169495233157733/800000000000000000)
  directionLo := (312174412604936005567/100000000000000000000)
  directionHi := (4877725196952125087/1562500000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree040.table
  base := (-1085509576313367177632430191483444825753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-126699282505236207881779350411597000000000000)
      constant := (1287078999345389673556109745840783120016432894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree040.table
  base := (-434460120279257518646850761817618671963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-149698616930799894548661027043881397000000000000)
      constant := (1524292339656895104221263808142283226670713850185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312174412604936005567/100000000000000000000)
  centralHi := (4877725196952125087/1562500000000000000)
  directionLo := (63230263408247657629/20000000000000000000)
  directionHi := (158075658520619144073/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree041.table
  base := (-1448311712459438329119973204377501888669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-129864582359910039319602845045997000000000000)
      constant := (1354357393617792285296935509959916117587571931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree041.table
  base := (-1449424077704603555298733880205059560311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-153438510015823603522202500093693297000000000000)
      constant := (1603959263563686566152956933990822202933026913689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63230263408247657629/20000000000000000000)
  centralHi := (158075658520619144073/50000000000000000000)
  directionLo := (80019703295728322451/25000000000000000000)
  directionHi := (64015762636582657961/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree042.table
  base := (-683923282729025883236897157583152856423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-14781098023842652306380704408933000000000000)
      constant := (158150875824766876519616397233294468824493753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree042.table
  base := (-171222075037407147627364886245936195813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-157178403100847312495743973143505197000000000000)
      constant := (1685664976656455269339198431518665030010804584748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80019703295728322451/25000000000000000000)
  centralHi := (64015762636582657961/20000000000000000000)
  directionLo := (64791739606297050119/20000000000000000000)
  directionHi := (80989674507871312649/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree043.table
  base := (60935969730224075133898223345250472429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-136195182069257702195249834314797000000000000)
      constant := (1494079752574050837076610739280787992957575658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree043.table
  base := (24207045246071491588763366646284002399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-160918296185871021469285446193317097000000000000)
      constant := (1769408646500482342742488676790045319238196681995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64791739606297050119/20000000000000000000)
  centralHi := (80989674507871312649/25000000000000000000)
  directionLo := (327792662230147831537/100000000000000000000)
  directionHi := (163896331115073915769/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree044.table
  base := (1513815147698916454807443826560425933/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-139360481923931533633073328949197000000000000)
      constant := (1566522399964067187995059591905213547425109120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree044.table
  base := (121014577388448153476785640401314733059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-164658189270894730442826919243128997000000000000)
      constant := (1855189568276320963170409587695802013982989016472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327792662230147831537/100000000000000000000)
  centralHi := (163896331115073915769/50000000000000000000)
  directionLo := (331582298673497533161/100000000000000000000)
  directionHi := (165791149336748766581/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree045.table
  base := (1856789246320947825050941435863859821257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-15836197975400596118988535953733000000000000)
      constant := (182298368098024803011299825217074655488343273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree045.table
  base := (1856161238065090776479432576530616964239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-168398082355918439416368392292940897000000000000)
      constant := (1943007145216258078757916597526757656892973738239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331582298673497533161/100000000000000000000)
  centralHi := (165791149336748766581/50000000000000000000)
  directionLo := (83832277560344135893/25000000000000000000)
  directionHi := (335329110241376543573/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree046.table
  base := (174096746814051613776778562582191713601/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-145691081633279196508720318217997000000000000)
      constant := (1716568057882750117699734616379032490353219216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree046.table
  base := (2785004281976618315137879014620535118437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-172137975440942148389909865342752797000000000000)
      constant := (2032860872039875788130288885854032824793662960437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83832277560344135893/25000000000000000000)
  centralHi := (335329110241376543573/100000000000000000000)
  directionLo := (1695172583816659671/500000000000000000)
  directionHi := (339034516763331934201/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree047.table
  base := (3754976645014739853900195067542418442809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-148856381487953027946543812852397000000000000)
      constant := (1794170267814667313863901150303311830369746209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree047.table
  base := (46931327682609804043448342808979834249/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-175877868525965857363451338392564697000000000000)
      constant := (2124750320928943001180860953362742563712981459920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1695172583816659671/500000000000000000)
  centralHi := (339034516763331934201/100000000000000000000)
  directionLo := (21418741331576406591/6250000000000000000)
  directionHi := (342699861305222505457/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree048.table
  base := (2382477883291319320168494321126859844629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-16891297926958539931596367498533000000000000)
      constant := (208165736853596241577953007264395324990195562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree048.table
  base := (952909778295646065713176678227619488851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-179617761610989566336992811442376597000000000000)
      constant := (2218675129652355596348278567926878953902183274255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21418741331576406591/6250000000000000000)
  centralHi := (342699861305222505457/100000000000000000000)
  directionLo := (346326415856907283447/100000000000000000000)
  directionHi := (43290801982113410431/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree049.table
  base := (5815384033874443270445706433401155478161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-155186981197300690822190802121197000000000000)
      constant := (1954531886056946239469690927117154405398696761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree049.table
  base := (5815032280461300555927637600502882931147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-183357654696013275310534284492188497000000000000)
      constant := (2314634991511522412904329388031339461319779633147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346326415856907283447/100000000000000000000)
  centralHi := (43290801982113410431/12500000000000000000)
  directionLo := (8747884662232786743/2500000000000000000)
  directionHi := (349915386489311469721/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree050.table
  base := (6906175657855274674214285061999388435959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-158352281051974522260014296755597000000000000)
      constant := (2037290807801127789207141358667360409321929359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree050.table
  base := (6905871685134199889803101111697416846497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-187097547781036984284075757542000397000000000000)
      constant := (2412629646827123398600304181184635554248776648497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8747884662232786743/2500000000000000000)
  centralHi := (349915386489311469721/100000000000000000000)
  directionLo := (44183489755018530957/12500000000000000000)
  directionHi := (353467918040148247657/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree051.table
  base := (4018628985530968137107601316315192567253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1193551981400388928289402200000000000000)
      linear := (-62098262555420358976485117797000000000000)
      constant := (815750944985328354139192378154630385134506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree051.table
  base := (8036995393775352181230541519169630384533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12662392970676726140222267939800000000000000)
      linear := (-660337165626507589126703220040873000000000000)
      constant := (8694321369311240447203841269445024858749510597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44183489755018530957/12500000000000000000)
  centralHi := (353467918040148247657/100000000000000000000)
  directionLo := (17849254918995197249/5000000000000000000)
  directionHi := (356985098379903944981/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree052.table
  base := (4604284710357925231089661715285243183363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-164682880761322185135661286024397000000000000)
      constant := (2207963926275302938837276955861657835039854326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree052.table
  base := (2302085672194059736204912195306894782791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-194577333951084402231158703641624197000000000000)
      constant := (2614722492062749249544422049108131807843727955164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17849254918995197249/5000000000000000000)
  centralHi := (356985098379903944981/100000000000000000000)
  directionLo := (72093592460629242077/20000000000000000000)
  directionHi := (180233981151573105193/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree053.table
  base := (5210028934388091977416505205710069791239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-167848180615996016573484780658797000000000000)
      constant := (2295877827295475251001059369559269783054025278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree053.table
  base := (10419862161210349766655679397435153343281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-198317227036108111204700176691436097000000000000)
      constant := (2718820338202705589652266930413113812335652889281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72093592460629242077/20000000000000000000)
  centralHi := (180233981151573105193/50000000000000000000)
  directionLo := (177694089396780907/48828125000000000)
  directionHi := (363917495084607297537/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree054.table
  base := (5835839575994495149116327288443162339937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-19001497830074427556812030588133000000000000)
      constant := (265056644010970274542297698852052147832483586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree054.table
  base := (233430205675594062241553411331375199291/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-202057120121131820178241649741247997000000000000)
      constant := (2824952280696078370882192724175043860120070264550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177694089396780907/48828125000000000)
  centralHi := (363917495084607297537/100000000000000000000)
  directionLo := (367334635734677101989/100000000000000000000)
  directionHi := (36733463573467710199/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree055.table
  base := (12963395862167931659205667818052633495901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-174178780325343679449131769927597000000000000)
      constant := (2476859735386381933772054814517964899722838501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree055.table
  base := (12963250202529800768158118281237084816477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-205797013206155529151783122791059897000000000000)
      constant := (2933118206548606247758865490179756174534403298477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367334635734677101989/100000000000000000000)
  centralHi := (36733463573467710199/10000000000000000000)
  directionLo := (9268006999619735361/2500000000000000000)
  directionHi := (370720279984789414441/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree056.table
  base := (14295176313023791135433996543299771725881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-177344080180017510886955264561997000000000000)
      constant := (2569927562742385386512256686715954706259016481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree056.table
  base := (893440669612244612843499001809483208467/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-209536906291179238125324595840871797000000000000)
      constant := (3043318020089821957720012714946922819226288487472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268006999619735361/2500000000000000000)
  centralHi := (370720279984789414441/100000000000000000000)
  directionLo := (46759410378699673921/12500000000000000000)
  directionHi := (374075283029597391369/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree057.table
  base := (7833496832505748620469458883721343763171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-20056597781632371369419862132933000000000000)
      constant := (296079245373009566462917138641996936695112838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree057.table
  base := (1958360674748099674806595196562084469073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-213276799376202947098866068890683697000000000000)
      constant := (3155551640317226192536981912714733228104098296584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46759410378699673921/12500000000000000000)
  centralHi := (374075283029597391369/100000000000000000000)
  directionLo := (4717505775621566033/1250000000000000000)
  directionHi := (377400462049725282641/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree058.table
  base := (17078825184027012192849046305847991310971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-183674679889365173762602253830797000000000000)
      constant := (2761216613099079466460799024838786625399835571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree058.table
  base := (2134841485768624112872620173393959360671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-217016692461226656072407541940495597000000000000)
      constant := (3269818998647603675059664836552905610850213173368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4717505775621566033/1250000000000000000)
  centralHi := (377400462049725282641/100000000000000000000)
  directionLo := (380696598536181923247/100000000000000000000)
  directionHi := (23793537408511370203/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree059.table
  base := (9265325806741342621212119431402139463563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-186839979744039005200425748465197000000000000)
      constant := (2859437726881981011798417905186251929489454726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree059.table
  base := (18530571238996619029007811016475305061891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-220756585546250365045949014990307497000000000000)
      constant := (3386120037013066557960817076037218106045062867891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380696598536181923247/100000000000000000000)
  centralHi := (23793537408511370203/6250000000000000000)
  directionLo := (383964440435167917447/100000000000000000000)
  directionHi := (47995555054395989681/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree060.table
  base := (10011228321210305894303747067800085437767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-21111697733190315182027693677733000000000000)
      constant := (328819611920109913812417958714668449383029326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree060.table
  base := (20022387421100278537451673605236621464813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-224496478631274074019490488040119397000000000000)
      constant := (3504454706248978405878017093487895781647738122813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383964440435167917447/100000000000000000000)
  centralHi := (47995555054395989681/12500000000000000000)
  directionLo := (193602352064976441253/50000000000000000000)
  directionHi := (387204704129952882507/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree061.table
  base := (336784788358994182562679773711545791089/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-193170579453386668076072737733997000000000000)
      constant := (3061032918361038812053475810092060758567839296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree061.table
  base := (5388541713927757260548006762288850770491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-228236371716297782993031961089931297000000000000)
      constant := (3624822964729013384706476982012693375754704705964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193602352064976441253/50000000000000000000)
  centralHi := (387204704129952882507/100000000000000000000)
  directionLo := (78083615254939903431/20000000000000000000)
  directionHi := (97604519068674879289/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree062.table
  base := (23125949348746042032141307002296805855453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-196335879308060499513896232368397000000000000)
      constant := (3164406929684182977001777043583937992030033253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree062.table
  base := (11562949023910312208992573706699128614091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-231976264801321491966573434139743197000000000000)
      constant := (3747224777209464716817953358783687771559863240182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78083615254939903431/20000000000000000000)
  centralHi := (97604519068674879289/25000000000000000000)
  directionLo := (393605215493532083847/100000000000000000000)
  directionHi := (49200651936691510481/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree063.table
  base := (6184403852883276524756558009876952183761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-22166797684748258994635525222533000000000000)
      constant := (363277612829865863744400847245571756724427716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree063.table
  base := (49475142530019045200204097491938840877/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-235716157886345200940114907189555097000000000000)
      constant := (3871660113850724353822445088143074006283861438500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393605215493532083847/100000000000000000000)
  centralHi := (49200651936691510481/12500000000000000000)
  directionLo := (396766753956758035687/100000000000000000000)
  directionHi := (49595844244594754461/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree064.table
  base := (13194608123761039103254730820892464957697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-202666479017408162389543221637197000000000000)
      constant := (3376307653877354059042081668784490602709939794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree064.table
  base := (2638917826722205267522921637255083020983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-239456050971368909913656380239366997000000000000)
      constant := (3998128949388773368644062020785878225974168989830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396766753956758035687/100000000000000000000)
  centralHi := (49595844244594754461/12500000000000000000)
  directionLo := (79980659768985478793/20000000000000000000)
  directionHi := (199951649422463696983/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree065.table
  base := (14040372372671542730153916180035532715377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-205831778872081993827366716271597000000000000)
      constant := (3484834326413193793631168666175974841185391154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree065.table
  base := (28080712077968155711397603546725687423131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-243195944056392618887197853289178897000000000000)
      constant := (4126631262433686264107328127418539778115007069131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79980659768985478793/20000000000000000000)
  centralHi := (199951649422463696983/50000000000000000000)
  directionLo := (201507716855166645209/50000000000000000000)
  directionHi := (403015433710333290419/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree066.table
  base := (29812194881606506190188476260430436452821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-23221897636306202807243356767333000000000000)
      constant := (399453168601052841278065880876492396134865269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree066.table
  base := (7453041697650238015980821951464382873267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-246935837141416327860739326338990797000000000000)
      constant := (4257167034875677800574762857086692811915277981068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201507716855166645209/50000000000000000000)
  centralHi := (403015433710333290419/100000000000000000000)
  directionLo := (203051859872300102203/50000000000000000000)
  directionHi := (406103719744600204407/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree067.table
  base := (15791780777243619480911363909353936947171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-212162378581429656703013705540397000000000000)
      constant := (3707040213596352303825665594893533179999183542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree067.table
  base := (6316707480858591416285689281686928563361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-250675730226440036834280799388802697000000000000)
      constant := (4389736251382205909277757153887039653560966946805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203051859872300102203/50000000000000000000)
  centralHi := (406103719744600204407/100000000000000000000)
  directionLo := (409168696960157895569/100000000000000000000)
  directionHi := (40916869696015789557/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree068.table
  base := (33394840442762037416155663868178280388373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10741967832603500354604619800000000000000)
      linear := (-745078472097243903601512803373000000000000)
      constant := (13220482365862707013219670629877604523495357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree068.table
  base := (33394819685158089004374030640113081624957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12662392970676726140222267939800000000000000)
      linear := (-880330876510255175805613399441573000000000000)
      constant := (15655151899557687299845960328451048682959168813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409168696960157895569/100000000000000000000)
  centralHi := (40916869696015789557/10000000000000000000)
  directionLo := (206105442646322579027/50000000000000000000)
  directionHi := (82442177058529031611/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree069.table
  base := (35246027886406990027788741769988154393403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-24276997587864146619851188312133000000000000)
      constant := (437346230922629271845498774434228576619693467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree069.table
  base := (17623005024332283398403430553710305505887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-258155516396487454781363745488426497000000000000)
      constant := (4660974966655396936519925516219067787532710095774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206105442646322579027/50000000000000000000)
  centralHi := (82442177058529031611/20000000000000000000)
  directionLo := (415230785630616511313/100000000000000000000)
  directionHi := (207615392815308255657/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree070.table
  base := (2321070049091101282789779987770144510779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-221658278145451151016484189443597000000000000)
      constant := (4053230229241368060408983730560582333960578864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree070.table
  base := (9284276365018688427857985409682689546903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-261895409481511163754905218538238397000000000000)
      constant := (4799644445127373200866242892219980870833976579612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415230785630616511313/100000000000000000000)
  centralHi := (207615392815308255657/50000000000000000000)
  directionLo := (41822888077832662109/10000000000000000000)
  directionHi := (418228880778326621091/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree071.table
  base := (19534058257169209953263371449345096175411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-224823578000124982454307684077997000000000000)
      constant := (4172061849718314269309521370668655190304488022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree071.table
  base := (7813620670029673378692969166966150067157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-265635302566534872728446691588050297000000000000)
      constant := (4940347326510807146221382756800679558610267145785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41822888077832662109/10000000000000000000)
  centralHi := (418228880778326621091/100000000000000000000)
  directionLo := (421205636356832815129/100000000000000000000)
  directionHi := (42120563635683281513/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree072.table
  base := (8207802569859164370146816497859630754473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-25332097539422090432459019856933000000000000)
      constant := (476956770438946560811743666501983166440213485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree072.table
  base := (10259750385942283041474939077061553434083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-269375195651558581701988164637862197000000000000)
      constant := (5083083604136790100842371096845350033561807648332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421205636356832815129/100000000000000000000)
  centralHi := (42120563635683281513/10000000000000000000)
  directionLo := (424161501648177897187/100000000000000000000)
  directionHi := (106040375412044474297/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree073.table
  base := (8609961581386099375313164949396220325019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-231154177709472645329954673346797000000000000)
      constant := (4414877477039260738418216969478503845326872095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree073.table
  base := (68879677119221880326729479690976179453/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-273115088736582290675529637687674097000000000000)
      constant := (5227853272359516157626822313682253210486923408125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424161501648177897187/100000000000000000000)
  centralHi := (106040375412044474297/25000000000000000000)
  directionLo := (213548455193493474363/50000000000000000000)
  directionHi := (427096910386986948727/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree074.table
  base := (9020100018426271955099843037347113027601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-234319477564146476767778167981197000000000000)
      constant := (4538861474835655410019725599135127204923951005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree074.table
  base := (11275122939621290469587619370238828468483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-276854981821605999649071110737485997000000000000)
      constant := (5374656326399406064235221486055282513792789385932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213548455193493474363/50000000000000000000)
  centralHi := (427096910386986948727/100000000000000000000)
  directionLo := (86002456300685435563/20000000000000000000)
  directionHi := (53751535187928397227/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree075.table
  base := (1474721501686666374926524669144946870043/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-26387197490980034245066851401733000000000000)
      constant := (518284769313994101332662977177102468654157664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree075.table
  base := (47191080900991361608617780650468971925909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-280594874906629708622612583787297897000000000000)
      constant := (5523492762210282122017929901385731574643808919909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86002456300685435563/20000000000000000000)
  centralHi := (53751535187928397227/12500000000000000000)
  directionLo := (432908019821134104309/100000000000000000000)
  directionHi := (43290801982113410431/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree076.table
  base := (49321570648360765844804095187368580416149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-240650077273494139643425157249997000000000000)
      constant := (4791981821034342527101895169585617677662403549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree076.table
  base := (49321564509864545837023535679716916690999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-284334767991653417596154056837109797000000000000)
      constant := (5674362576366906958048439142072294093291519624999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432908019821134104309/100000000000000000000)
  centralHi := (43290801982113410431/10000000000000000000)
  directionLo := (435784516713396068901/100000000000000000000)
  directionHi := (217892258356698034451/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree077.table
  base := (51491946906384953799526802703159703158919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-243815377128167971081248651884397000000000000)
      constant := (4921118163940710644666653628280212387916348319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree077.table
  base := (51491941639404992648238141031082658441427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-288074661076677126569695529886921697000000000000)
      constant := (5827265765969764279234626734471036374614073623427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435784516713396068901/100000000000000000000)
  centralHi := (217892258356698034451/50000000000000000000)
  directionLo := (219321075360304188947/50000000000000000000)
  directionHi := (87728430144121675579/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree078.table
  base := (53702216007521498595184154039148012940397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-27442297442537978057674682946533000000000000)
      constant := (561330216712318592022858929702837775739774733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree078.table
  base := (10740442297817193042682563154046988815473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-291814554161700835543237002936733597000000000000)
      constant := (5982202328564438309932505487388517862276145167365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219321075360304188947/50000000000000000000)
  centralHi := (87728430144121675579/20000000000000000000)
  directionLo := (441481288131754974921/100000000000000000000)
  directionHi := (220740644065877487461/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree079.table
  base := (55952377256927545373762694517932955318431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-250145976837515633956895641153197000000000000)
      constant := (5184543178637526312233432391105681616783239031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree079.table
  base := (55952373381290198672894387769301033185753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-295554447246724544516778475986545497000000000000)
      constant := (6139172262073353838465113915427508606298551883753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441481288131754974921/100000000000000000000)
  centralHi := (220740644065877487461/50000000000000000000)
  directionLo := (88860456706489280851/20000000000000000000)
  directionHi := (13884446360388950133/3125000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree080.table
  base := (29121215033105825843294183909621690486161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-253311276692189465394719135787597000000000000)
      constant := (5318831847090281454940758479131612033909009522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree080.table
  base := (29121213371229917866508647984749850054391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-299294340331748253490319949036357397000000000000)
      constant := (6298175564737981900812216114716224310033225720782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88860456706489280851/20000000000000000000)
  centralHi := (13884446360388950133/3125000000000000000)
  directionLo := (447105480321835391429/100000000000000000000)
  directionHi := (44710548032183539143/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree081.table
  base := (60572373937145200827733485332140648927719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-28497397394095921870282514491333000000000000)
      constant := (606093106052582236030621190369586647540110791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree081.table
  base := (60572371087136501677319679590686707749009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-303034233416771962463861422086169297000000000000)
      constant := (6459212235069906634634765303640881962395169343009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447105480321835391429/100000000000000000000)
  centralHi := (44710548032183539143/10000000000000000000)
  directionLo := (449891211200543318211/100000000000000000000)
  directionHi := (112472802800135829553/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree082.table
  base := (31471104223932718756441418854072849762377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-259641876401537128270366125056397000000000000)
      constant := (5592561499689137293743425234174290964463885154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree082.table
  base := (7867775750556054322303777314653577926791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-306774126501795671437402895135981197000000000000)
      constant := (6622282271809394806991679087355629343116953062328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449891211200543318211/100000000000000000000)
  centralHi := (112472802800135829553/25000000000000000000)
  directionLo := (14145618707236255673/3125000000000000000)
  directionHi := (452659798631560181537/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree083.table
  base := (32675966620594512814020458402457812120411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-262807176256210959708189619690797000000000000)
      constant := (5732002481808939106111759724997411538650378022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree083.table
  base := (32675965573334756488783952132778515958609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-310514019586819380410944368185793097000000000000)
      constant := (6787385673890317781764213435068837207665222305218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14145618707236255673/3125000000000000000)
  centralHi := (452659798631560181537/100000000000000000000)
  directionLo := (455411555275925505339/100000000000000000000)
  directionHi := (22770577763796275267/5000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree084.table
  base := (8475193501839164495265232371340779556551/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-29552497345653865682890346036133000000000000)
      constant := (652573433338455141198062206048611882334745912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree084.table
  base := (33900773109766268275709384141618176835329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-314253912671843089384485841235604997000000000000)
      constant := (6954522440410452028493887395884769516590591098658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455411555275925505339/100000000000000000000)
  centralHi := (22770577763796275267/5000000000000000000)
  directionLo := (229073392202428265323/50000000000000000000)
  directionHi := (458146784404856530647/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree085.table
  base := (7029105251243188515975227007330474647711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (702)
      previous := (351)
      next := (351)
      square := (10741967832603500354604619800000000000000)
      linear := (-931272581195704576414659546573000000000000)
      constant := (20816736172092512389648786935489742718293990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree085.table
  base := (70291050974027811661271900911850858640071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12662392970676726140222267939800000000000000)
      linear := (-1100324587394002762484523578842273000000000000)
      constant := (24649455261613610994722213432802124509312513239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229073392202428265323/50000000000000000000)
  centralHi := (458146784404856530647/100000000000000000000)
  directionLo := (460865780289861432383/100000000000000000000)
  directionHi := (7201027817029084881/1562500000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree086.table
  base := (72820446517632729055504771597342344700531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-272303075820232454021660103593997000000000000)
      constant := (6160630042311190612755301823236179438566081131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree086.table
  base := (4551277824966207800453140365152547581329/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-321733698841890507331568787335228797000000000000)
      constant := (7294896063831968240620073739133643596090436725264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460865780289861432383/100000000000000000000)
  centralHi := (7201027817029084881/1562500000000000000)
  directionLo := (7243262946441531999/1562500000000000000)
  directionHi := (463568828572258047937/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree087.table
  base := (7538972984688291901558813145722702406043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-30607597297211809495498177580933000000000000)
      constant := (700771196144261202205164006269084609953464270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree087.table
  base := (37694864358782848658711139879265976614729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-325473591926914216305110260385040697000000000000)
      constant := (7468132919540806452660428844626425422383471457458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7243262946441531999/1562500000000000000)
  centralHi := (463568828572258047937/100000000000000000000)
  directionLo := (93251241322682307487/20000000000000000000)
  directionHi := (116564051653352884359/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree088.table
  base := (77998902344933537215831823331549818721651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-278633675529580116897307092862797000000000000)
      constant := (6454968922292414266621354584951297078495014251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree088.table
  base := (77998901377542673073540111295474476334493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-329213485011937925278651733434852597000000000000)
      constant := (7643403137270482213532980845386251325916031872493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93251241322682307487/20000000000000000000)
  centralHi := (116564051653352884359/25000000000000000000)
  directionLo := (117232045956726633819/25000000000000000000)
  directionHi := (468928183826906535277/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree089.table
  base := (80647963880404124600046883143345952114541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-281798975384253948335130587497197000000000000)
      constant := (6604714512951660379074789913260600821449921141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree089.table
  base := (3225918522073156726111715303615568797407/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-332953378096961634252193206484664497000000000000)
      constant := (7820706716629892345869057728394676090460466485175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117232045956726633819/25000000000000000000)
  centralHi := (468928183826906535277/100000000000000000000)
  directionLo := (117896255498444952483/25000000000000000000)
  directionHi := (471585021993779809933/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree090.table
  base := (41668457171063702762533529752261361010953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-31662697248769753308106009125733000000000000)
      constant := (750686392998549230362100735721027066664330834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree090.table
  base := (8333691363253810161550736807849571997209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-336693271181985343225734679534476397000000000000)
      constant := (8000043657288257251121290444396857248430147912090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117896255498444952483/25000000000000000000)
  centralHi := (471585021993779809933/100000000000000000000)
  directionLo := (237113487780928716109/50000000000000000000)
  directionHi := (474226975561857432219/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree091.table
  base := (86065753636053290386527869969508127288729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-288129575093601611210777576765997000000000000)
      constant := (6909357994153638066112752690796292639077984129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree091.table
  base := (17213150605687633693380937572358973426343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-340433164267009052199276152584288297000000000000)
      constant := (8181413958965859357443631952846649632670705321715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237113487780928716109/50000000000000000000)
  centralHi := (474226975561857432219/100000000000000000000)
  directionLo := (476854291930165252047/100000000000000000000)
  directionHi := (29803393245635328253/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree092.table
  base := (88834481682626605474568492883609983308727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-291294874948275442648601071400397000000000000)
      constant := (7064255884244822350816980124057893566585998927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree092.table
  base := (17766896232478781414862669484347744601369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-344173057352032761172817625634100197000000000000)
      constant := (8364817621426202028835099818878690745477709776845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476854291930165252047/100000000000000000000)
  centralHi := (29803393245635328253/6250000000000000000)
  directionLo := (479467211719312465231/100000000000000000000)
  directionHi := (29966700732457029077/6250000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree093.table
  base := (3665723936582643381774373518941014305109/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-32717797200327697120713840670533000000000000)
      constant := (802319023009499705985420795219242828354412525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree093.table
  base := (45821548984600887846229874161269841864683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-347912950437056470146359098683912097000000000000)
      constant := (8550254644469371141101143444415257357603919885366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479467211719312465231/100000000000000000000)
  centralHi := (29966700732457029077/6250000000000000000)
  directionLo := (482065969028684645421/100000000000000000000)
  directionHi := (241032984514342322711/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree094.table
  base := (4724580188749162023410675307198626540559/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-297625474657623105524248060669197000000000000)
      constant := (7379203962527696120249060164995340552639879180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree094.table
  base := (23622900848439210815089763531373778586473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-351652843522080179119900571733723997000000000000)
      constant := (8737725027926414920503852259950450751579619217892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482065969028684645421/100000000000000000000)
  centralHi := (241032984514342322711/50000000000000000000)
  directionLo := (242325395840612155061/50000000000000000000)
  directionHi := (484650791681224310123/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree095.table
  base := (97379997715789123961062080626559595877337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-300790774512296936962071555303597000000000000)
      constant := (7539254150446339292867334895609771508876953537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree095.table
  base := (9737999738950092057404946110446401022979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-355392736607103888093442044783535897000000000000)
      constant := (8927228771654585912385690171298118881078546369790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242325395840612155061/50000000000000000000)
  centralHi := (484650791681224310123/100000000000000000000)
  directionLo := (121805475364130855987/25000000000000000000)
  directionHi := (487221901456523423949/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree096.table
  base := (12538535024543116127586415705533709365029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (22542)
      previous := (11271)
      next := (11271)
      square := (344936522624712400275637235800000000000000)
      linear := (-33772897151885640933321672215333000000000000)
      constant := (855669085637302815256872602451161936051947048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree096.table
  base := (100308279917108765258816307874465533945731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-359132629692127597066983517833347797000000000000)
      constant := (9118765875533312884300539651937249113543145191731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121805475364130855987/25000000000000000000)
  centralHi := (487221901456523423949/100000000000000000000)
  directionLo := (489779514312902802653/100000000000000000000)
  directionHi := (244889757156451401327/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree097.table
  base := (10327645118231914102429688567477062485207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-307121374221644599837718544572397000000000000)
      constant := (7864506823306557984048701615633812395240234070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree097.table
  base := (12909556367921981796792487473243763814877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-362872522777151306040524990883159697000000000000)
      constant := (9312336339460790735708857577752627802551413575016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell095.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489779514312902802653/100000000000000000000)
  centralHi := (244889757156451401327/50000000000000000000)
  directionLo := (492323840599107794723/100000000000000000000)
  directionHi := (123080960149776948681/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree098.table
  base := (106284510644719629409087954526336474868861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (202878)
      previous := (101439)
      next := (101439)
      square := (3104428703622411602480735122200000000000000)
      linear := (-310286674076318431275542039206797000000000000)
      constant := (8029709308083428701484060589425157171133907461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree098.table
  base := (106284510440276815475963207232532949112541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3659431568525573854524235434602200000000000000)
      linear := (-366612415862175015014066463932971597000000000000)
      constant := (9507940163351093646669953051314049573011999818541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell095.Kernel098
