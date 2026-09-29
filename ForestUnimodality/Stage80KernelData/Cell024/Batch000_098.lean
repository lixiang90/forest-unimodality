import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell024.Parameters
import ForestUnimodality.BinomialMassData.Q22_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q67_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q67_153.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree000.table
  base := (2106072434263015618171266363/100000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1421)
      previous := (1078)
      next := (0)
      square := (45212605631620760293643002080000000000000)
      linear := (157156412960332091399706657900000000000000)
      constant := (10740969414741379652673458451300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree000.table
  base := (2106072434263015618171266363/100000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4214)
      previous := (3283)
      next := (0)
      square := (135637816894862280880929006240000000000000)
      linear := (471469238880996274199119973700000000000000)
      constant := (32222908244224138958020375353900000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree001.table
  base := (134693671639558149466574634542468110555769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (6025622413185623208464747461380000000000000)
      constant := (347309875342024312280828317441879555555555169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree001.table
  base := (417383603324146195988331214542435067709/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (53959326084880884314420869139940000000000000)
      constant := (3098961643281015184527026812434855999999993920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49526788001235641567/100000000000000000000)
  directionHi := (1547712125038613799/3125000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree002.table
  base := (87636658308184396735827803135126991755307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (4036267765394309755544455369860000000000000)
      constant := (222744372059976490004545980889745305555553507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree002.table
  base := (86254893238597254818552713163352246999017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (35783858620969338676376382303780000000000000)
      constant := (1971882301081316350478007675089592749999988953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/100000000000000000000)
  centralHi := (1547712125038613799/3125000000000000000)
  directionLo := (2188795477878891139/3125000000000000000)
  directionHi := (70041455292124516449/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree003.table
  base := (28336276692550156382503852320284435963/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (682304372534332100874721092780000000000000)
      constant := (48144134668574447051666132179894169046878208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree003.table
  base := (56752618588516796388884677420026779706999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (1956487906339754782036877274180000000000000)
      constant := (141063677097651615577006022171309654017904399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2188795477878891139/3125000000000000000)
  centralHi := (70041455292124516449/100000000000000000000)
  directionLo := (5361432072114548443/6250000000000000000)
  directionHi := (85782913153832775089/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree004.table
  base := (19522954222138499391757113166026016827927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (57558469811682849703871186820000000000000)
      constant := (94593867405629194257726148325987339538876254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree004.table
  base := (7595575196170572415516943565132527630931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-567076306853752599712591368540000000000000)
      constant := (826343875891864499581573663127256696562318895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5361432072114548443/6250000000000000000)
  centralHi := (85782913153832775089/100000000000000000000)
  directionLo := (49526788001235641567/50000000000000000000)
  directionHi := (19810715200494256627/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree005.table
  base := (13285132085460193366523483421861732141901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-1931796177979630603216420904700000000000000)
      constant := (62548963999449184065218415159524730602169002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree005.table
  base := (25721896375911612454206202940765468368983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-18742543770765298237757078204700000000000000)
      constant := (543671572670123141416240870478878849049523047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/50000000000000000000)
  centralHi := (19810715200494256627/20000000000000000000)
  directionLo := (55372632338991916439/50000000000000000000)
  directionHi := (110745264677983832879/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree006.table
  base := (906996775164002669647273511297090854733/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-1307050275256981352045570998740000000000000)
      constant := (13961359823019652618831503386931555421070220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree006.table
  base := (17481599898201323271000374036341385872331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-4102001248297427097311285004540000000000000)
      constant := (40329065267583854753500569834403944653932931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55372632338991916439/50000000000000000000)
  centralHi := (110745264677983832879/100000000000000000000)
  directionLo := (6065767960101184149/5000000000000000000)
  directionHi := (121315359202023682981/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree007.table
  base := (12259498657652601902350133323541594134689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-5910505473562257509057005087740000000000000)
      constant := (28709616553045980396458605523211686344326089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree007.table
  base := (11753195348745147592695122198413266151769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-55093478698588389513846051877020000000000000)
      constant := (249011671929410143769581639652236147346760521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6065767960101184149/5000000000000000000)
  centralHi := (121315359202023682981/100000000000000000000)
  directionLo := (65517782143543616389/50000000000000000000)
  directionHi := (131035564287087232779/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree008.table
  base := (8015202313517690517162387875073917402807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-7899860121353570961977297179260000000000000)
      constant := (20648908066736842808710325198747259164701007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree008.table
  base := (1525190646810075255214824997489402705889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-73268946162499935151890538713180000000000000)
      constant := (180502559520418666046919511919627139710778005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65517782143543616389/50000000000000000000)
  centralHi := (131035564287087232779/100000000000000000000)
  directionLo := (2188795477878891139/1562500000000000000)
  directionHi := (140082910584249032897/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree009.table
  base := (4843380096202652387059866380240832800241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-3296404923048294804965863090260000000000000)
      constant := (5411952589869312871853730439708802037808947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree009.table
  base := (2271335219990365941174159288297454536011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-10160490402934608976659447283260000000000000)
      constant := (16043409164718237894322838909903358496329222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2188795477878891139/1562500000000000000)
  centralHi := (140082910584249032897/100000000000000000000)
  directionLo := (148580364003706924701/100000000000000000000)
  directionHi := (74290182001853462351/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree010.table
  base := (478451941484392892905741540524934953907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-11878569416936197867817881362300000000000000)
      constant := (14555505913818622370427651068526779075560535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree010.table
  base := (1079083412491814802992412647113002538931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-109619881090323026427979512385500000000000000)
      constant := (132595718881942111062820621045536552867671558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148580364003706924701/100000000000000000000)
  centralHi := (74290182001853462351/50000000000000000000)
  directionLo := (156617455276202809203/100000000000000000000)
  directionHi := (39154363819050702301/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree011.table
  base := (439252794080173489707520851260184082051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-13867924064727511320738173453820000000000000)
      constant := (15028900192967620144410226479447738797414651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree011.table
  base := (63854391320810552467419045552131088351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-127795348554234572066023999221660000000000000)
      constant := (140037334619084236295063825147939346588834236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156617455276202809203/100000000000000000000)
  centralHi := (39154363819050702301/25000000000000000000)
  directionLo := (32852354574314898487/20000000000000000000)
  directionHi := (41065443217893623109/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree012.table
  base := (-231750809785371397451539182242296287763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-5285759570839608257886155181780000000000000)
      constant := (5761267546793024343812886344339645592547395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree012.table
  base := (-1304378055813031412415178635457184151913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-16218979557571790856007609561980000000000000)
      constant := (18162927079648157493943892549895864020874287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32852354574314898487/20000000000000000000)
  centralHi := (41065443217893623109/25000000000000000000)
  directionLo := (171565826307665550177/100000000000000000000)
  directionHi := (85782913153832775089/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree013.table
  base := (-1247717814142352677957646503193625333997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-17846633360310138226578757636860000000000000)
      constant := (21076565083863791640297689282666761012547606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree013.table
  base := (-81615561148197451424863479547488189017/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-164146283482057663342112972893980000000000000)
      constant := (200764748582494944246865834249311167465633504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171565826307665550177/100000000000000000000)
  centralHi := (85782913153832775089/50000000000000000000)
  directionLo := (89285686823744884191/50000000000000000000)
  directionHi := (178571373647489768383/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree014.table
  base := (-726660438368733771307795948392465829747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-19835988008101451679499049728380000000000000)
      constant := (26244598368763152849035399319075981884140265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree014.table
  base := (-3726737906402483237463135030472874546813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-182321750945969208980157459730140000000000000)
      constant := (250523426461938710181726103840580479733654483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89285686823744884191/50000000000000000000)
  centralHi := (178571373647489768383/100000000000000000000)
  directionLo := (7412490886720413853/4000000000000000000)
  directionHi := (92656136084005173163/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree015.table
  base := (-4614913126050970358275470112100180748761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-7275114218630921710806447273300000000000000)
      constant := (10892401843642643325000395347809143290824213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree015.table
  base := (-4690398641420915819450345194317993732007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-22277468712208972735355771840700000000000000)
      constant := (34642770223494904667140978781078898303049793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7412490886720413853/4000000000000000000)
  centralHi := (92656136084005173163/50000000000000000000)
  directionLo := (191816425119930959311/100000000000000000000)
  directionHi := (11988526569995684957/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree016.table
  base := (-2734915571457854018232156762862814964621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-23814697303684078585339633911420000000000000)
      constant := (40297493956422458664136881443107636554041558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree016.table
  base := (-5531054808820001264085025514134211985617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-218672685873792300256246433402460000000000000)
      constant := (383885043118894227551691529899952231628691647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191816425119930959311/100000000000000000000)
  centralHi := (11988526569995684957/6250000000000000000)
  directionLo := (49526788001235641567/25000000000000000000)
  directionHi := (198107152004942566269/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree017.table
  base := (-6218990045081185150759334089929206647163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4263)
      previous := (3234)
      next := (0)
      square := (135637816894862280880929006240000000000000)
      linear := (-1517885408910317178721172117820000000000000)
      constant := (2885353813210088655181346412680831382984061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree017.table
  base := (-783597914460766335925984911153051205027/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (37926)
      previous := (29547)
      next := (0)
      square := (1220740352053760527928361056160000000000000)
      linear := (-13932244313982579170252407072860000000000000)
      constant := (27432575262721978658152790759877987925422568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/25000000000000000000)
  centralHi := (198107152004942566269/100000000000000000000)
  directionLo := (204204178226667923803/100000000000000000000)
  directionHi := (51051044556666980951/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree018.table
  base := (-3438739592238163489500102002432957193021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-9264468866422235163726739364820000000000000)
      constant := (19632840243669313583059407122741252227301586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree018.table
  base := (-1729511929136014296812159925602546572451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-28335957866846154614703934119420000000000000)
      constant := (62094729300635825071987813778551105460219796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204204178226667923803/100000000000000000000)
  centralHi := (51051044556666980951/25000000000000000000)
  directionLo := (6566386433636673417/3125000000000000000)
  directionHi := (42024873175274709869/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree019.table
  base := (-3728174455814314264359523933580654609303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-29782761247058018944100510185980000000000000)
      constant := (69811269714009744982831822425233434722405794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree019.table
  base := (-936179233540962215952730355723336624457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-273199088265526937170379893910940000000000000)
      constant := (661133591512274530718953897787199303664688696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6566386433636673417/3125000000000000000)
  centralHi := (42024873175274709869/20000000000000000000)
  directionLo := (1349264149347180907/625000000000000000)
  directionHi := (215882263895548945121/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree020.table
  base := (-3981901638803294950033872185077681676709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-31772115894849332397020802277500000000000000)
      constant := (81767923036747751078548655705225899917759782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree020.table
  base := (-7990794767974245315326006943159257283321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-291374555729438482808424380747100000000000000)
      constant := (773013032080627201305641651157584946254738711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1349264149347180907/625000000000000000)
  centralHi := (215882263895548945121/100000000000000000000)
  directionLo := (221490529355967665757/100000000000000000000)
  directionHi := (110745264677983832879/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree021.table
  base := (-8406003687847915961765979759374982237111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-11253823514213548616647031456340000000000000)
      constant := (31584151627892829557596272427861890400424763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree021.table
  base := (-2107005409644730721343687197986907647629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-34394447021483336494052096398140000000000000)
      constant := (99372553085482707080246647611924212834067884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221490529355967665757/100000000000000000000)
  centralHi := (110745264677983832879/50000000000000000000)
  directionLo := (226960254943692978381/100000000000000000000)
  directionHi := (113480127471846489191/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree022.table
  base := (-1098452680253258038770162964535007417883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-35750825190431959302861386460540000000000000)
      constant := (108752715204351294557452330438835565648690536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree022.table
  base := (-2201393578307357858734973440055604212269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-327725490657261574084513354419420000000000000)
      constant := (1025049028345676025325893169795233443979979916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226960254943692978381/100000000000000000000)
  centralHi := (113480127471846489191/50000000000000000000)
  directionLo := (232301226974429585661/100000000000000000000)
  directionHi := (116150613487214792831/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree023.table
  base := (-9112225202163182525295816980387474381327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-37740179838223272755781678552060000000000000)
      constant := (123759421908846562876849691147492179134168473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree023.table
  base := (-9126853525067566124792451844618960120247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-345900958121173119722557841255580000000000000)
      constant := (1165021576047505903198173102010094762545137977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232301226974429585661/100000000000000000000)
  centralHi := (116150613487214792831/50000000000000000000)
  directionLo := (237522131144752047219/100000000000000000000)
  directionHi := (11876106557237602361/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree024.table
  base := (-9382557805998566067584460375058287261489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-13243178162004862069567323547860000000000000)
      constant := (46588480292068128712813879442664464944289037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree024.table
  base := (-2348616795288576957270566986330504748083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-40452936176120518373400258676860000000000000)
      constant := (146023285819827055117342878431497428600944468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237522131144752047219/100000000000000000000)
  centralHi := (11876106557237602361/5000000000000000000)
  directionLo := (6065767960101184149/2500000000000000000)
  directionHi := (242630718404047365961/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree025.table
  base := (-960073739414776548703513991078608056997/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-41718889133805899661622262735100000000000000)
      constant := (156765262822683717361657608447045404437508030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree025.table
  base := (-9610424028900834383458828605174733579461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-382251893048996210998646814927900000000000000)
      constant := (1472565994570340541944912750933964661638397451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6065767960101184149/2500000000000000000)
  centralHi := (242630718404047365961/100000000000000000000)
  directionLo := (49526788001235641567/20000000000000000000)
  directionHi := (61908485001544551959/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree026.table
  base := (-1953681145321196750413651974902439988997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-43708243781597213114542554826620000000000000)
      constant := (174754617530537033625636129954313767943094015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree026.table
  base := (-9776276565976288618388876171089180028163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-400427360512907756636691301764060000000000000)
      constant := (1640054500205260076346257665562693384720732333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/20000000000000000000)
  centralHi := (61908485001544551959/25000000000000000000)
  directionLo := (63134514615968383267/25000000000000000000)
  directionHi := (252538058463873533069/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree027.table
  base := (-9886838944767244261701745333434093309543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-15232532809796175522487615639380000000000000)
      constant := (64576728585332826689843859916672641100626219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree027.table
  base := (-9893227782861199120381586072115353874447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-46511425330757700252748420955580000000000000)
      constant := (201849658719893711730947484683447964572563353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63134514615968383267/25000000000000000000)
  centralHi := (252538058463873533069/100000000000000000000)
  directionLo := (128674369730749162633/50000000000000000000)
  directionHi := (257348739461498325267/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree028.table
  base := (-9957031159927313892315454430031427013641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-47686953077179840020383139009660000000000000)
      constant := (213689381815587767047879946805568258337519759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree028.table
  base := (-9962211686364487690052443162280806963817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-436778295440730847912780275436380000000000000)
      constant := (2002321415226300479211113955751048589784007847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128674369730749162633/50000000000000000000)
  centralHi := (257348739461498325267/100000000000000000000)
  directionLo := (262071128574174465557/100000000000000000000)
  directionHi := (131035564287087232779/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree029.table
  base := (-4989879037569204252954681830082100768171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-49676307724971153473303431101180000000000000)
      constant := (234630188105666081103619292255232911803974458) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree029.table
  base := (-9983954529653191788123554208375273144457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-454953762904642393550824762272540000000000000)
      constant := (2197060959586644117325973649058963230961406087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262071128574174465557/100000000000000000000)
  centralHi := (131035564287087232779/50000000000000000000)
  directionLo := (133354957877332801061/50000000000000000000)
  directionHi := (266709915754665602123/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree030.table
  base := (-9955625741114447265538665682001213119287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-17221887457587488975407907730900000000000000)
      constant := (85517009429442172831214353331704948225578171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree030.table
  base := (-9959021664890746503633058851386972811027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-52569914485394882132096583234300000000000000)
      constant := (266761369692364496435979181246542483718518773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133354957877332801061/50000000000000000000)
  centralHi := (266709915754665602123/100000000000000000000)
  directionLo := (67817347472632399413/25000000000000000000)
  directionHi := (271269389890529597653/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree031.table
  base := (-1977021624235602580471214094398299731487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-53655017020553780379144015284220000000000000)
      constant := (279450669584967041534223051376470111992011565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree031.table
  base := (-9887853570313110945101246595929272850623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-491304697832465484826913735944860000000000000)
      constant := (2613685207005183964233279445217311651839766193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67817347472632399413/25000000000000000000)
  centralHi := (271269389890529597653/100000000000000000000)
  directionLo := (137876742619358668427/50000000000000000000)
  directionHi := (55150697047743467371/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree032.table
  base := (-9768576155504202648502177406488789755231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-55644371668345093832064307375740000000000000)
      constant := (303328147180192222324561567421402657846644169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree032.table
  base := (-76334325451767841278415610323073716703/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-509480165296377030464958222781020000000000000)
      constant := (2835551559979047085703281621431317422809532544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137876742619358668427/50000000000000000000)
  centralHi := (55150697047743467371/20000000000000000000)
  directionLo := (280165821168498065793/100000000000000000000)
  directionHi := (140082910584249032897/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree033.table
  base := (-4803160160662838373167883192589399027577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-19211242105378802428328199822420000000000000)
      constant := (109394235180906637191427807203609982086181482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree033.table
  base := (-960810979848467672975415976272229750597/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-58628403640032064011444745513020000000000000)
      constant := (340716123951039677953301619600379304186972030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280165821168498065793/100000000000000000000)
  centralHi := (140082910584249032897/50000000000000000000)
  directionLo := (56901947270981219953/20000000000000000000)
  directionHi := (142254868177453049883/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree034.table
  base := (-9398568188235875871810588477384925913599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4263)
      previous := (3234)
      next := (0)
      square := (135637816894862280880929006240000000000000)
      linear := (-3507240056701630631641464209340000000000000)
      constant := (20824338397884562946190171024320106335219353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree034.table
  base := (-2350002755435097629271910079209481407527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (37926)
      previous := (29547)
      next := (0)
      square := (1220740352053760527928361056160000000000000)
      linear := (-32107711777894124808296893909020000000000000)
      constant := (194491822386804105459506157924074176407341284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56901947270981219953/20000000000000000000)
  centralHi := (142254868177453049883/50000000000000000000)
  directionLo := (144394159170703227877/50000000000000000000)
  directionHi := (57757663668281291151/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree035.table
  base := (-9145498104925310548348566146082865466043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-61612435611719034190825183650300000000000000)
      constant := (380820824959201179985989604503038466922822157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree035.table
  base := (-9146660492142192705495501150459345809667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-564006567688111667379091683289500000000000000)
      constant := (3555295335509063057249339269614397173941505197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144394159170703227877/50000000000000000000)
  centralHi := (57757663668281291151/20000000000000000000)
  directionLo := (58600885843194164143/20000000000000000000)
  directionHi := (73251107303992705179/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree036.table
  base := (-221181247132762676685769505136758899167/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-21200596753170115881248491913940000000000000)
      constant := (136201186157404618797470407227297201376888440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree036.table
  base := (-442409280299294724290249738416024074859/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-64686892794669245890792907791740000000000000)
      constant := (423693910904405361191871464137278427625834820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58600885843194164143/20000000000000000000)
  centralHi := (73251107303992705179/25000000000000000000)
  directionLo := (148580364003706924701/50000000000000000000)
  directionHi := (297160728007413849403/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree037.table
  base := (-8503933161068241906608596028635079907363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-65591144907301661096665767833340000000000000)
      constant := (437361668151084303686386657614600157160948837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree037.table
  base := (-4252342927275021624589926060106999948223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-600357502615934758655180656961820000000000000)
      constant := (4080208239476085857364364629768890476424095586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148580364003706924701/50000000000000000000)
  centralHi := (297160728007413849403/100000000000000000000)
  directionLo := (301259690299939617539/100000000000000000000)
  directionHi := (15062984514996980877/5000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree038.table
  base := (-8115633915612970754753934233757087608621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-67580499555092974549586059924860000000000000)
      constant := (467094930352951522621160046773277815129976779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree038.table
  base := (-507264934519453972824356016963330969623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-618532970079846304293225143797980000000000000)
      constant := (4356182640300192572612848320879566165313523088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301259690299939617539/100000000000000000000)
  centralHi := (15062984514996980877/5000000000000000000)
  directionLo := (305303625476892873407/100000000000000000000)
  directionHi := (4770369148076451147/1562500000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree039.table
  base := (-7682419598681749954743422066834010255629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-23189951400961429334168784005460000000000000)
      constant := (165934389880349809882969760563694913108369657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree039.table
  base := (-7682905615519953363145381233710469029957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-70745381949306427770141070070460000000000000)
      constant := (515685219922806981260561829889499070053081843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305303625476892873407/100000000000000000000)
  centralHi := (4770369148076451147/1562500000000000000)
  directionLo := (309294691934818386593/100000000000000000000)
  directionHi := (154647345967409193297/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree040.table
  base := (-7204343131770000883465147223677038620261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-71559208850675601455426644107900000000000000)
      constant := (529486248366568433768348446271216022548701139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree040.table
  base := (-7204733289864345825521144039561419320091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-654883905007669395569314117470300000000000000)
      constant := (4935160145835180782992449659453906735135989781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309294691934818386593/100000000000000000000)
  centralHi := (154647345967409193297/50000000000000000000)
  directionLo := (156617455276202809203/50000000000000000000)
  directionHi := (313234910552405618407/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree041.table
  base := (-6681446046076355831995955905789500600777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-73548563498466914908346936199420000000000000)
      constant := (562144058506860892390386663543561508937379023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree041.table
  base := (-3340879529607409789952655309487758650089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-673059372471580941207358604306460000000000000)
      constant := (5238161271793624734261812770529222115520133198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156617455276202809203/50000000000000000000)
  centralHi := (313234910552405618407/100000000000000000000)
  directionLo := (158563088326455163799/50000000000000000000)
  directionHi := (317126176652910327599/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree042.table
  base := (-3056880470752667969051706417393963320641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-25179306048752742787089076096980000000000000)
      constant := (198592171756525048678563499222398867602008506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree042.table
  base := (-6114011915867406950262068612392382277789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-76803871103943609649489232349180000000000000)
      constant := (616685519833326318275718681528487413695470811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158563088326455163799/50000000000000000000)
  centralHi := (317126176652910327599/100000000000000000000)
  directionLo := (64194054132205180757/20000000000000000000)
  directionHi := (160485135330512951893/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree043.table
  base := (-1100262682805035871120807514519863932367/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-77527272794049541814187520382460000000000000)
      constant := (630383552079597807266183181261549169559567165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree043.table
  base := (-5501514532746522177384170343040097930521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-709410307399404032483447577978780000000000000)
      constant := (5871184835203629560688698210000954347544433911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64194054132205180757/20000000000000000000)
  centralHi := (160485135330512951893/50000000000000000000)
  directionLo := (162384433812120338949/50000000000000000000)
  directionHi := (324768867624240677899/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree044.table
  base := (-2422061783281057283109791590530178642329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-79516627441840855267107812473980000000000000)
      constant := (665965116649217755800906434612782010702604542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree044.table
  base := (-2422142323502653264427191939562494194613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-727585774863315578121492064814940000000000000)
      constant := (6201206326695684938950657981554283146796608566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162384433812120338949/50000000000000000000)
  centralHi := (324768867624240677899/100000000000000000000)
  directionLo := (328523545743148984871/100000000000000000000)
  directionHi := (41065443217893623109/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree045.table
  base := (-129443974798874804142759947746001246549/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-27168660696544056240009368188500000000000000)
      constant := (234173722632358709388296713638734941415744544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree045.table
  base := (-414233614034270578861900424225705672031/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-82862360258580791528837394627900000000000000)
      constant := (726692647557712486378994292028389395470473690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328523545743148984871/100000000000000000000)
  centralHi := (41065443217893623109/12500000000000000000)
  directionLo := (66447158806790299727/20000000000000000000)
  directionHi := (83058948508487874659/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree046.table
  base := (-1697788354901796438684140477580196489157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-83495336737423482172948396657020000000000000)
      constant := (740051673532348933923044683484347817863405286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree046.table
  base := (-53057498165352374646376993194013946043/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-763936709791138669397581038487260000000000000)
      constant := (6888267084723105792297235689751084962373082432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66447158806790299727/20000000000000000000)
  centralHi := (83058948508487874659/25000000000000000000)
  directionLo := (67181403845733852283/20000000000000000000)
  directionHi := (41988377403583657677/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree047.table
  base := (-2604241878697909115488216094310434843429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-85484691385214795625868688748540000000000000)
      constant := (778556608160388563579596456490578558972241171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree047.table
  base := (-2604324390434464551323753950604735521481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-782112177255050215035625525323420000000000000)
      constant := (7245305897439109701758818365583073746177651271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67181403845733852283/20000000000000000000)
  centralHi := (41988377403583657677/12500000000000000000)
  directionLo := (84884638000939589787/25000000000000000000)
  directionHi := (339538552003758359149/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree048.table
  base := (-1768210383453711076843053913876140120139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-29158015344335369692929660280020000000000000)
      constant := (272678650599058070642712242188829386515839487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree048.table
  base := (-110517271372214688496696887639662506941/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-88920849413217973408185556906620000000000000)
      constant := (845705567760087554627150429021907805111143344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84884638000939589787/25000000000000000000)
  centralHi := (339538552003758359149/100000000000000000000)
  directionLo := (171565826307665550177/50000000000000000000)
  directionHi := (68626330523066220071/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree049.table
  base := (-443744137490898616644253645526564264439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-89463400680797422531709272931580000000000000)
      constant := (858489688704286892143368784518490812696388322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree049.table
  base := (-443770489169690820156742877966269773569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-818463112182873306311714498995740000000000000)
      constant := (7986399599237032229193061535251395181741046558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171565826307665550177/50000000000000000000)
  centralHi := (68626330523066220071/20000000000000000000)
  directionLo := (346687516008649490969/100000000000000000000)
  directionHi := (34668751600864949097/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree050.table
  base := (37919676814532499686975748079538755143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-91452755328588735984629565023100000000000000)
      constant := (899917806475208121145107177030754880302126943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree050.table
  base := (37877582275018358343582662907018790391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-836638579646784851949758985831900000000000000)
      constant := (8370454269226334119426718717460990402864262919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346687516008649490969/100000000000000000000)
  centralHi := (34668751600864949097/10000000000000000000)
  directionLo := (350207276460622582241/100000000000000000000)
  directionHi := (175103638230311291121/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree051.table
  base := (504004853759781461634193589187530228953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1421)
      previous := (1078)
      next := (0)
      square := (45212605631620760293643002080000000000000)
      linear := (-1832198234830981361520585433620000000000000)
      constant := (18476868535660639680416354279017128083353206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree051.table
  base := (20159521994027874431398588496881292187/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4214)
      previous := (3283)
      next := (0)
      square := (135637816894862280880929006240000000000000)
      linear := (-5587019915756185605149042305020000000000000)
      constant := (57277869568360594101674331901741141885230550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350207276460622582241/100000000000000000000)
  centralHi := (175103638230311291121/50000000000000000000)
  directionLo := (353692011806439126581/100000000000000000000)
  directionHi := (176846005903219563291/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree052.table
  base := (2022778842101301612882125501148137215899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-95431464624171362890470149206140000000000000)
      constant := (985697147496682187515433520617766304898553299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree052.table
  base := (2022752020256220358243559680874865101407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-872989514574607943225847959504220000000000000)
      constant := (9165578863656364948132348948347279717158836463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353692011806439126581/100000000000000000000)
  centralHi := (176846005903219563291/50000000000000000000)
  directionLo := (71428549458995907353/20000000000000000000)
  directionHi := (178571373647489768383/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree053.table
  base := (1541112362701008573654205826841492352647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-97420819271962676343390441297660000000000000)
      constant := (1030048356883411553161112888852309443218469694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree053.table
  base := (770550831802492343712420355532421828247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-891164982038519488863892446340380000000000000)
      constant := (9576648681108294729286959453468013850309736092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71428549458995907353/20000000000000000000)
  centralHi := (178571373647489768383/50000000000000000000)
  directionLo := (72112091822419061467/20000000000000000000)
  directionHi := (45070057389011913417/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree054.table
  base := (2093172744584718780803877754176252443059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-33136724639917996598770244463060000000000000)
      constant := (358457972873185520419154853037181621736264306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree054.table
  base := (13082276324878987466371044327836027859/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-101037827722492337166881881464060000000000000)
      constant := (1110747050993346543648296137270424482707602880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72112091822419061467/20000000000000000000)
  centralHi := (45070057389011913417/12500000000000000000)
  directionLo := (18197303880303552447/5000000000000000000)
  directionHi := (363946077606071048941/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree055.table
  base := (166723113992028781519365445901700544451/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-101399528567545303249231025480700000000000000)
      constant := (1121673828840919084360024167662290339715745632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree055.table
  base := (5335126042767308950862466510124738089129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-927515916966342580139981420012700000000000000)
      constant := (10425803167475245502031382275839009993928420761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18197303880303552447/5000000000000000000)
  centralHi := (363946077606071048941/100000000000000000000)
  directionLo := (3673004902454713977/1000000000000000000)
  directionHi := (367300490245471397701/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree056.table
  base := (6528606016226371130557439631049868127583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-103388883215336616702151317572220000000000000)
      constant := (1168948084465568769842188278125480706999843383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree056.table
  base := (6528595173433605338184312943512145699393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-945691384430254125778025906848860000000000000)
      constant := (10863887783066032374346861113964595818677090737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3673004902454713977/1000000000000000000)
  centralHi := (367300490245471397701/100000000000000000000)
  directionLo := (7412490886720413853/2000000000000000000)
  directionHi := (370624544336020692651/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree057.table
  base := (7766743646257801707106208994444029129793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-35126079287709310051690536554580000000000000)
      constant := (405732227675610565848306046985742973255530531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree057.table
  base := (121355234493635510949098862432606108833/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-107096316877129519046230043742780000000000000)
      constant := (1256775254087711653223137561013601343300776512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7412490886720413853/2000000000000000000)
  centralHi := (370624544336020692651/100000000000000000000)
  directionLo := (373919049520083032109/100000000000000000000)
  directionHi := (37391904952008303211/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree058.table
  base := (9049551775643606404786277380990605967741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-107367592510919243607991901755260000000000000)
      constant := (1266419622542237095394832991489636566122094341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree058.table
  base := (9049544895158069517568178769521228578833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-982042319358077217054114880521180000000000000)
      constant := (11767071663427489506451165432705202439801901697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373919049520083032109/100000000000000000000)
  centralHi := (37391904952008303211/10000000000000000000)
  directionLo := (37718478007963370833/10000000000000000000)
  directionHi := (377184780079633708331/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree059.table
  base := (5188514894402974292800960755335803837459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-109356947158710557060912193846780000000000000)
      constant := (1316616901410667010296505953471376851562461718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree059.table
  base := (518851215514416492093188455653966084467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1000217786821988762692159367357340000000000000)
      constant := (12232170900670863380327046575710693841425760060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37718478007963370833/10000000000000000000)
  centralHi := (377184780079633708331/100000000000000000000)
  directionLo := (76084495412256230389/20000000000000000000)
  directionHi := (190211238530640575973/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree060.table
  base := (5874588592873500688472470030397139134779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-37115433935500623504610828646100000000000000)
      constant := (455929506110542364851427698420708639259706786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree060.table
  base := (5874586412389481134671256115234241971749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-113154806031766700925578206021500000000000000)
      constant := (1411808332055076395705881865173448526737038298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76084495412256230389/20000000000000000000)
  centralHi := (190211238530640575973/50000000000000000000)
  directionLo := (191816425119930959311/50000000000000000000)
  directionHi := (383632850239861918623/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree061.table
  base := (13165993557682256761237970559144342733211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-113335656454293183966752778029820000000000000)
      constant := (1419934472241868842814445697071654435449081811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree061.table
  base := (2633198017451342867787484840882901928287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1036568721749811853968248341029660000000000000)
      constant := (13189383918676665582667719038736759256196351915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191816425119930959311/50000000000000000000)
  centralHi := (383632850239861918623/100000000000000000000)
  directionLo := (96704144983837062279/25000000000000000000)
  directionHi := (386816579935348249117/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree062.table
  base := (14627478567906748181250254780351153127519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-115325011102084497419673070121340000000000000)
      constant := (1473054762265622637061636556755773349284676919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree062.table
  base := (14627475806906373081687341808208909229009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1054744189213723399606292827865820000000000000)
      constant := (13681497684406104123880981462263842356141871681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96704144983837062279/25000000000000000000)
  centralHi := (386816579935348249117/100000000000000000000)
  directionLo := (24373394918515195331/6250000000000000000)
  directionHi := (389974318696243125297/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree063.table
  base := (16133631936766288552791390732284493419039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-39104788583291936957531120737620000000000000)
      constant := (509049795891835978896625479577650655794306813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree063.table
  base := (8066814870369226053335096905812628182791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-119213295186403882804926368300220000000000000)
      constant := (1575846253332873588674181032412657291806878782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24373394918515195331/6250000000000000000)
  centralHi := (389974318696243125297/100000000000000000000)
  directionLo := (12284584151914428073/3125000000000000000)
  directionHi := (393106692861261698337/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree064.table
  base := (17684453429849137404495339159721470072957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-119303720397667124325513654304380000000000000)
      constant := (1582218347861819804733142274900355543659761157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree064.table
  base := (8842225841811641224336985009216045866107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1091095124141546490882381801538140000000000000)
      constant := (14692739700644059684421014580403396835359397526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12284584151914428073/3125000000000000000)
  centralHi := (393106692861261698337/100000000000000000000)
  directionLo := (49526788001235641567/12500000000000000000)
  directionHi := (396214304009885132537/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree065.table
  base := (19279942848704323532632279347563422443723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-121293075045458437778433946395900000000000000)
      constant := (1638261642308387265090532801578012461776123523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree065.table
  base := (9639970730243310976686226709836235479729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1109270591605458036520426288374300000000000000)
      constant := (15211867942252383348350514914369612872689952322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49526788001235641567/12500000000000000000)
  centralHi := (396214304009885132537/100000000000000000000)
  directionLo := (199648865155650845069/50000000000000000000)
  directionHi := (399297730311301690139/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree066.table
  base := (1307506251471405728934075966330113133071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-41094143231083250410451412829140000000000000)
      constant := (565093090191196068231235190866771329381960912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree066.table
  base := (20920098920194346585706783729119485889863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-125271784341041064684274530578940000000000000)
      constant := (1748889000142548286702159714796919782799533663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199648865155650845069/50000000000000000000)
  centralHi := (399297730311301690139/100000000000000000000)
  directionLo := (201178763890150912747/50000000000000000000)
  directionHi := (80471505556060365099/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree067.table
  base := (2260492480749249698488189792545253176899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-125271784341041064684274530578940000000000000)
      constant := (1753271232275410775890414186821582035131142990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree067.table
  base := (5651230982689306084824717427663686154163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1145621526533281127796515262046620000000000000)
      constant := (16277138874645977448290477399065096916731206668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201178763890150912747/50000000000000000000)
  centralHi := (80471505556060365099/20000000000000000000)
  directionLo := (101348557861963338707/25000000000000000000)
  directionHi := (405394231447853354829/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree068.table
  base := (12167208536039503410294055214977094686927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4263)
      previous := (3234)
      next := (0)
      square := (135637816894862280880929006240000000000000)
      linear := (-7485949352284257537482048392380000000000000)
      constant := (106602207475275919905032931036422990974199662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree068.table
  base := (24334416375567553410307399396672345543101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (37926)
      previous := (29547)
      next := (0)
      square := (1220740352053760527928361056160000000000000)
      linear := (-68458646705717216084385867581340000000000000)
      constant := (989604797624226015337500796482257819812850077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101348557861963338707/25000000000000000000)
  centralHi := (405394231447853354829/100000000000000000000)
  directionLo := (408408356453335847607/100000000000000000000)
  directionHi := (51051044556666980951/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree069.table
  base := (6527144175914636882745770531252070746221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-43083497878874563863371704920660000000000000)
      constant := (624059384896947039081297803337622181347894428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree069.table
  base := (5221715230088506778851597366049269064053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-131330273495678246563622692857660000000000000)
      constant := (1930936561526857094966300550634050744178009265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408408356453335847607/100000000000000000000)
  centralHi := (51051044556666980951/12500000000000000000)
  directionLo := (411400399064748564319/100000000000000000000)
  directionHi := (2571252494154678527/625000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree070.table
  base := (13963701800304020777426884648589873147069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-131239848284415005043035406853500000000000000)
      constant := (1933093114844540587728699807303964520111052938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree070.table
  base := (27927403161298512243150166502544600899479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1200147928925015764710648722555100000000000000)
      constant := (17942581354833187984262908748493066562455903911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411400399064748564319/100000000000000000000)
  centralHi := (2571252494154678527/625000000000000000)
  directionLo := (41437083763261346347/10000000000000000000)
  directionHi := (414370837632613463471/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree071.table
  base := (29790897671104274226706277553219667147447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-133229202932206318495955698945020000000000000)
      constant := (1994982407301956868495029400175644354250509647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree071.table
  base := (7447724330579679214483207989795687317593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1218323396388927310348693209391260000000000000)
      constant := (18515738460877379843073937567567528977670138148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41437083763261346347/10000000000000000000)
  centralHi := (414370837632613463471/100000000000000000000)
  directionLo := (417320133482765301421/100000000000000000000)
  directionHi := (208660066741382650711/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree072.table
  base := (31699058831367547715028142277553197852001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-45072852526665877316291997012180000000000000)
      constant := (685948677281726321827706089387598622537684867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree072.table
  base := (6339811710901431047761010350660947664279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-137388762650315428442970855136380000000000000)
      constant := (2121988930002785804744661267632265624373948395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417320133482765301421/100000000000000000000)
  centralHi := (208660066741382650711/50000000000000000000)
  directionLo := (420248731752747098689/100000000000000000000)
  directionHi := (42024873175274709869/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree073.table
  base := (33651887004270086485766854648439375063857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-137207912227788945401796283128060000000000000)
      constant := (2121683988273597534528895835820070814541092057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree073.table
  base := (1682594339227240701684709720800881160467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1254674331316750401624782183063580000000000000)
      constant := (19689067080559940399588282041806336541707440060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420248731752747098689/100000000000000000000)
  centralHi := (42024873175274709869/10000000000000000000)
  directionLo := (423157062176104685011/100000000000000000000)
  directionHi := (105789265544026171253/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree074.table
  base := (17824691059115587831424626955384716307821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-139197266875580258854716575219580000000000000)
      constant := (2186496276401031136239695812023431294233284842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree074.table
  base := (17824690971941317353128010496509192953217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1272849798780661947262826669899740000000000000)
      constant := (20289238590877319402455647177234087395683713506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423157062176104685011/100000000000000000000)
  centralHi := (105789265544026171253/25000000000000000000)
  directionLo := (2662784623865580961/625000000000000000)
  directionHi := (426045539818492953761/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree075.table
  base := (37691544106337811391928818589779093261937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-47062207174457190769212289103700000000000000)
      constant := (750760965351146349196787631472338473858099379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree075.table
  base := (18845771984010027595008144035925606821691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-143447251804952610322319017415100000000000000)
      constant := (2322046099940812843765550138992385006686436582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2662784623865580961/625000000000000000)
  centralHi := (426045539818492953761/100000000000000000000)
  directionLo := (428914565769163875443/100000000000000000000)
  directionHi := (107228641442290968861/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree076.table
  base := (39778372905642817456354171726721733381221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-143175976171162885760557159402620000000000000)
      constant := (2319043847067095663241386851531123228524555821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree076.table
  base := (39778372795929090989083084423190082717423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1309200733708485038538915643572060000000000000)
      constant := (21516596004901324884826860512931176646332155007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428914565769163875443/100000000000000000000)
  centralHi := (107228641442290968861/25000000000000000000)
  directionLo := (1349264149347180907/312500000000000000)
  directionHi := (431764527791097890241/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree077.table
  base := (20954934228301358267486264199220665321821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-145165330818954199213477451494140000000000000)
      constant := (2386779129287128398680449289780625901004112842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree077.table
  base := (8381973673918532863592852310595353010211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1327376201172396584176960130408220000000000000)
      constant := (22143781905821225501385789259135813093080146495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1349264149347180907/312500000000000000)
  centralHi := (431764527791097890241/100000000000000000000)
  directionLo := (217297900466381106451/50000000000000000000)
  directionHi := (434595800932762212903/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree078.table
  base := (44086030702625750570461868237064783449947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-49051561822248504222132581195220000000000000)
      constant := (818496247522114030400151878062895167251104049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree078.table
  base := (8817206126726542645517913343374111551133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-149505740959589792201667179693820000000000000)
      constant := (2531108066770074710155661327005900320722484665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217297900466381106451/50000000000000000000)
  centralHi := (434595800932762212903/100000000000000000000)
  directionLo := (437408748104228500509/100000000000000000000)
  directionHi := (43740874810422850051/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree079.table
  base := (46306859589706803417040574613215000269433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-149144040114536826119318035677180000000000000)
      constant := (2525172686764269433706227899902292215700795233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree079.table
  base := (46306859535008942967979457628352457910889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1363727136100219675453049104080540000000000000)
      constant := (23425168088988045295070077459297922687236000601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437408748104228500509/100000000000000000000)
  centralHi := (43740874810422850051/10000000000000000000)
  directionLo := (55025465077519415069/12500000000000000000)
  directionHi := (440203720620155320553/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree080.table
  base := (9714471013226193444122576200186806361617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-151133394762328139572238327768700000000000000)
      constant := (2595830961746399950869262998187429416732829085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree080.table
  base := (48572355022773246089000483332480925945193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1381902603564131221091093590916700000000000000)
      constant := (24079368368800699965092991854466045995451022937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55025465077519415069/12500000000000000000)
  centralHi := (440203720620155320553/100000000000000000000)
  directionLo := (221490529355967665757/50000000000000000000)
  directionHi := (88596211742387066303/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree081.table
  base := (50882517082231407476733388564971597923983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-51040916470039817675052873286740000000000000)
      constant := (889154522461183402047832815557870375400093261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree081.table
  base := (10176503409573614269004853314261430225297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-155564230114226974081015341972540000000000000)
      constant := (2749174826580027576040086716147349900079987485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221490529355967665757/50000000000000000000)
  centralHi := (88596211742387066303/20000000000000000000)
  directionLo := (55717636501390096763/12500000000000000000)
  directionHi := (89148218402224154821/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree082.table
  base := (13309336397547563062179669040538949111171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-155112104057910766478078911951740000000000000)
      constant := (2740070503551345914621620666967447226552623084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree082.table
  base := (6654668195369945471502833240630074533789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1418253538491954312367182564589020000000000000)
      constant := (25414783299138651742020508469382355318091733608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55717636501390096763/12500000000000000000)
  centralHi := (89148218402224154821/20000000000000000000)
  directionLo := (224242070003035879207/50000000000000000000)
  directionHi := (89696828001214351683/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree083.table
  base := (27818420271936820211522307356419550609487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-157101458705702079930999204043260000000000000)
      constant := (2813651770129792903547353399332774502270551374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree083.table
  base := (11127368104459657017168656322888514135649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1436429005955865858005227051425180000000000000)
      constant := (26095997947484962037278452400202466137007037205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224242070003035879207/50000000000000000000)
  centralHi := (89696828001214351683/20000000000000000000)
  directionLo := (451210512473618142559/100000000000000000000)
  directionHi := (2820065702960113391/625000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree084.table
  base := (58081001898693954716003354467268454631437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-53030271117831131127973165378260000000000000)
      constant := (962735789000972926788590842190161750165455879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree084.table
  base := (29040500940800938215883629303668876026153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-161622719268864155960363504251260000000000000)
      constant := (2976246375913619259078277617815365493088047906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451210512473618142559/100000000000000000000)
  centralHi := (2820065702960113391/625000000000000000)
  directionLo := (226960254943692978381/50000000000000000000)
  directionHi := (453920509887385956763/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree085.table
  base := (473201793839794915973055765897438733209/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4263)
      previous := (3234)
      next := (0)
      square := (135637816894862280880929006240000000000000)
      linear := (-9475304000075570990402340483900000000000000)
      constant := (174337487885792413431475366806335440151165056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree085.table
  base := (15142457399488809869976935622659639063459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13770000000000000000000000000000000000000000
      center := (37926)
      previous := (29547)
      next := (0)
      square := (1220740352053760527928361056160000000000000)
      linear := (-86634114169628761722430354417500000000000000)
      constant := (1616790682667463887558489739696109291961532172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226960254943692978381/50000000000000000000)
  centralHi := (453920509887385956763/100000000000000000000)
  directionLo := (456614423804311936071/100000000000000000000)
  directionHi := (57076802975538992009/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree086.table
  base := (15775830910111761632458408473917913030027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-163069522649076020289760080317820000000000000)
      constant := (3040241551187660280032779410460961967164400908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree086.table
  base := (15775830907431190271344231686037635195211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1490955408347600494919360511933660000000000000)
      constant := (28193670612883299057539254780857940009138777196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456614423804311936071/100000000000000000000)
  centralHi := (57076802975538992009/12500000000000000000)
  directionLo := (28705783576922096447/6250000000000000000)
  directionHi := (459292537230753543153/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree087.table
  base := (6568148394497459358875474225226309800187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-55019625765622444580893457469780000000000000)
      constant := (1039240046094979966149944698419072105967621290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree087.table
  base := (65681483936483849145948382598501735537129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-167681208423501337839711666529980000000000000)
      constant := (3212322711653940682702029745260923014132072529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28705783576922096447/6250000000000000000)
  centralHi := (459292537230753543153/100000000000000000000)
  directionLo := (230977562484747892601/50000000000000000000)
  directionHi := (461955124969495785203/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree088.table
  base := (17076077621417596306199904822532798945257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-167048231944658647195600664500860000000000000)
      constant := (3196173055247814864070110181334911240226453828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree088.table
  base := (34152155239473814067437045713139919122667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1527306343275423586195449485605980000000000000)
      constant := (29637142980433767697625719986255864733485023606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230977562484747892601/50000000000000000000)
  centralHi := (461955124969495785203/100000000000000000000)
  directionLo := (464602453948859171323/100000000000000000000)
  directionHi := (116150613487214792831/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree089.table
  base := (35485901612118663528088333764208630994349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-169037586592449960648520956592380000000000000)
      constant := (3275600301976674434406567723646333298432603498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree089.table
  base := (70971803218915097395969257046858044253409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1545481810739335131833493972442140000000000000)
      constant := (30372386338633956493100981723788319957928051281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464602453948859171323/100000000000000000000)
  centralHi := (116150613487214792831/25000000000000000000)
  directionLo := (467234783535024440193/100000000000000000000)
  directionHi := (233617391767512220097/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree090.table
  base := (4605247632714397149652965912057468305651/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-57008980413413758033813749561300000000000000)
      constant := (1118667292791548065401526119862061200335990672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree090.table
  base := (73683962119217411257839968741662643657821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-173739697578138519719059828808700000000000000)
      constant := (3457403830957327446935821429326064536153992421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467234783535024440193/100000000000000000000)
  centralHi := (233617391767512220097/50000000000000000000)
  directionLo := (469852365828608427609/100000000000000000000)
  directionHi := (46985236582860842761/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree091.table
  base := (38220393573502835915754746834744526831049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-173016295888032587554361540775420000000000000)
      constant := (3437377784347454037607667520950861028575116898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree091.table
  base := (38220393571835609453726488213200801360349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1581832745667158223109582946114460000000000000)
      constant := (31869887399532723226407658055471455118088819482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469852365828608427609/100000000000000000000)
  centralHi := (46985236582860842761/10000000000000000000)
  directionLo := (118113861486612734257/25000000000000000000)
  directionHi := (472455445946450937029/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree092.table
  base := (79242278259675052716547783975857273340379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-175005650535823901007281832866940000000000000)
      constant := (3519728019803319281097065390705684767958325779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree092.table
  base := (79242278257036220594547102597676328947289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1600008213131069768747627432950620000000000000)
      constant := (32632145100559344928202913394221885184327088201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118113861486612734257/25000000000000000000)
  centralHi := (472455445946450937029/100000000000000000000)
  directionLo := (237522131144752047219/50000000000000000000)
  directionHi := (475044262289504094439/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree093.table
  base := (41044217713532176807930364603728930363661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-58998335061205071486734041652820000000000000)
      constant := (1201017528217610926533904705620825965250588174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree093.table
  base := (8208843542497626826699146521463513012613/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-179798186732775701598407991087420000000000000)
      constant := (3711489731210226359783980784721285973458064130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237522131144752047219/50000000000000000000)
  centralHi := (475044262289504094439/100000000000000000000)
  directionLo := (477619046797652847307/100000000000000000000)
  directionHi := (119404761699413211827/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree094.table
  base := (42489629307837784452156685627205565072957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-178984359831406527913122417049980000000000000)
      constant := (3687351478808866220490637673377443349509522314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree094.table
  base := (84979258614023473434542261932172962199541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1636359148058892860023716406622940000000000000)
      constant := (34183674839747350354298281891183956872129055269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477619046797652847307/100000000000000000000)
  centralHi := (119404761699413211827/25000000000000000000)
  directionLo := (120045006298059374777/25000000000000000000)
  directionHi := (480180025192237499109/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree095.table
  base := (87914747792851884687807133546691814352263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-180973714479197841366042709141500000000000000)
      constant := (3772624702186479230825285662591945409130236063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree095.table
  base := (43957373895772445474242016141139309076749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1654534615522804405661760893459100000000000000)
      constant := (34972946876361379663943997666203360172355234682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120045006298059374777/25000000000000000000)
  centralHi := (480180025192237499109/100000000000000000000)
  directionLo := (60340927150874500019/12500000000000000000)
  directionHi := (482727417206996000153/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree096.table
  base := (90894902926745297028960017267352230050669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (24157)
      previous := (18326)
      next := (0)
      square := (768614295737552924991931035360000000000000)
      linear := (-60987689708996384939654333744340000000000000)
      constant := (1286290751567611717454842501861034383453930023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree096.table
  base := (90894902925711430736064406123176610655107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (71638)
      previous := (55811)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-185856675887412883477756153366140000000000000)
      constant := (3974580409998781999719990461655662364313933307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60340927150874500019/12500000000000000000)
  centralHi := (482727417206996000153/100000000000000000000)
  directionLo := (6065767960101184149/1250000000000000000)
  directionHi := (485261436808094731921/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree097.table
  base := (93919723986286443005675216628336714713381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-184952423774780468271883293324540000000000000)
      constant := (3946094136277122572147989410496183794969503981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree097.table
  base := (9391972398546871523935278015525187563239/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1690885550450627496937849867131420000000000000)
      constant := (36578505279903373430652433864636071156678617510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell024.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6065767960101184149/1250000000000000000)
  centralHi := (485261436808094731921/100000000000000000000)
  directionLo := (121945573100967838967/25000000000000000000)
  directionHi := (487782292403871355869/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 51
  table := BinomialMassData.Q22_51.Degree098.table
  base := (96989210941156359231160577459962770613859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (72471)
      previous := (54978)
      next := (0)
      square := (2305842887212658774975793106080000000000000)
      linear := (-186941778422571781724803585416060000000000000)
      constant := (4034290346830481866406624984335843166366647259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree098.table
  base := (96989210940509652205438762484001001363051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 234090000000000000000000000000000000000000000
      center := (644742)
      previous := (502299)
      next := (0)
      square := (20752585984913928974782137954720000000000000)
      linear := (-1709061017914539042575894353967580000000000000)
      constant := (37394791645394927240913177431550259440907660859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell024.Kernel098
