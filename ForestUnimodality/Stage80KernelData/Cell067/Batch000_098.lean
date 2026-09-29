import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell067.Parameters
import ForestUnimodality.BinomialMassData.Q24_49.Batch000_049
import ForestUnimodality.BinomialMassData.Q24_49.Batch050_099
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch000_049
import ForestUnimodality.BinomialMassData.Q9529_19404.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree000.table
  base := (189434392305710303744348267/5000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (575833580289930244133778100000000000000)
      linear := (10175886000212464900516185000000000000)
      constant := (189434392305710303744348267000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree000.table
  base := (189434392305710303744348267/5000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (575833580289930244133778100000000000000)
      linear := (10175886000212464900516185000000000000)
      constant := (189434392305710303744348267000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree001.table
  base := (10990765493651798517773576851709221290807/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-1329928278555405805976506731015000000000000)
      constant := (264207992802890432373641629361578403192276070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree001.table
  base := (54849051685316127540005679469971585736657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-13069544166846362949554404440216765000000000000)
      constant := (2584588144123531556064641892757226742187491184114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24994793293705898961/50000000000000000000)
  directionHi := (49989586587411797923/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree002.table
  base := (131250142463030755661736604852805268008079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-5368577718794643480358305644430000000000000)
      constant := (317737165823967843473906009602145448487397679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree002.table
  base := (13078321923372226508156118348776823587921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-26378549328402811665853200749606715000000000000)
      constant := (1551644997441574197405492418335381051562490720605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24994793293705898961/50000000000000000000)
  centralHi := (49989586587411797923/100000000000000000000)
  directionLo := (17673987832335482587/25000000000000000000)
  directionHi := (70695951329341930349/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree003.table
  base := (40589890609659069045877972820702700488861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-4038649440239237674381798913415000000000000)
      constant := (100405548108205673588573497312227183873755261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree003.table
  base := (80783180937657518850166154550011874525937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-8819456553324280084922666013110370000000000000)
      constant := (217680341207388936924594975554230908192347688593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/25000000000000000000)
  centralHi := (70695951329341930349/100000000000000000000)
  directionLo := (17316900763752184271/20000000000000000000)
  directionHi := (21646125954690230339/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree004.table
  base := (26111713279174178079138295467538919299431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-5393010021081153608584445004615000000000000)
      constant := (67953238491504199263055918252920945237933831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree004.table
  base := (25958257392671870742053656805509414854603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-52996559651515709098450793368386615000000000000)
      constant := (662671297622193954048894728653725442750903571203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/20000000000000000000)
  centralHi := (21646125954690230339/25000000000000000000)
  directionLo := (24994793293705898961/25000000000000000000)
  directionHi := (19995834634964719169/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree005.table
  base := (6986446466597046886368232586381493553941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-13494741203846139085574182191630000000000000)
      constant := (100336628524485040314673371143909830115061705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree005.table
  base := (34701553367219834801225154508579122962301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-132611129626144315629499179355553130000000000000)
      constant := (978824064719869737936976755559016420952582554501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24994793293705898961/25000000000000000000)
  centralHi := (19995834634964719169/20000000000000000000)
  directionLo := (2235602275531290259/2000000000000000000)
  directionHi := (111780113776564512951/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree006.table
  base := (24148573816823724330375307610983827972797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-16203462365529970953979474374030000000000000)
      constant := (81718093872742750897271074534452170962685597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree006.table
  base := (2397404948442135830440446085571556297717/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-8846063330514289614560931776351835000000000000)
      constant := (44335632010865607572681193475885207322606825065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2235602275531290259/2000000000000000000)
  centralHi := (111780113776564512951/100000000000000000000)
  directionLo := (122448979591836734693/100000000000000000000)
  directionHi := (61224489795918367347/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree007.table
  base := (852862513534260793756443041227293325213/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (28215845434206581962555126900000000000000)
      linear := (-192981464563406151248824148535000000000000)
      constant := (747873225030751915458426556721373729354370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree007.table
  base := (8460612955277667502212664544743097404083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (276543501100658709815002798746900000000000000)
      linear := (-1896399492575205209129534332582785000000000000)
      constant := (7314323373589994527683122800861597785213456667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122448979591836734693/100000000000000000000)
  centralHi := (61224489795918367347/50000000000000000000)
  directionLo := (66130007126610818683/50000000000000000000)
  directionHi := (132260014253221637367/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree008.table
  base := (12113549008518760394305420511975567881093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-21620904688897634690790058738830000000000000)
      constant := (71348219906089523006654393869093338482504293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree008.table
  base := (6001456733957238834730188048727625333701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-106232580297741503963645978605946415000000000000)
      constant := (349433718652386358923467417304340443605344005901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66130007126610818683/50000000000000000000)
  centralHi := (132260014253221637367/100000000000000000000)
  directionLo := (17673987832335482587/12500000000000000000)
  directionHi := (141391902658683860697/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree009.table
  base := (423210280688738188327681755407433438417/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-12164812925290733279597675460615000000000000)
      constant := (36919668783917340643546126678892476856392170) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree009.table
  base := (8370037378831556121364040879189420999389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (334583495158821648911978694780200000000000000)
      linear := (-2951644085414764263702340121366330000000000000)
      constant := (8941382937559816383269638694058134778163491669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/12500000000000000000)
  centralHi := (141391902658683860697/100000000000000000000)
  directionLo := (149968759762235393767/100000000000000000000)
  directionHi := (18746094970279424221/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree010.table
  base := (1126617481324313205281464498908198447457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-27038347012265298427600643103630000000000000)
      constant := (79621734473973346979155077758192922361721285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree010.table
  base := (221986065317309686774345713426407692821/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-265701181241708802792487142449452630000000000000)
      constant := (781827971946271681181817007144381288385250725525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/100000000000000000000)
  centralHi := (18746094970279424221/12500000000000000000)
  directionLo := (79040476453212589493/50000000000000000000)
  directionHi := (158080952906425178987/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree011.table
  base := (1675150894899677408804250736125459519531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-14873534086974565148002967643015000000000000)
      constant := (44023699249242355307733727105877228306393931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree011.table
  base := (1637034811803781454384769217571185244501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (111988690528365923809381298666100000000000000)
      linear := (-1207930543656288017459027830860465000000000000)
      constant := (3575603488780110756859529347908226677535798981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79040476453212589493/50000000000000000000)
  centralHi := (158080952906425178987/100000000000000000000)
  directionLo := (82898351067713881229/50000000000000000000)
  directionHi := (165796702135427762459/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree012.table
  base := (729602732068597614126607446657239504103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-16227894667816481082205613734215000000000000)
      constant := (49370114540029678736273990803104032049351303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree012.table
  base := (694043928658498529032670353244382343393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-17718733438218588758760129315945135000000000000)
      constant := (53944664175112669046618546297395595825063899777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82898351067713881229/50000000000000000000)
  centralHi := (165796702135427762459/100000000000000000000)
  directionLo := (17316900763752184271/10000000000000000000)
  directionHi := (173169007637521842711/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree013.table
  base := (-134259091909840039735287655140531474931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-35164510497316794032816519650830000000000000)
      constant := (111474394109467917107714382200247583928690669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree013.table
  base := (-100725900917722484808358689880689543337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-172777606105523747545139960152896165000000000000)
      constant := (548379744284646946033369303734463755147595505263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/10000000000000000000)
  centralHi := (173169007637521842711/100000000000000000000)
  directionLo := (180240017680160139893/100000000000000000000)
  directionHi := (90120008840080069947/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree014.table
  base := (-1489215553944185569545463592512942927403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (56431690868413163925110253800000000000000)
      linear := (-772923095081645426555547180270000000000000)
      constant := (2573631380440590695647574892446865796557253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree014.table
  base := (-1553132507460652533352706667088746570709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (553087002201317419630005597493800000000000000)
      linear := (-7595371888452252908630153324991270000000000000)
      constant := (25330286816134674013393492880860901548163573459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180240017680160139893/100000000000000000000)
  centralHi := (90120008840080069947/50000000000000000000)
  directionLo := (46760976479141224557/25000000000000000000)
  directionHi := (187043905916564898229/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree015.table
  base := (-2644986118833877781126718654560952699357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-40581952820684457769627104015630000000000000)
      constant := (142546447081742282965299821023599152568843843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree015.table
  base := (-338245559446532763495763122342212527633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-22155068492070738330859728085741785000000000000)
      constant := (77964425287314285241182441376514550673343195452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46760976479141224557/25000000000000000000)
  centralHi := (187043905916564898229/100000000000000000000)
  directionLo := (96804418168419775469/50000000000000000000)
  directionHi := (193608836336839550939/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree016.table
  base := (-1814703086931834893354877966683068459119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-21645336991184144819016198099015000000000000)
      constant := (80361544832528620760477208978633952629655281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree016.table
  base := (-1843805943633734299237937614936007847723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-212704621590193093694036349081066015000000000000)
      constant := (791317646521194312040332422091490401189804971677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804418168419775469/50000000000000000000)
  centralHi := (193608836336839550939/100000000000000000000)
  directionLo := (199958346349647191689/100000000000000000000)
  directionHi := (19995834634964719169/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree017.table
  base := (-2231710816097365765349025337308525452287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-22999697572026060753218844190215000000000000)
      constant := (90293787127016925358591108233002230389058913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree017.table
  base := (-903786707748325715683806972495148165893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-452027253503499084820670290780911930000000000000)
      constant := (1778520114218106329719279473994066394177122897535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199958346349647191689/100000000000000000000)
  centralHi := (19995834634964719169/10000000000000000000)
  directionLo := (103056172840429366871/50000000000000000000)
  directionHi := (206112345680858733743/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree018.table
  base := (-2581827902657372998109523753086743375189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-24354058152867976687421490281415000000000000)
      constant := (101049994138895091855747110999158729156171211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree018.table
  base := (-1043302842728894114902001497545151012207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (334583495158821648911978694780200000000000000)
      linear := (-5909200787982863978435405967897430000000000000)
      constant := (24575602990573127481124075903619240913913050765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103056172840429366871/50000000000000000000)
  centralHi := (206112345680858733743/100000000000000000000)
  directionLo := (53021963497006447761/25000000000000000000)
  directionHi := (42417570797605158209/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree019.table
  base := (-5743864306835305959871918927843033329061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-51416837467419785243248272745230000000000000)
      constant := (225227304508044806247275821382168876976924539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree019.table
  base := (-2897048955781685117678141259829394399953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-252631637074862439842932738009235865000000000000)
      constant := (1109311525268252786005220027891886300272031613447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53021963497006447761/25000000000000000000)
  centralHi := (42417570797605158209/20000000000000000000)
  directionLo := (27237444520488038803/12500000000000000000)
  directionHi := (8715982246556172417/4000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree020.table
  base := (-6215778574609972897891609599655349860163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-54125558629103617111653564927630000000000000)
      constant := (249941355762511317220086912488827504985748637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree020.table
  base := (-3131709222475528611288768170731116006289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-265940642236418888559231534318625815000000000000)
      constant := (1231120808342609565220776493280894986185689987911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27237444520488038803/12500000000000000000)
  centralHi := (8715982246556172417/4000000000000000000)
  directionLo := (2235602275531290259/1000000000000000000)
  directionHi := (223560227553129025901/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree021.table
  base := (-823701396989564495666883437604028697929/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (28215845434206581962555126900000000000000)
      linear := (-579941630518239275306723031735000000000000)
      constant := (2818547159868936662128936359389610375205916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree021.table
  base := (-6634697229329552565146550881130336890913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4055436)
      previous := (2027718)
      next := (2027718)
      square := (61454111355701935514445066388200000000000000)
      linear := (-1266438310194899488777915331646330000000000000)
      constant := (6170609996095227397923751956164359093163991407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2235602275531290259/1000000000000000000)
  centralHi := (223560227553129025901/100000000000000000000)
  directionLo := (229081064496363758301/100000000000000000000)
  directionHi := (114540532248181879151/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree022.table
  base := (-3437186109802815129883318580160501463393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-29771500476235640424232074646215000000000000)
      constant := (152017234475313857161835191181114635986393407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree022.table
  base := (-1383391092157823470806161536367971076553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (14780556)
      previous := (7390278)
      next := (7390278)
      square := (223977381056731847618762597332200000000000000)
      linear := (-4835680207595566710608745899791830000000000000)
      constant := (24755396171199814793419660115421688085304480035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229081064496363758301/100000000000000000000)
  centralHi := (114540532248181879151/50000000000000000000)
  directionLo := (117235972378327115507/50000000000000000000)
  directionHi := (46894388951330846203/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree023.table
  base := (-7078078711765658912107594607227204698951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-62251722114155112716869441474830000000000000)
      constant := (333372648781308969667848786169087481517818649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree023.table
  base := (-711822119019846242117882860264077693487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-305867657721088234708127923246795665000000000000)
      constant := (1642272242145042662545737966207178823186237625565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117235972378327115507/50000000000000000000)
  centralHi := (46894388951330846203/20000000000000000000)
  directionLo := (11987081759664010803/5000000000000000000)
  directionHi := (239741635193280216061/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree024.table
  base := (-7207901879569525489192337492911819103089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-64960443275838944585274733657230000000000000)
      constant := (364214943042757369437201585879838722333483311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree024.table
  base := (-1449135101352827887255352514078380994831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-70928147307254374094317048790263470000000000000)
      constant := (398721629352012331482169524950078540375031637205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11987081759664010803/5000000000000000000)
  centralHi := (239741635193280216061/100000000000000000000)
  directionLo := (244897959183673469387/100000000000000000000)
  directionHi := (61224489795918367347/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree025.table
  base := (-3635138691804460039204770981196435511479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-33834582218761388226840012919815000000000000)
      constant := (198272949856946132865954285035147358336938921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree025.table
  base := (-146115245239084387036167963267690804087/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-332485668044201132140725515865575565000000000000)
      constant := (1953550919170646887005909144154608392309327362825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244897959183673469387/100000000000000000000)
  centralHi := (61224489795918367347/25000000000000000000)
  directionLo := (249947932937058989611/100000000000000000000)
  directionHi := (62486983234264747403/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree026.table
  base := (-454437021272046099242594120976316772829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-35188942799603304161042659011015000000000000)
      constant := (215175811964035920938784050717326907427500568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree026.table
  base := (-7304274964717396779290661541618577468187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-691589346411515161714048624349931030000000000000)
      constant := (4240229672792557716822520402390611724684552410413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249947932937058989611/100000000000000000000)
  centralHi := (62486983234264747403/25000000000000000000)
  directionLo := (254897877485648906361/100000000000000000000)
  directionHi := (127448938742824453181/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree027.table
  base := (-7215257044097763763598555065038776345171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-73086606760890440190490610204430000000000000)
      constant := (465619605768689515298057408081401897995244429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree027.table
  base := (-7246428567094274170623543956391075407933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (334583495158821648911978694780200000000000000)
      linear := (-8866757490550963693168471814428530000000000000)
      constant := (56638956150892320922375662231742318381411896907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254897877485648906361/100000000000000000000)
  centralHi := (127448938742824453181/50000000000000000000)
  directionLo := (51950702291256552813/20000000000000000000)
  directionHi := (129876755728141382033/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree028.table
  base := (-1421553191358623161746465276062956784961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (56431690868413163925110253800000000000000)
      linear := (-1546843426991311674671344946670000000000000)
      constant := (10251807629236846032419620193924575587684555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree028.table
  base := (-3568460305240753042735000037561480171063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (276543501100658709815002798746900000000000000)
      linear := (-7600258847527968944686161322321335000000000000)
      constant := (50505802256552068488326406754725791709327165313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51950702291256552813/20000000000000000000)
  centralHi := (129876755728141382033/50000000000000000000)
  directionLo := (264520028506443274733/100000000000000000000)
  directionHi := (132260014253221637367/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree029.table
  base := (-3476375347548959596806172141948123206147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-39252024542129051963650597284615000000000000)
      constant := (270249184004110551247409428803542556182041053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree029.table
  base := (-6979984406534758758524560018675431082551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-771443377380853854011841402206270730000000000000)
      constant := (5325569572411255087629453209561951097003762275249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264520028506443274733/100000000000000000000)
  centralHi := (132260014253221637367/50000000000000000000)
  directionLo := (16825135150858315269/6250000000000000000)
  directionHi := (53840432482746608861/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree030.table
  base := (-1350805343281935767773859558968333485137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-81212770245941935795706486751630000000000000)
      constant := (580089827382325046702395528060985156510930315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree030.table
  base := (-847429490515690689939083054242003695859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-44336743761331486191357721934725035000000000000)
      constant := (317537139104624522101531463302859480893912508596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16825135150858315269/6250000000000000000)
  centralHi := (53840432482746608861/20000000000000000000)
  directionLo := (273804242142831391397/100000000000000000000)
  directionHi := (136902121071415695699/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree031.table
  base := (-6515034823326161802337974549701801405907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-83921491407625767664111778934030000000000000)
      constant := (621104690587880049505430075748645974824417293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree031.table
  base := (-1307743097199692870569813021581045724863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-824679398027079648877036587443830530000000000000)
      constant := (6119784457191729479084824445214881951061665932685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273804242142831391397/100000000000000000000)
  centralHi := (136902121071415695699/50000000000000000000)
  directionLo := (55666047742799411807/20000000000000000000)
  directionHi := (69582559678499264759/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree032.table
  base := (-1559719567267078948957077795761314899451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-43315106284654799766258535558215000000000000)
      constant := (331767753356951307723933421405234165852836298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree032.table
  base := (-6260925050119208912060648433334458931719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-851297408350192546309634180062610430000000000000)
      constant := (6537844436438378489174068477353793372192543216481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55666047742799411807/20000000000000000000)
  centralHi := (69582559678499264759/25000000000000000000)
  directionLo := (17673987832335482587/6250000000000000000)
  directionHi := (282783805317367721393/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree033.table
  base := (-2964178022690842863595612887720817816697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-44669466865496715700461181649415000000000000)
      constant := (353687777690605845602977887467502316422110503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree033.table
  base := (-5948861654324467789841888330711905478281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (1642284)
      previous := (821142)
      next := (821142)
      square := (24886375672970205290973621925800000000000000)
      linear := (-806166591986506376255492904206970000000000000)
      constant := (6400167696204417260159398479322331434519825871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/6250000000000000000)
  centralHi := (282783805317367721393/100000000000000000000)
  directionLo := (143584155912962129221/50000000000000000000)
  directionHi := (287168311825924258443/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree034.table
  base := (-2792996404697432742841755256940206947/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-46023827446338631634663827740615000000000000)
      constant := (376309387444020761425795657040646563120253000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree034.table
  base := (-560504748036299837826948128964375563847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-452266714498209170587414682650085115000000000000)
      constant := (3707769829444277455026394607945075709460320313765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143584155912962129221/50000000000000000000)
  centralHi := (287168311825924258443/100000000000000000000)
  directionLo := (145743437317201020367/50000000000000000000)
  directionHi := (58297374926880408147/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree035.table
  base := (-5214065823914697888545154353655299685819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (56431690868413163925110253800000000000000)
      linear := (-1933803592946144798729243829870000000000000)
      constant := (16311422398497813893481229525870890315394869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree035.table
  base := (-1046351382543507668263017592370209231363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (553087002201317419630005597493800000000000000)
      linear := (-19003090598357780379743407304468370000000000000)
      constant := (160715551598600264625567953394246946934235753065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145743437317201020367/50000000000000000000)
  centralHi := (58297374926880408147/20000000000000000000)
  directionLo := (295742382575294664769/100000000000000000000)
  directionHi := (29574238257529466477/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree036.table
  base := (-962925845705203167113427278884188879839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-97465097216044927006138239846030000000000000)
      constant := (847293391307122581200524432175875312497532805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree036.table
  base := (-2415520455548724529785644493039596521589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (167291747579410824455989347390100000000000000)
      linear := (-5912157096559531703950768830479815000000000000)
      constant := (51532725098142351682246693447939508378951442131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295742382575294664769/100000000000000000000)
  centralHi := (29574238257529466477/10000000000000000000)
  directionLo := (149968759762235393767/50000000000000000000)
  directionHi := (59987503904894157507/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree037.table
  base := (-4389535916576474707226814718636280107411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-100173818377728758874543532028430000000000000)
      constant := (896715407433302903542897733549914291462106189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree037.table
  base := (-550593621679150056506447558938764730941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-492193729982878516736311071578254965000000000000)
      constant := (4417607224417225012753756885240232184139141875436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149968759762235393767/50000000000000000000)
  centralHi := (59987503904894157507/20000000000000000000)
  directionLo := (304074784199006933047/100000000000000000000)
  directionHi := (38009348024875866631/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree038.table
  base := (-3940457260039276573634467699470899959229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-102882539539412590742948824210830000000000000)
      constant := (947521732940826189637365372515810369197891171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree038.table
  base := (-1977274466568942048337015574878344785797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-505502735144434965452609867887644915000000000000)
      constant := (4667880864673234369280251428568381672453323050803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304074784199006933047/100000000000000000000)
  centralHi := (38009348024875866631/12500000000000000000)
  directionLo := (308156507562071416213/100000000000000000000)
  directionHi := (154078253781035708107/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree039.table
  base := (-1734450448586043513254466509488665231857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-52795630350548211305677058196615000000000000)
      constant := (499854373995117892199105209899477714778311343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree039.table
  base := (-1740972403620996532306828106543593864383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-57645748922887934907656518244114985000000000000)
      constant := (547217106366891562533496324158477027102330278113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308156507562071416213/100000000000000000000)
  centralHi := (154078253781035708107/50000000000000000000)
  directionLo := (156092434089575045817/50000000000000000000)
  directionHi := (62436973635830018327/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree040.table
  base := (-1488113387494133947377526591166508349443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-54149990931390127239879704287815000000000000)
      constant := (526636593674376303037116174272209213452987357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree040.table
  base := (-1494146444485755895632571989734625720237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-532120745467547862885207460506424815000000000000)
      constant := (5188810544021189691239113691898583700891613148363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156092434089575045817/50000000000000000000)
  centralHi := (62436973635830018327/20000000000000000000)
  directionLo := (316161905812850357973/100000000000000000000)
  directionHi := (158080952906425178987/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree041.table
  base := (-492732323746363159486447391635039787303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-111008703024464086348164700758030000000000000)
      constant := (1108212105649065818783069518298701347353427485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree041.table
  base := (-77338008073825635517642258055310342013/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-545429750629104311601506256815814765000000000000)
      constant := (5459436233948108369591988072232313539129941430192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316161905812850357973/100000000000000000000)
  centralHi := (158080952906425178987/50000000000000000000)
  directionLo := (320089533497104529269/100000000000000000000)
  directionHi := (32008953349710452927/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree042.table
  base := (-1932311983122382499896913884622536456189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (56431690868413163925110253800000000000000)
      linear := (-2320763758900977922787142713070000000000000)
      constant := (23765772368434562012981655953893495713646739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree042.table
  base := (-388523573385237837488769716533529628333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (4055436)
      previous := (2027718)
      next := (2027718)
      square := (61454111355701935514445066388200000000000000)
      linear := (-2533962611295513652234943551588230000000000000)
      constant := (26017315417888659905705508352615506627512613935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320089533497104529269/100000000000000000000)
  centralHi := (32008953349710452927/10000000000000000000)
  directionLo := (80992387073405834403/25000000000000000000)
  directionHi := (323969548293623337613/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree043.table
  base := (-1383176024669967589882926610302082374857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-116426145347831750084975285122830000000000000)
      constant := (1222203011987655256623178262671304700217968343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree043.table
  base := (-696346168383936413991156090738861852157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-572047760952217209034103849434594665000000000000)
      constant := (6020944288286565517469690801100646309383809192443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80992387073405834403/25000000000000000000)
  centralHi := (323969548293623337613/100000000000000000000)
  directionLo := (81950910225556176227/25000000000000000000)
  directionHi := (327803640902224704909/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree044.table
  base := (-817154120545203579309344660314912315859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-119134866509515581953380577305230000000000000)
      constant := (1281250441646564284083183195160503895529622541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree044.table
  base := (-825936600609902593160867856910253345291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (14780556)
      previous := (7390278)
      next := (7390278)
      square := (223977381056731847618762597332200000000000000)
      linear := (-9675318448161548061990126375933630000000000000)
      constant := (104327345396262851713803834272189507019154461029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81950910225556176227/25000000000000000000)
  centralHi := (327803640902224704909/100000000000000000000)
  directionLo := (82898351067713881229/25000000000000000000)
  directionHi := (331593404270855524917/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree045.table
  base := (-29382305888307638106854822324704444247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-60921793835599706910892934743815000000000000)
      constant := (670831592497292086558725225616193538517451812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree045.table
  base := (-243159496667955094386747614253693546387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (334583495158821648911978694780200000000000000)
      linear := (-14781870895687163122634603507490730000000000000)
      constant := (163194786600857448177014102979040377697210102373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82898351067713881229/25000000000000000000)
  centralHi := (331593404270855524917/100000000000000000000)
  directionLo := (335340341329693538851/100000000000000000000)
  directionHi := (83835085332423384713/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree046.table
  base := (362378379944855893049985755635743760319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-124552308832883245690191161670030000000000000)
      constant := (1403439483021415852865006146170961420768525919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree046.table
  base := (354909578913721045089377968333729082917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1223949552873773110366000476725529030000000000000)
      constant := (13827378177441400686246708731873307752858748510317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335340341329693538851/100000000000000000000)
  centralHi := (83835085332423384713/25000000000000000000)
  directionLo := (339045871955839789901/100000000000000000000)
  directionHi := (169522935977919894951/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree047.table
  base := (974495511826169075911592865740966359769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-127261029994567077558596453852430000000000000)
      constant := (1466577749029132352735127301296804060229805369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree047.table
  base := (967612869473700334376650919327637627623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1250567563196886007798598069344308930000000000000)
      constant := (14449394702801681455497795779799677913508387588223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339045871955839789901/100000000000000000000)
  centralHi := (169522935977919894951/50000000000000000000)
  directionLo := (342711339260136024529/100000000000000000000)
  directionHi := (34271133926013602453/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree048.table
  base := (320139367284201756531465701971218943837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-129969751156250909427001746034830000000000000)
      constant := (1531076551752542029071578473775204483420763185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree048.table
  base := (797178610803049890110750670682666841043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-70954754084444383623955314553504935000000000000)
      constant := (838045185141395807606204379682727371479939880627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342711339260136024529/100000000000000000000)
  centralHi := (34271133926013602453/10000000000000000000)
  directionLo := (17316900763752184271/5000000000000000000)
  directionHi := (346338015275043685421/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree049.table
  base := (1120222318356073944093796763159374567421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (575833580289930244133778100000000000000)
      linear := (-27629835967916439253520832615000000000000)
      constant := (332556143301350795407537593923159374567421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree049.table
  base := (1117303870008288319866561695975076203609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (372438)
      previous := (186219)
      next := (186219)
      square := (5643744920421606322755159158100000000000000)
      linear := (-271512616377157809800873230858365000000000000)
      constant := (3276472611288660871074502318034974221871571809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17316900763752184271/5000000000000000000)
  centralHi := (346338015275043685421/100000000000000000000)
  directionLo := (21870444131992661591/6250000000000000000)
  directionHi := (349927106111882585457/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree050.table
  base := (723313467608193436602537716085803615751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-67693596739809286581906165199815000000000000)
      constant := (832075364792141603499055498434644028962836302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree050.table
  base := (1443941032790636680252834293255173003803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-665210797083112350048195423600324315000000000000)
      constant := (8197903896209449776821728605214875362915265960403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21870444131992661591/6250000000000000000)
  centralHi := (349927106111882585457/100000000000000000000)
  directionLo := (17673987832335482587/5000000000000000000)
  directionHi := (353479756646709651741/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree051.table
  base := (1779343505039683779261984479502642888819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-69047957320651202516108811291015000000000000)
      constant := (866361944801298071394501804769325845576054419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree051.table
  base := (3553745215397583589787506284051160924449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-150782178276593066392109826646603170000000000000)
      constant := (1896818003941364332558437977404984315906386631361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17673987832335482587/5000000000000000000)
  centralHi := (353479756646709651741/100000000000000000000)
  directionLo := (89249263696611741901/25000000000000000000)
  directionHi := (71399410957289393521/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree052.table
  base := (847269877678532247127716213956339640739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-140804635802986236900622914764430000000000000)
      constant := (1802653132591935824238247353383105857387071695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree052.table
  base := (2115902464814370589648271077014078332263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-691828807406225247480793016219104215000000000000)
      constant := (8880137488915482406427921920680969176144557700863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89249263696611741901/25000000000000000000)
  centralHi := (71399410957289393521/20000000000000000000)
  directionLo := (180240017680160139893/50000000000000000000)
  directionHi := (360480035360320279787/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree053.table
  base := (4925884999791030540190191723991768409353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-143513356964670068769028206946830000000000000)
      constant := (1873937603782900771551451555472744235950856553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree053.table
  base := (4921707475366204720637355121616906888759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1410275625135563392394183625056988330000000000000)
      constant := (18462538295381052902093979208368584812904561428559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180240017680160139893/50000000000000000000)
  centralHi := (360480035360320279787/100000000000000000000)
  directionLo := (90982420919015346343/25000000000000000000)
  directionHi := (363929683676061385373/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree054.table
  base := (5626972713091519952309129416191684925013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-146222078126353900637433499129230000000000000)
      constant := (1946576532139520708525409134522996235504956213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree054.table
  base := (2811566931311474001624385629839853558567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (167291747579410824455989347390100000000000000)
      linear := (-8869713799127631418683834677010915000000000000)
      constant := (118383607911025009707167617469231076595688443407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90982420919015346343/25000000000000000000)
  centralHi := (363929683676061385373/100000000000000000000)
  directionLo := (367346938775510204081/100000000000000000000)
  directionHi := (183673469387755102041/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree055.table
  base := (396207678451823291570828345760205869517/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-74465399644018866252919395655815000000000000)
      constant := (1010284611078383336933422045459562034341682536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree055.table
  base := (633579643197954823946283121298359488719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 972405000000000000000000000000000000000000000
      center := (7390278)
      previous := (3695139)
      next := (3695139)
      square := (111988690528365923809381298666100000000000000)
      linear := (-6047568784222269368840408307002265000000000000)
      constant := (82260689120606129850884237873947581258627799195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367346938775510204081/100000000000000000000)
  centralHi := (183673469387755102041/50000000000000000000)
  directionLo := (74146539284020204051/20000000000000000000)
  directionHi := (11585396763128156883/3125000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree056.table
  base := (706267412963210779211066037318569251449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (28215845434206581962555126900000000000000)
      linear := (-1547342045405322085451470239735000000000000)
      constant := (21386888229199689607828013304903049466605005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree056.table
  base := (7059435777380645609106264357582743045879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (553087002201317419630005597493800000000000000)
      linear := (-30410809308263307850856661283945470000000000000)
      constant := (421415490771173736974221072564451774765040343871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74146539284020204051/20000000000000000000)
  centralHi := (11585396763128156883/3125000000000000000)
  directionLo := (46760976479141224557/12500000000000000000)
  directionHi := (374087811833129796457/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree057.table
  base := (7796790836469887442614946464609419428589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-154348241611405396242649375676430000000000000)
      constant := (2172613439138636550250918778664487216048042189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree057.table
  base := (3896908985582254516930035558821478580029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-84263759246000832340254110862894885000000000000)
      constant := (1189164212141988073349263642242580905506937445981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46760976479141224557/12500000000000000000)
  centralHi := (374087811833129796457/100000000000000000000)
  directionLo := (377413102222590394913/100000000000000000000)
  directionHi := (188706551111295197457/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree058.table
  base := (53384127282525316227311252833864866123/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-78528481386544614055527333929415000000000000)
      constant := (1125331944855032367504240545856248763484905840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree058.table
  base := (1067341507705182741854833951713533806863/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-771682838375563939778585794075443915000000000000)
      constant := (11086936057666968645342198378947679545353581181852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377413102222590394913/100000000000000000000)
  centralHi := (188706551111295197457/50000000000000000000)
  directionLo := (190354674552832960113/50000000000000000000)
  directionHi := (380709349105665920227/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree059.table
  base := (2324122733191609050414816257690277972257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-79882841967386529989729980020615000000000000)
      constant := (1165032968852353740577331114762988714822778114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree059.table
  base := (1161748477056549491924646983194679449053/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-784991843537120388494884590384833865000000000000)
      constant := (11478051730767928890214897445803696460702737822612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190354674552832960113/50000000000000000000)
  centralHi := (380709349105665920227/100000000000000000000)
  directionLo := (191988650226803869481/50000000000000000000)
  directionHi := (383977300453607738963/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree060.table
  base := (10061709543303897955662399602931743836591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-162474405096456891847865252223630000000000000)
      constant := (2410819167759521384416389113739439116951654991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree060.table
  base := (10059413687567724113615087667067212955501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-177400188599705963824707419265383070000000000000)
      constant := (2639071757806537044014370615417814253975405954189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191988650226803869481/50000000000000000000)
  centralHi := (383977300453607738963/100000000000000000000)
  directionLo := (387217672673679101877/100000000000000000000)
  directionHi := (193608836336839550939/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree061.table
  base := (10836960147785028366456880988662407632683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-165183126258140723716270544406030000000000000)
      constant := (2492923205200782035405556246394658440726071883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree061.table
  base := (2166970995231605144251573553382904392023/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1623219707720466571854964366007227530000000000000)
      constant := (24560495551098915744021993126549640935584340163115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387217672673679101877/100000000000000000000)
  centralHi := (193608836336839550939/50000000000000000000)
  directionLo := (195215576221520316077/50000000000000000000)
  directionHi := (78086230488608126431/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree062.table
  base := (11622101983890635438621994858273444556731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-167891847419824555584675836588430000000000000)
      constant := (2576377712058161054141158492386074540380711131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree062.table
  base := (11620172177705674335589175092192388974891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1649837718043579469287561958626007430000000000000)
      constant := (25382649371207755631085025106843128313027318965091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195215576221520316077/50000000000000000000)
  centralHi := (78086230488608126431/20000000000000000000)
  directionLo := (6150287475123058033/1562500000000000000)
  directionHi := (393618398407875714113/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree063.table
  base := (2483401615705513976365807934525992972543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (56431690868413163925110253800000000000000)
      linear := (-3481644256765477294960839362670000000000000)
      constant := (54309844560597179370961564067718868278273035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree063.table
  base := (496609579586191694659635919521654659847/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (450604)
      previous := (225302)
      next := (225302)
      square := (6828234595077992834938340709800000000000000)
      linear := (-422387434710680868410219085725570000000000000)
      constant := (6605720413246238808802312033872057261955821575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6150287475123058033/1562500000000000000)
  centralHi := (393618398407875714113/100000000000000000000)
  directionLo := (396780042759664912099/100000000000000000000)
  directionHi := (3967800427596649121/1000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree064.table
  base := (13221563897035486218833347270104097443157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-173309289743192219321486420953230000000000000)
      constant := (2747336944436364751022566238935039937961019957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree064.table
  base := (2643988693127112228101141049701754357141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1703073738689805264152757143863567230000000000000)
      constant := (27066857728355837053818695910472790887924338986705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396780042759664912099/100000000000000000000)
  centralHi := (3967800427596649121/1000000000000000000)
  directionLo := (399916692699294383379/100000000000000000000)
  directionHi := (19995834634964719169/5000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree065.table
  base := (14035666124716640891736862277384714545831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-176018010904876051189891713135630000000000000)
      constant := (2834841146900880657394994060285200699624540231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree065.table
  base := (3508545450466709004362851072373894308737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-864845874506459080792677368241173565000000000000)
      constant := (13964453594159580170224571709218593718551910280274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399916692699294383379/100000000000000000000)
  centralHi := (19995834634964719169/5000000000000000000)
  directionLo := (100757232949650505191/25000000000000000000)
  directionHi := (80605786359720404153/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree066.table
  base := (594368862709059396210258718946316934541/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-178726732066559883058297005318030000000000000)
      constant := (2923694767104388746156725340122032673995823525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree066.table
  base := (3714465560688735499295513858715125162463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (821142)
      previous := (410571)
      next := (410571)
      square := (12443187836485102645486810962900000000000000)
      linear := (-806386482707084967409528158448635000000000000)
      constant := (13225092070287932946554458082891897779271325934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100757232949650505191/25000000000000000000)
  centralHi := (80605786359720404153/20000000000000000000)
  directionLo := (406117321268008144789/100000000000000000000)
  directionHi := (40611732126800814479/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree067.table
  base := (1569214616163257199049122384404461321981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-90717726614121857463351148750215000000000000)
      constant := (1506948801604093356908064460134655558170381905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree067.table
  base := (784545079699079079651412538741038955307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-891463884829571978225274960859953465000000000000)
      constant := (14846442896457144835411997720646445411451143407070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406117321268008144789/100000000000000000000)
  centralHi := (40611732126800814479/10000000000000000000)
  directionLo := (204591200569014503579/50000000000000000000)
  directionHi := (409182401138029007159/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree068.table
  base := (4133591019273670788716704927759168704919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-92072087194963773397553794841415000000000000)
      constant := (1552724736573014347286016940995419528121021038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree068.table
  base := (16533224832523612466730690027540120433887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-1809545779982256853883147514338686830000000000000)
      constant := (30594811214343815266978772784348671539614436095287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204591200569014503579/50000000000000000000)
  centralHi := (409182401138029007159/100000000000000000000)
  directionLo := (103056172840429366871/25000000000000000000)
  directionHi := (82444938272343493497/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree069.table
  base := (17385806913152249085418550042729293695509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-186852895551611378663512881865230000000000000)
      constant := (3198350212687208361504011967304513034162917109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree069.table
  base := (17384764304084346960808469607080699313209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-204018198922818861257305011884162970000000000000)
      constant := (3501113911257909619829986884095553981606555127001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103056172840429366871/25000000000000000000)
  centralHi := (82444938272343493497/20000000000000000000)
  directionLo := (415244692844404171779/100000000000000000000)
  directionHi := (20762234642220208589/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree070.table
  base := (9123206484768561971406261760295210226737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (28215845434206581962555126900000000000000)
      linear := (-1934302211360155209509369122935000000000000)
      constant := (33597955853973284657671658195454465301110113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree070.table
  base := (18245458999351080762553891179574708065459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4802490000000000000000000000000000000000000000
      center := (36498924)
      previous := (18249462)
      next := (18249462)
      square := (553087002201317419630005597493800000000000000)
      linear := (-38015955114866992831598830603596870000000000000)
      constant := (662010741186999881133818745865038598973728619291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415244692844404171779/100000000000000000000)
  centralHi := (20762234642220208589/5000000000000000000)
  directionLo := (418242888406514219723/100000000000000000000)
  directionHi := (104560722101628554931/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree071.table
  base := (19116126590270441756219484486471732269003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-192270337874979042400323466230030000000000000)
      constant := (3388197722522544042219504446705698629177876203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree071.table
  base := (4778813475334193919424436154379889933749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-944699905475797773090470146097513265000000000000)
      constant := (16690156635099220330529131227548880790557716303098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418242888406514219723/100000000000000000000)
  centralHi := (104560722101628554931/25000000000000000000)
  directionLo := (421219743684699860757/100000000000000000000)
  directionHi := (210609871842349930379/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree072.table
  base := (3998979514312122576817308324328476863871/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-194979059036662874268728758412430000000000000)
      constant := (3485144238647391192077689305901723364750771355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree072.table
  base := (499852484920605542825668304522456023273/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (11039798)
      previous := (5519899)
      next := (5519899)
      square := (167291747579410824455989347390100000000000000)
      linear := (-11827270501695731133416900523542015000000000000)
      constant := (211946820308143990078727220504331298926745904660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421219743684699860757/100000000000000000000)
  centralHi := (210609871842349930379/50000000000000000000)
  directionLo := (53021963497006447761/12500000000000000000)
  directionHi := (424175707976051582089/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree073.table
  base := (1305167539231472487434045245998254911339/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-98843890099173353068567025297415000000000000)
      constant := (1791719556666473927941462040697654480336999512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree073.table
  base := (10440975372808360160732891117786844595379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-971317915798910670523067738716293165000000000000)
      constant := (17651870062245174940448790899707353034674222299179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53021963497006447761/12500000000000000000)
  centralHi := (424175707976051582089/100000000000000000000)
  directionLo := (106777803757430355779/25000000000000000000)
  directionHi := (427111215029721423117/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree074.table
  base := (4355886981860665105817958139459253934153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-200396501360030538005539342777230000000000000)
      constant := (3683082248499814340946146891188528343479506765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree074.table
  base := (10889383800958849417189189278907558099773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-984626920960467119239366535025683115000000000000)
      constant := (18142689012243058336170058896260137315123036290373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106777803757430355779/25000000000000000000)
  centralHi := (427111215029721423117/100000000000000000000)
  directionLo := (215013341894953854049/50000000000000000000)
  directionHi := (430026683789907708099/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree075.table
  base := (5671280892171944595692703757213079245121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-101552611260857184936972317479815000000000000)
      constant := (1892036777838364929537731879925137206535071042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree075.table
  base := (22684513582719300466087739930454835150043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-221763539138227459545703406963349570000000000000)
      constant := (4142255303748263655180184196042551272463630781627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215013341894953854049/50000000000000000000)
  centralHi := (430026683789907708099/100000000000000000000)
  directionLo := (54115314886725575847/12500000000000000000)
  directionHi := (432922519093804606777/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree076.table
  base := (23599713367896204044269914216977876970357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-205813943683398201742349927142030000000000000)
      constant := (3886412955059350735198836050985043882605827157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree076.table
  base := (4719831175716571967754623159267560735731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2022489862567160033343928255288926030000000000000)
      constant := (38288498480156813182899582870920932090064648869655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54115314886725575847/12500000000000000000)
  centralHi := (432922519093804606777/100000000000000000000)
  directionLo := (435799112327808620849/100000000000000000000)
  directionHi := (8715982246556172417/2000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree077.table
  base := (24523174325068461719028580208027998224433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (3724)
      previous := (1862)
      next := (1862)
      square := (56431690868413163925110253800000000000000)
      linear := (-4255564588675143543076637129070000000000000)
      constant := (81430619891045525944255689525633371912997217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree077.table
  base := (1532666556415478118925118997066906456427/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (150822)
      previous := (75411)
      next := (75411)
      square := (2285483480170733138966965278900000000000000)
      linear := (-172803834785821633561859153981085000000000000)
      constant := (3315059838717278119685933693789375913804470104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435799112327808620849/100000000000000000000)
  centralHi := (8715982246556172417/2000000000000000000)
  directionLo := (109664210511248352241/25000000000000000000)
  directionHi := (87731368408998681793/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree078.table
  base := (25455479395473902484415950838061343540123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-211231386006765865479160511506830000000000000)
      constant := (4095135749547971679221305267107625285839835323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree078.table
  base := (1272750698705661163236315723855134508309/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-115318104622965879344951302251471435000000000000)
      constant := (2241374464885245900482098605499814720423959509010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109664210511248352241/25000000000000000000)
  centralHi := (87731368408998681793/20000000000000000000)
  directionLo := (441496074546610933851/100000000000000000000)
  directionHi := (110374018636652733463/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree079.table
  base := (13198302091893375602617748834364976938583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-106970053584224848673782901844615000000000000)
      constant := (2100759510573198136478779313629670309629537783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree079.table
  base := (6599044758202360925624399800427745855391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-1051171946768249362820860516572632865000000000000)
      constant := (20696390157621440119725435285694976062891955891182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441496074546610933851/100000000000000000000)
  centralHi := (110374018636652733463/25000000000000000000)
  directionLo := (444317164430147780921/100000000000000000000)
  directionHi := (222158582215073890461/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree080.table
  base := (3418315835568382302860917808682920411903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-108324414165066764607985547935815000000000000)
      constant := (2154625068310697606913595279789790767635916412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree080.table
  base := (27346138381800856829968495897923952123387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2128961903859611623074318625764045630000000000000)
      constant := (42454098898858199838913939767762417324081919684787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444317164430147780921/100000000000000000000)
  centralHi := (222158582215073890461/50000000000000000000)
  directionLo := (447120455106258051801/100000000000000000000)
  directionHi := (223560227553129025901/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree081.table
  base := (14152613524023085821070739245637914325229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-109678774745908680542188194027015000000000000)
      constant := (2209164524156909013594576908932016632294874829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree081.table
  base := (28304872455271939816885691728411225711159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (334583495158821648911978694780200000000000000)
      linear := (-26612097705959561981566866893615130000000000000)
      constant := (537391304424119523393893489500124962704831623839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447120455106258051801/100000000000000000000)
  centralHi := (223560227553129025901/50000000000000000000)
  directionLo := (449906279286706181301/100000000000000000000)
  directionHi := (224953139643353090651/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree082.table
  base := (7318171842286536536815202974802044981741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-111033135326750596476390840118215000000000000)
      constant := (2264377856616714253890481819907479420002320282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree082.table
  base := (29272363609210206736171322770451957571729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2182197924505837417939513811001605430000000000000)
      constant := (44616570178526876642079501580152950661421398745529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449906279286706181301/100000000000000000000)
  centralHi := (224953139643353090651/50000000000000000000)
  directionLo := (56584369930660291643/12500000000000000000)
  directionHi := (90534991889056466629/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree083.table
  base := (30248891496786491148218565794498064075013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-224774991815185024821186972418830000000000000)
      constant := (4640530092601530417215765734098429851844106213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree083.table
  base := (30248595932648021385495251763993924694993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2208815934828950315372111403620385330000000000000)
      constant := (45717722084957697060828217101329765188701438969593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56584369930660291643/12500000000000000000)
  centralHi := (90534991889056466629/20000000000000000000)
  directionLo := (227713404126748951973/50000000000000000000)
  directionHi := (455426808253497903947/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree084.table
  base := (15616912431075861552486028833647547086509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (28215845434206581962555126900000000000000)
      linear := (-2321262377314988333567268006135000000000000)
      constant := (48506654606514263056264465510288729807238941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree084.table
  base := (3123355507744389207606334788531165797793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2027718)
      previous := (1013859)
      next := (1013859)
      square := (30727055677850967757222533194100000000000000)
      linear := (-2534505606748370989574499995736015000000000000)
      constant := (53097676916102940013935358592830342690680161365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227713404126748951973/50000000000000000000)
  centralHi := (455426808253497903947/100000000000000000000)
  directionLo := (229081064496363758301/50000000000000000000)
  directionHi := (458162128992727516603/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree085.table
  base := (2014217145229482229879432846096866152949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-115096217069276344278998778391815000000000000)
      constant := (2434060929095560360667199489215228605065844392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree085.table
  base := (32227228104782345437790929208790847206257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2262051955475176110237306588857945130000000000000)
      constant := (47959856739183358315212828990698118858417928181657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229081064496363758301/50000000000000000000)
  centralHi := (458162128992727516603/100000000000000000000)
  directionLo := (92176243188867060611/20000000000000000000)
  directionHi := (28805075996520956441/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree086.table
  base := (6645965605441181348991578958603634690609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-232901155300236520426402848966030000000000000)
      constant := (4983939184397907753020949793020916634460761045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree086.table
  base := (8307400836687580059871723854703000204359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-1144334982899144503834952090738362515000000000000)
      constant := (24550419453963858661088024397378356844724034128318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92176243188867060611/20000000000000000000)
  centralHi := (28805075996520956441/6250000000000000000)
  directionLo := (115896088689801502263/25000000000000000000)
  directionHi := (463584354759206009053/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree087.table
  base := (17120437639961976134452226891794200474781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (91238)
      previous := (45619)
      next := (45619)
      square := (1382576426276122516165201218100000000000000)
      linear := (-117804938230960176147404070574215000000000000)
      constant := (2550552052192636609270692453653877875339949181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree087.table
  base := (34240670281509300684802771548245045656161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (198716364)
      previous := (99358182)
      next := (99358182)
      square := (3011251456429394840207808253021800000000000000)
      linear := (-257254219569044656122500197121722770000000000000)
      constant := (5583899699848205696657699812453574830181661948929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115896088689801502263/25000000000000000000)
  centralHi := (463584354759206009053/100000000000000000000)
  directionLo := (116567955701998596209/25000000000000000000)
  directionHi := (466271822807994384837/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree088.table
  base := (35260606436541122870104784454182005241971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-238318597623604184163213433330830000000000000)
      constant := (5219616594994888482654790552140730994585972371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree088.table
  base := (35260419420727846840005748554600220213041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1944810000000000000000000000000000000000000000
      center := (14780556)
      previous := (7390278)
      next := (7390278)
      square := (223977381056731847618762597332200000000000000)
      linear := (-19354594929293510764752887328217230000000000000)
      constant := (424980427173722624457045871074314145427252426721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116567955701998596209/25000000000000000000)
  centralHi := (466271822807994384837/100000000000000000000)
  directionLo := (117235972378327115507/25000000000000000000)
  directionHi := (468943889513308462029/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree089.table
  base := (36289012796698171756892952386782519320829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-241027318785288016031618725513230000000000000)
      constant := (5339476635337190993814376818982184828889310429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree089.table
  base := (36288842208070333554236299835598026386451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2368523996767627699967696959333064730000000000000)
      constant := (52603441874738066435815123355716539857129268608651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117235972378327115507/25000000000000000000)
  centralHi := (468943889513308462029/100000000000000000000)
  directionLo := (471600816664952771441/100000000000000000000)
  directionHi := (235800408332476385721/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree090.table
  base := (37326086512393960421592715187177785750553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-243736039946971847900024017695630000000000000)
      constant := (5460684206569130018463213049843613863587077753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree090.table
  base := (37325930927655981420612116748854493361561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (22079596)
      previous := (11039798)
      next := (11039798)
      square := (334583495158821648911978694780200000000000000)
      linear := (-29569654408527661696299932740146230000000000000)
      constant := (664167008360680006252069159369619031265894063281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471600816664952771441/100000000000000000000)
  centralHi := (235800408332476385721/50000000000000000000)
  directionLo := (1482008933497736053/312500000000000000)
  directionHi := (474242858719275536961/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree091.table
  base := (2398238781530379526098162590636793081329/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (1862)
      previous := (931)
      next := (931)
      square := (28215845434206581962555126900000000000000)
      linear := (-2514742460292404895596217447735000000000000)
      constant := (56971829507078414435846247753889622887880968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree091.table
  base := (19185839310754459588199100499091614247291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2401245000000000000000000000000000000000000000
      center := (18249462)
      previous := (9124731)
      next := (9124731)
      square := (276543501100658709815002798746900000000000000)
      linear := (-24711836912386260151356042291536985000000000000)
      constant := (561274376854234622606175329285911233650647255459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1482008933497736053/312500000000000000)
  centralHi := (474242858719275536961/100000000000000000000)
  directionLo := (238435131541794338993/50000000000000000000)
  directionHi := (476870263083588677987/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree092.table
  base := (7885241677474222658205612325066040798337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-249153482270339511636834602060430000000000000)
      constant := (5707141875379021032479964191624177819784035685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree092.table
  base := (39426079015116197370395370679113988067731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2448378027736966392265489737189404430000000000000)
      constant := (56225525490584704059189405599345461379121447505931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238435131541794338993/50000000000000000000)
  centralHi := (476870263083588677987/100000000000000000000)
  directionLo := (479483270386560432121/100000000000000000000)
  directionHi := (239741635193280216061/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree093.table
  base := (40489244401043412576824539287570079040661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-251862203432023343505239894242830000000000000)
      constant := (5832391943795365656977506309096095759776627061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree093.table
  base := (5061140806287175874610879161556549557191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-137499779892226627205449296100454685000000000000)
      constant := (3192190956704154164376974382955082699520568714396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479483270386560432121/100000000000000000000)
  centralHi := (239741635193280216061/50000000000000000000)
  directionLo := (96416422947083400241/20000000000000000000)
  directionHi := (241041057367708500603/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree094.table
  base := (41560923349809337387553156135503794955591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-254570924593707175373645186425230000000000000)
      constant := (5958989484467858075642894717495264611688373991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree094.table
  base := (41560815824667771918118199017651792517783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2501614048383192187130684922426964230000000000000)
      constant := (58706624001914861582779928042347324574538765630383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96416422947083400241/20000000000000000000)
  centralHi := (241041057367708500603/50000000000000000000)
  directionLo := (4846670239607313157/1000000000000000000)
  directionHi := (484667023960731315701/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree095.table
  base := (8528248109401046310733471092789739164381/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-257279645755391007242050478607630000000000000)
      constant := (6086934486143818850013048134172540818668393905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree095.table
  base := (2132057126852355847768935998248256496753/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 117661005000000000000000000000000000000000000000
      center := (894223638)
      previous := (447111819)
      next := (447111819)
      square := (13550631553932276780935137138598100000000000000)
      linear := (-1264116029353152542281641257522872065000000000000)
      constant := (29983542863014533605825977462965857997811474433530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4846670239607313157/1000000000000000000)
  centralHi := (484667023960731315701/100000000000000000000)
  directionLo := (97447643969904668971/20000000000000000000)
  directionHi := (60904777481190418107/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree096.table
  base := (8746038353026172547238076509394086182231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-259988366917074839110455770790030000000000000)
      constant := (6216226938673019922242083371030956004617683155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree096.table
  base := (21865051219115359515107133993805832942613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (99358182)
      previous := (49679091)
      next := (49679091)
      square := (1505625728214697420103904126510900000000000000)
      linear := (-141936114946078776777548894870251335000000000000)
      constant := (3402267905298748461765005195815258939530887842357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97447643969904668971/20000000000000000000)
  centralHi := (60904777481190418107/12500000000000000000)
  directionLo := (19591836734693877551/4000000000000000000)
  directionHi := (61224489795918367347/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree097.table
  base := (8965554638173574374754307477874617643387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (182476)
      previous := (91238)
      next := (91238)
      square := (2765152852552245032330402436200000000000000)
      linear := (-262697088078758670978861062972430000000000000)
      constant := (6346866832899683912223697397382044784808860935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree097.table
  base := (44827691786595407084869975739425155754531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 235322010000000000000000000000000000000000000000
      center := (1788447276)
      previous := (894223638)
      next := (894223638)
      square := (27101263107864553561870274277196200000000000000)
      linear := (-2581468079352530879428477700283303930000000000000)
      constant := (62527833621911448355545873691457838674671930152731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell067.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19591836734693877551/4000000000000000000)
  centralHi := (61224489795918367347/12500000000000000000)
  directionLo := (492340329869992600287/100000000000000000000)
  directionHi := (15385635308437268759/3125000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 24
  qDenominator := 49
  table := BinomialMassData.Q24_49.Degree098.table
  base := (22966990692252343813317384154308536238163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (575833580289930244133778100000000000000)
      linear := (-55269847821833090971942181415000000000000)
      constant := (1349199117152241427982317349674308536238163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24_49.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9529
  qDenominator := 19404
  table := BinomialMassData.Q9529_19404.Degree098.table
  base := (45933907208066001280760972950324607424767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (744876)
      previous := (372438)
      next := (372438)
      square := (11287489840843212645510318316200000000000000)
      linear := (-1086249933226007403940472841691830000000000000)
      constant := (26583973188767838409790324324667546477370141367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9529_19404.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell067.Kernel098
