import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell183.Parameters
import ForestUnimodality.BinomialMassData.Q83_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q83_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q83_126.Batch100_149
import ForestUnimodality.BinomialMassData.Q2_3.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_3.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_3.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree000.table
  base := (127680930468463409232882099/20000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-82459056244605058727525915280000000000000)
      constant := (8043898619513194781671572237000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree000.table
  base := (127680930468463409232882099/20000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-1963310862966787112560140840000000000000)
      constant := (191521395702695113849323148500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree001.table
  base := (23186595736934781851969024062666430461073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-8818279255511234982628510089420000000000000)
      constant := (372725852583507042537591969465007249999994948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree001.table
  base := (46166754443251829557716744477713813303099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-10047544421489135041403173440000000000000)
      constant := (420813282326062964812478565619424319727891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (30010543871903535651/100000000000000000000)
  directionHi := (7502635967975883913/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree002.table
  base := (4177903763025555881102269306742079239103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-12441637967612351265422887516200000000000000)
      constant := (276931333554594464222060832871568999999996912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree002.table
  base := (1324792017479160623578064135129196271101/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-14205156254077908745125924360000000000000)
      constant := (311474929828129987026935328324069160997725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30010543871903535651/100000000000000000000)
  centralHi := (7502635967975883913/25000000000000000000)
  directionLo := (10610329539459689051/25000000000000000000)
  directionHi := (8488263631567751241/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree003.table
  base := (5950277783902521768553062523042428898367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-1784999631079274172024140549220000000000000)
      constant := (23326671462771136030392064371328689153438776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree003.table
  base := (23466615529949946556933111401786771586941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-6120922695555560816282891760000000000000)
      constant := (78484080148372187599642366805360314760823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10610329539459689051/25000000000000000000)
  centralHi := (8488263631567751241/20000000000000000000)
  directionLo := (25989893374455870263/50000000000000000000)
  directionHi := (51979786748911740527/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree004.table
  base := (8315373177715670688630956720991393237119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-19688355391814583831011642369760000000000000)
      constant := (164797593182487802298105058230859359032501244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree004.table
  base := (16302975038912743534256584371187870394651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-22520379919255456152571426200000000000000)
      constant := (184607192027755781795311724300690833551859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25989893374455870263/50000000000000000000)
  centralHi := (51979786748911740527/100000000000000000000)
  directionLo := (60021087743807071303/100000000000000000000)
  directionHi := (7502635967975883913/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree005.table
  base := (2818401005938326304184424124046020070099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-23311714103915700113806019796540000000000000)
      constant := (136435318655792684459910911257184229265783448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree005.table
  base := (10972495239080927773441262959927272012021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-26677991751844229856294177120000000000000)
      constant := (153032331052969335284262366039345448108189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60021087743807071303/100000000000000000000)
  centralHi := (7502635967975883913/12500000000000000000)
  directionLo := (33552808069658023357/50000000000000000000)
  directionHi := (13421123227863209343/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree006.table
  base := (727670962312327220881067802629286608131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-2992785868446312932955599691480000000000000)
      constant := (13473056429479476387123573523250307883715420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree006.table
  base := (17527896751038762718670011933121102987/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-10278534528144334520005642680000000000000)
      constant := (45517166883468758527535581359745323584400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33552808069658023357/50000000000000000000)
  centralHi := (13421123227863209343/20000000000000000000)
  directionLo := (18377629847393068317/25000000000000000000)
  directionHi := (73510519389572273269/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree007.table
  base := (4265941805235688511282723103653794644259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-4365490218302561811342110664300000000000000)
      constant := (16613483649743732138762859217628403126589706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree007.table
  base := (126195459590060137522344572135568938877/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-34993215417021777263739678960000000000000)
      constant := (131738304375755643009748806895043854396576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/25000000000000000000)
  centralHi := (73510519389572273269/100000000000000000000)
  directionLo := (39700217897425097133/50000000000000000000)
  directionHi := (79400435794850194267/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree008.table
  base := (198400847191193805714394563467067355889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-34181790240219048962189152076880000000000000)
      constant := (119503567029123342581669993888655806710468820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree008.table
  base := (28012034016095361328634229570507744867/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-39150827249610550967462429880000000000000)
      constant := (136243624495966694272340922632612461043392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39700217897425097133/50000000000000000000)
  centralHi := (79400435794850194267/100000000000000000000)
  directionLo := (84882636315677512409/100000000000000000000)
  directionHi := (8488263631567751241/10000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree009.table
  base := (60317574062650097609412707636135734129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-4200572105813351693887058833740000000000000)
      constant := (14375521703458162748413095174615286870007112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree009.table
  base := (83155485043079206661016364588317895179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-14436146360733108223728393600000000000000)
      constant := (49447838126228923628848652413764953685537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84882636315677512409/100000000000000000000)
  centralHi := (8488263631567751241/10000000000000000000)
  directionLo := (18006326323142121391/20000000000000000000)
  directionHi := (22507907903927651739/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree010.table
  base := (-1101997981556835269801615842184959820731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-41428507664421281527777906930440000000000000)
      constant := (144813631341846532854179824485435788943037322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree010.table
  base := (-1231112740350018735321308657778253565373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-47466050914788098374907931720000000000000)
      constant := (166773263682478030424069402879995717911643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18006326323142121391/20000000000000000000)
  centralHi := (22507907903927651739/25000000000000000000)
  directionLo := (23725418113905901949/25000000000000000000)
  directionHi := (94901672455623607797/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree011.table
  base := (-2148728451266061773953568469892341773593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-45051866376522397810572284357220000000000000)
      constant := (164988300132811857090741727212709591001218766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree011.table
  base := (-2253107922507768674913630998395016641539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-51623662747376872078630682640000000000000)
      constant := (190605211597113271118918039934444850226149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23725418113905901949/25000000000000000000)
  centralHi := (94901672455623607797/100000000000000000000)
  directionLo := (19906742755520718719/20000000000000000000)
  directionHi := (24883428444400898399/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree012.table
  base := (-1487371089828506784530533976674522673241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-5408358343180390454818517976000000000000000)
      constant := (21033537119546701978308592769226142004402876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree012.table
  base := (-1529213900763263421902108388849865670231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-18593758193321881927451144520000000000000)
      constant := (73052992820575095628632491106900805978614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19906742755520718719/20000000000000000000)
  centralHi := (24883428444400898399/25000000000000000000)
  directionLo := (103959573497823481053/100000000000000000000)
  directionHi := (51979786748911740527/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree013.table
  base := (-3635887196982572833762778834464644433943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-52298583800724630376161039210780000000000000)
      constant := (217310911507024536262252928482734652483360466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree013.table
  base := (-3702515817781500597115390265655477865731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-59938886412554419486076184480000000000000)
      constant := (251935573312937211528906784609100699208421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103959573497823481053/100000000000000000000)
  centralHi := (51979786748911740527/50000000000000000000)
  directionLo := (108204554734709800683/100000000000000000000)
  directionHi := (27051138683677450171/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree014.table
  base := (-4173298623350201977800666662054485507657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-7988848930403678094136488091080000000000000)
      constant := (35527000263244496550662397909330213434316962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree014.table
  base := (-1056508257130542845737964051221419658773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-64096498245143193189798935400000000000000)
      constant := (288569046635503712015003631116028892284172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108204554734709800683/100000000000000000000)
  centralHi := (27051138683677450171/25000000000000000000)
  directionLo := (112289173159411303957/100000000000000000000)
  directionHi := (56144586579705651979/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree015.table
  base := (-4617274128109130598504550072883890479841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-6616144580547429215749977118260000000000000)
      constant := (31466178020409661337591645025791408596780238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree015.table
  base := (-7454078123667676087071541535471750051/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-22751370025910655631173895440000000000000)
      constant := (109597007962510321055411041020990468654375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112289173159411303957/100000000000000000000)
  centralHi := (56144586579705651979/50000000000000000000)
  directionLo := (11623033662650944443/10000000000000000000)
  directionHi := (116230336626509444431/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree016.table
  base := (-311883054817981021045228086505669495693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-63168659937027979224544171491120000000000000)
      constant := (320653574743605620620255877205727928691023456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree016.table
  base := (-2511340717255830029407853687592788856699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-72411721910320740597244437240000000000000)
      constant := (372404691085240936456924552343329800579418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11623033662650944443/10000000000000000000)
  centralHi := (116230336626509444431/100000000000000000000)
  directionLo := (120042175487614142607/100000000000000000000)
  directionHi := (7502635967975883913/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree017.table
  base := (-2654149271935498704069317197319402104487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-66792018649129095507338548917900000000000000)
      constant := (360932453145548971964356844421952172189164388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree017.table
  base := (-2666858952252322617131099820078776710979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-76569333742909514300967188160000000000000)
      constant := (419265714739714154843976663758582019202378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120042175487614142607/100000000000000000000)
  centralHi := (7502635967975883913/6250000000000000000)
  directionLo := (123736642266091076331/100000000000000000000)
  directionHi := (30934160566522769083/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree018.table
  base := (-697986044743311704518447947367550865721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-7823930817914467976681436260520000000000000)
      constant := (44881794008649505554721528883434561091472624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree018.table
  base := (-5603668957534796013639483819544346779253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-26908981858499429334896646360000000000000)
      constant := (156422749456192910643822271741366959662241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123736642266091076331/100000000000000000000)
  centralHi := (30934160566522769083/25000000000000000000)
  directionLo := (63661977236758134307/50000000000000000000)
  directionHi := (25464790894703253723/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree019.table
  base := (-2912907037621463828618500184103122905143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-74038736073331328072927303771460000000000000)
      constant := (449593880269932995656236759555653820757949732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree019.table
  base := (-5841159272238417765049467810413762062333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-84884557408087061708412690000000000000000)
      constant := (522334669864107919406477835666276141439003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63661977236758134307/50000000000000000000)
  centralHi := (25464790894703253723/20000000000000000000)
  directionLo := (13081292797832135631/10000000000000000000)
  directionHi := (130812927978321356311/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree020.table
  base := (-755080294353292144754304825734249424821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-77662094785432444355721681198240000000000000)
      constant := (497853529582145101799136320826972224526167216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree020.table
  base := (-3026256870850663936837140675647044880699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-89042169240675835412135440920000000000000)
      constant := (578408055188529360802370557438353192147418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13081292797832135631/10000000000000000000)
  centralHi := (130812927978321356311/100000000000000000000)
  directionLo := (134211232278632093429/100000000000000000000)
  directionHi := (13421123227863209343/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree021.table
  base := (-3116604861924192631292053832121225293189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-1290245293611643819658985057540000000000000)
      constant := (8709153994634158199087769996310451226116372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree021.table
  base := (-624237074799956404882353432126445563921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-31066593691088203038619397280000000000000)
      constant := (212482219634386238911786163876206633082370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134211232278632093429/100000000000000000000)
  centralHi := (13421123227863209343/10000000000000000000)
  directionLo := (68762794469895535221/50000000000000000000)
  directionHi := (137525588939791070443/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree022.table
  base := (-3203539229640082893104593538113659266659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-84908812209634676921310436051800000000000000)
      constant := (602035119154757047180380927245127545482521716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree022.table
  base := (-100220811023557353518380781686110530251/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-97357392905853382819580942760000000000000)
      constant := (699419866478625088193329348468800334575424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68762794469895535221/50000000000000000000)
  centralHi := (137525588939791070443/100000000000000000000)
  directionLo := (140761927937648789721/100000000000000000000)
  directionHi := (70380963968824394861/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree023.table
  base := (-1641218087856036934558324154087517040621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-88532170921735793204104813478580000000000000)
      constant := (657907954413139344716679679489528158926202008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree023.table
  base := (-6570291875321758922179131276820655332271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-101515004738442156523303693680000000000000)
      constant := (764305225965063473301266042708614102009561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140761927937648789721/100000000000000000000)
  centralHi := (70380963968824394861/50000000000000000000)
  directionLo := (17990689041579291727/12500000000000000000)
  directionHi := (143925512332634333817/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree024.table
  base := (-3354261998154040496025598091626531720287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-10239503292648545498544354545040000000000000)
      constant := (79586651832203397850713129158370798045413732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree024.table
  base := (-6712680228836402118709306410612065367847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-35224205523676976742342148200000000000000)
      constant := (277362090406640904483090393088163803896459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17990689041579291727/12500000000000000000)
  centralHi := (143925512332634333817/100000000000000000000)
  directionLo := (18377629847393068317/12500000000000000000)
  directionHi := (147021038779144546537/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree025.table
  base := (-6839456926972877105007138174889898028281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-95778888345938025769693568332140000000000000)
      constant := (777139555379551999057397700517598989451505422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree025.table
  base := (-3421319406335378921097305116597047419179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-109830228403619703930749195520000000000000)
      constant := (902750925623630389990495324901253146454778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/12500000000000000000)
  centralHi := (147021038779144546537/100000000000000000000)
  directionLo := (75026359679758839129/50000000000000000000)
  directionHi := (150052719359517678259/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree026.table
  base := (-3479359876283187592545820600738421468551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-99402247058039142052487945758920000000000000)
      constant := (840478697222888053080389557038416820765284324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree026.table
  base := (-3480575907051389307311481568431804952951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-113987840236208477634471946440000000000000)
      constant := (976290331490684930227047196088227510846882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75026359679758839129/50000000000000000000)
  centralHi := (150052719359517678259/100000000000000000000)
  directionLo := (15302434881636849589/10000000000000000000)
  directionHi := (153024348816368495891/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree027.table
  base := (-7067084950755803300485503953799268777439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-11447289530015584259475813687300000000000000)
      constant := (100699017788012920702241616886704044938298802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree027.table
  base := (-7068941140188465771764361551358800277757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-39381817356265750446064899120000000000000)
      constant := (350899330552527440712332274985923599166729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15302434881636849589/10000000000000000000)
  centralHi := (153024348816368495891/100000000000000000000)
  directionLo := (7796968012336761079/5000000000000000000)
  directionHi := (155939360246735221581/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree028.table
  base := (-3582560813605298362297966207994129177879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-15235566354605910659725242944640000000000000)
      constant := (139224632346633245939492326320189315024570428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree028.table
  base := (-358326818022635014122576858216808864511/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-122303063901386025041917448280000000000000)
      constant := (1131969139998598637000849626320974404388020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/5000000000000000000)
  centralHi := (155939360246735221581/100000000000000000000)
  directionLo := (39700217897425097133/25000000000000000000)
  directionHi := (158800871589700388533/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree029.table
  base := (-725324910190412389785215722547663821327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-110272323194342490900871078039260000000000000)
      constant := (1045319167663888760169077521021441445863062740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree029.table
  base := (-3627162998246692063487298759648834726849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-126460675733974798745640199200000000000000)
      constant := (1214100279819352756995994632286320974916718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39700217897425097133/25000000000000000000)
  centralHi := (158800871589700388533/100000000000000000000)
  directionLo := (161611724701940975421/100000000000000000000)
  directionHi := (80805862350970487711/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree030.table
  base := (-3665888187258547490948070154381566337027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-12655075767382623020407272829560000000000000)
      constant := (124280992329446547203883818727570916981484372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree030.table
  base := (-3666297566484850560959482273196716902533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-43539429188854524149787650040000000000000)
      constant := (433029615119304009257721015160819698584802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161611724701940975421/100000000000000000000)
  centralHi := (80805862350970487711/50000000000000000000)
  directionLo := (3287490368327998963/2000000000000000000)
  directionHi := (164374518416399948151/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree031.table
  base := (-231279099686716416978918312915380891423/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-117519040618544723466459832892820000000000000)
      constant := (1194199908490605268394025837311401607484295232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree031.table
  base := (-925194124737912163623028984479279375991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-134775899399152346153085701040000000000000)
      constant := (1386932953562081634957058523237491884928648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3287490368327998963/2000000000000000000)
  centralHi := (164374518416399948151/100000000000000000000)
  directionLo := (41772909169782852053/25000000000000000000)
  directionHi := (167091636679131408213/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree032.table
  base := (-1492176288931468755716084615009664413617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-121142399330645839749254210319600000000000000)
      constant := (1272330767479185503660147010204986419423541270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree032.table
  base := (-7461353187406865986445489119687895472079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-138933511231741119856808451960000000000000)
      constant := (1477631222066847338863205259042808940751289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41772909169782852053/25000000000000000000)
  centralHi := (167091636679131408213/100000000000000000000)
  directionLo := (169765272631355024819/100000000000000000000)
  directionHi := (8488263631567751241/5000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree033.table
  base := (-1877937737917701952107834844032869672619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-13862862004749661781338731971820000000000000)
      constant := (150324502789146730092604992180087035795000168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree033.table
  base := (-1502421699310340460194691538244900380113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-47697041021443297853510400960000000000000)
      constant := (523727545238855827723855586726326494298305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169765272631355024819/100000000000000000000)
  centralHi := (8488263631567751241/5000000000000000000)
  directionLo := (172397449328827792521/100000000000000000000)
  directionHi := (86198724664413896261/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree034.table
  base := (-7553631051706707662962224960793136363797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-128389116754848072314842965173160000000000000)
      constant := (1435968456297602214267512088787524083544179414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree034.table
  base := (-7553901794923857202905793881936174430903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-147248734896918667264253953800000000000000)
      constant := (1667586448684967609329104120022574430121873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172397449328827792521/100000000000000000000)
  centralHi := (86198724664413896261/50000000000000000000)
  directionLo := (8749501882760697073/5000000000000000000)
  directionHi := (174990037655213941461/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree035.table
  base := (-758658916428663855102392253346599145539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-18858925066707026942519620371420000000000000)
      constant := (217353432269838287313498642616774565689587740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree035.table
  base := (-7586794001769614383815583955100066406481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-151406346729507440967976704720000000000000)
      constant := (1766842112698831164111659562204099402341671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8749501882760697073/5000000000000000000)
  centralHi := (174990037655213941461/100000000000000000000)
  directionLo := (177544771880392580611/100000000000000000000)
  directionHi := (44386192970098145153/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree036.table
  base := (-951334385711770775873875135956764701939/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-15070648242116700542270191114080000000000000)
      constant := (178826315399246557423879425504449068263118416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree036.table
  base := (-7610829934292917854144884830826946692353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-51854652854032071557233151880000000000000)
      constant := (622983074801107550475084858147519159922941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177544771880392580611/100000000000000000000)
  centralHi := (44386192970098145153/25000000000000000000)
  directionLo := (18006326323142121391/10000000000000000000)
  directionHi := (180063263231421213911/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree037.table
  base := (-1525185125482642993416823679099400796469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-139259192891151421163226097453500000000000000)
      constant := (1699856602201095839747865501060139782388145390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree037.table
  base := (-3813021298178753077637234081169151585191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-159721570394684988375422206560000000000000)
      constant := (1973907486763668424397462211858955271466562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18006326323142121391/10000000000000000000)
  centralHi := (180063263231421213911/100000000000000000000)
  directionLo := (182547011777885681497/100000000000000000000)
  directionHi := (91273505888942840749/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree038.table
  base := (-3816184016202468192841202196241841186623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-142882551603252537446020474880280000000000000)
      constant := (1792733100457872858954680979449804529321173252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree038.table
  base := (-1908114080889281085756329554106939802667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-163879182227273762079144957480000000000000)
      constant := (2081716680759524777525893616052150167103988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182547011777885681497/100000000000000000000)
  centralHi := (91273505888942840749/50000000000000000000)
  directionLo := (46249354220169239959/25000000000000000000)
  directionHi := (184997416880676959837/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree039.table
  base := (-7630022491304038991161070519626334228419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-16278434479483739303201650256340000000000000)
      constant := (209785130343365750904124315143364573210534442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree039.table
  base := (-305203563587028135320387912021562305501/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-56012264686620845260955902800000000000000)
      constant := (730792214875612110706679473918382827087425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46249354220169239959/25000000000000000000)
  centralHi := (184997416880676959837/100000000000000000000)
  directionLo := (187415786410884895429/100000000000000000000)
  directionHi := (18741578641088489543/10000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree040.table
  base := (-7618903995735817932514609746334406078539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-150129269027454770011609229733840000000000000)
      constant := (1985855701094830944402460786390397484548557418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree040.table
  base := (-7618954198205833918599181256860031472643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-172194405892451309486590459320000000000000)
      constant := (2305887258634169772389552459888259716746213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187415786410884895429/100000000000000000000)
  centralHi := (18741578641088489543/10000000000000000000)
  directionLo := (189803344911247215593/100000000000000000000)
  directionHi := (94901672455623607797/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree041.table
  base := (-7599023703443424753330578939199279310497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-153752627739555886294403607160620000000000000)
      constant := (2086101595901325280797708803343151120833274814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree041.table
  base := (-1899765380734389177505113111504116029847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-176352017725040083190313210240000000000000)
      constant := (2422248433917414731492395575705851822925508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189803344911247215593/100000000000000000000)
  centralHi := (94901672455623607797/50000000000000000000)
  directionLo := (192161240844727376953/100000000000000000000)
  directionHi := (96080620422363688477/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree042.table
  base := (-7570389943876958754985731805840518771957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-2498031530978682580590444199800000000000000)
      constant := (34742917323660315540770384384404094634733418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree042.table
  base := (-1892604604470999775663012052517481676693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-60169876519209618964678653720000000000000)
      constant := (847153368096817687773386979209790219879684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192161240844727376953/100000000000000000000)
  centralHi := (96080620422363688477/50000000000000000000)
  directionLo := (194490553051999849583/100000000000000000000)
  directionHi := (12155659565749990599/6250000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree043.table
  base := (-7533008958990598175846162183576369188587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-160999345163758118859992362014180000000000000)
      constant := (2293962238014022472358786972132685781380996394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree043.table
  base := (-7533030384732369701998545302724682939909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-184667241390217630597758712080000000000000)
      constant := (2663522220238099890423307354875477853540819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194490553051999849583/100000000000000000000)
  centralHi := (12155659565749990599/6250000000000000000)
  directionLo := (196792296520875569721/100000000000000000000)
  directionHi := (98396148260437784861/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree044.table
  base := (-935860681127999707933141048884700824289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-164622703875859235142786739440960000000000000)
      constant := (2401576898461090682076189306555225958854351344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree044.table
  base := (-7486901562486566188731554062800694415113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-188824853222806404301481463000000000000000)
      constant := (2788434744509320133675790334394793750263983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196792296520875569721/100000000000000000000)
  centralHi := (98396148260437784861/50000000000000000000)
  directionLo := (19906742755520718719/10000000000000000000)
  directionHi := (199067427555207187191/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree045.table
  base := (-14515669872372732051855239831022468919/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-18694006954217816825064568540860000000000000)
      constant := (279071971607460563526425672245622549395682304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree045.table
  base := (-7432035086719291185837595930002096302843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-64327488351798392668401404640000000000000)
      constant := (972065882961319823156910394409993711091471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19906742755520718719/10000000000000000000)
  centralHi := (199067427555207187191/100000000000000000000)
  directionLo := (12582303026121758759/6250000000000000000)
  directionHi := (40263369683589628029/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree046.table
  base := (-1842106063341629828964620883141370705651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-171869421300061467708375494294520000000000000)
      constant := (2624174754460802430410970737569435197354169448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree046.table
  base := (-7368433353203799076682451663546287653/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-197140076887983951708926964840000000000000)
      constant := (3046810911800058608357837874548083411123000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12582303026121758759/6250000000000000000)
  centralHi := (40263369683589628029/20000000000000000000)
  directionLo := (203541411512307626117/100000000000000000000)
  directionHi := (101770705756153813059/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree047.table
  base := (-1459218275580258118542318200775332328179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-175492780012162583991169871721300000000000000)
      constant := (2739157911829874766376668966411822059894575490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree047.table
  base := (-912012276427646125072764080385806044029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-201297688720572725412649715760000000000000)
      constant := (3180274516612287838083266485932221964829912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203541411512307626117/100000000000000000000)
  centralHi := (101770705756153813059/50000000000000000000)
  directionLo := (205741923155952837253/100000000000000000000)
  directionHi := (102870961577976418627/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree048.table
  base := (-7215025977324067581819413727932242522669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-19901793191584855585996027683120000000000000)
      constant := (317399689293649420537285344611323762095005942) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree048.table
  base := (-7215031106638526331668727191223026603741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-68485100184387166372124155560000000000000)
      constant := (1105529483437747676759942560826330920188777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205741923155952837253/100000000000000000000)
  centralHi := (102870961577976418627/50000000000000000000)
  directionLo := (207919146995646962107/100000000000000000000)
  directionHi := (51979786748911740527/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree049.table
  base := (-7125229335812887234742942129978057482807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-26105642490909259508108375224980000000000000)
      constant := (425213231386558175495168142977729882814496862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree049.table
  base := (-7125233184267106561900171924537024626873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-209612912385750272820095217600000000000000)
      constant := (3455752702594223065519900574639166778358143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207919146995646962107/100000000000000000000)
  centralHi := (51979786748911740527/25000000000000000000)
  directionLo := (105036903551662374781/50000000000000000000)
  directionHi := (210073807103324749563/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree050.table
  base := (-1756675620077098933285991521347906128579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-186362856148465932839553004001640000000000000)
      constant := (3098844151867207247878464376407661284605359592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree050.table
  base := (-7026705366552640071237407982723676544081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-213770524218339046523817968520000000000000)
      constant := (3597767265155016370383836512155486911103271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105036903551662374781/50000000000000000000)
  centralHi := (210073807103324749563/100000000000000000000)
  directionLo := (6631455962162305657/3125000000000000000)
  directionHi := (8488263631567751241/4000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree051.table
  base := (-3459723122610532428478554999607503606733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-21109579428951894346927486825380000000000000)
      constant := (358183532611466057564812131073927363637722988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree051.table
  base := (-21623276278029524242246063682240427433/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-72642712016975940075846906480000000000000)
      constant := (1247544043732118018930363583305049189664320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6631455962162305657/3125000000000000000)
  centralHi := (8488263631567751241/4000000000000000000)
  directionLo := (107159075581422161829/50000000000000000000)
  directionHi := (214318151162844323659/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree052.table
  base := (-1700865330058590647268508490860696724009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-193609573572668165405141758855200000000000000)
      constant := (3350915539139161670232517412806911157619266232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree052.table
  base := (-136069258834474374294014263441856813263/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-222085747883516593931263470360000000000000)
      constant := (3890347295046380422896054391371164434031650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107159075581422161829/50000000000000000000)
  centralHi := (214318151162844323659/100000000000000000000)
  directionLo := (108204554734709800683/50000000000000000000)
  directionHi := (216409109469419601367/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree053.table
  base := (-3339374142825523068294143363107877085507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-197232932284769281687936136281980000000000000)
      constant := (3480635384168665417616180485869614343390490868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree053.table
  base := (-1669687375082481382308130219998726858229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-226243359716105367634986221280000000000000)
      constant := (4040912751885465215420684685880045833103756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108204554734709800683/50000000000000000000)
  centralHi := (216409109469419601367/100000000000000000000)
  directionLo := (109240028612265892517/50000000000000000000)
  directionHi := (43696011444906357007/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree054.table
  base := (-6545307638558029018059814095243704075607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-22317365666318933107858945967640000000000000)
      constant := (401423480516203315635996616559095053005314626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree054.table
  base := (-409081784260458566926554794412007724173/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-76800323849564713779569657400000000000000)
      constant := (1398109499181065004845861738188223629239696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109240028612265892517/50000000000000000000)
  centralHi := (43696011444906357007/20000000000000000000)
  directionLo := (55132889542179204951/25000000000000000000)
  directionHi := (44106311633743363961/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree055.table
  base := (-3201569906111186718693896503955588851879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-204479649708971514253524891135540000000000000)
      constant := (3747443357131380999781332935764676071387568996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree055.table
  base := (-6403140493148541525520126193763108789607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-234558583381282915042431723120000000000000)
      constant := (4350594528348356526572374867656132020893537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/25000000000000000000)
  centralHi := (44106311633743363961/20000000000000000000)
  directionLo := (222564150059729020029/100000000000000000000)
  directionHi := (22256415005972902003/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree056.table
  base := (-6252245190495480209159312565409968468491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-29729001203010375790902752651760000000000000)
      constant := (554933068368329496446011190397545095756731206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree056.table
  base := (-156306142501589561956086592872669819113/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-238716195213871688746154474040000000000000)
      constant := (4509710841017839359260726895685838865119320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222564150059729020029/100000000000000000000)
  centralHi := (22256415005972902003/10000000000000000000)
  directionLo := (112289173159411303957/50000000000000000000)
  directionHi := (44915669263764521583/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree057.table
  base := (-23799312963025582017633713157617619189/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-23525151903685971868790405109900000000000000)
      constant := (447119520694083157313355727651670202528077312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree057.table
  base := (-761578062468323632444588753397237798303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-80957935682153487483292408320000000000000)
      constant := (1557225810858045450142528303958466292840728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112289173159411303957/50000000000000000000)
  centralHi := (44915669263764521583/20000000000000000000)
  directionLo := (226574637545300888129/100000000000000000000)
  directionHi := (22657463754530088813/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree058.table
  base := (-2962138455402859143243493088432154999893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-215349725845274863101908023415880000000000000)
      constant := (4166075977640474614565623205958191107221698732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree058.table
  base := (-5924277195906209555720270009254388086927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-247031418879049236153599975880000000000000)
      constant := (4836494300283869665496605272316710507217657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226574637545300888129/100000000000000000000)
  centralHi := (22657463754530088813/10000000000000000000)
  directionLo := (228553492911991869479/100000000000000000000)
  directionHi := (5713837322799796737/2500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree059.table
  base := (-1436800964269864740484531820458878427283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-218973084557375979384702400842660000000000000)
      constant := (4310532350459287073490196274904464692176910184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree059.table
  base := (-2873602035118542774507767200390832775481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-251189030711638009857322726800000000000000)
      constant := (5004161441611787530227255460352965010041342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228553492911991869479/100000000000000000000)
  centralHi := (5713837322799796737/2500000000000000000)
  directionLo := (28814420181612019929/12500000000000000000)
  directionHi := (230515361452896159433/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree060.table
  base := (-1112281045388369505698159988707386865929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-24732938141053010629721864252160000000000000)
      constant := (495271644729245724143587135808600423921253110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree060.table
  base := (-2780702693132644709025215008892440208539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-85115547514742261187015159240000000000000)
      constant := (1724892951395385097737354711546645358748766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28814420181612019929/12500000000000000000)
  centralHi := (230515361452896159433/100000000000000000000)
  directionLo := (11623033662650944443/5000000000000000000)
  directionHi := (232460673253018888861/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree061.table
  base := (-1073376254641531016336354321043694774893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-226219801981578211950291155696220000000000000)
      constant := (4606813331945404293015516188112490754384496830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree061.table
  base := (-670860174032518813061281977057108336871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-259504254376815557264768228640000000000000)
      constant := (5348046535772548990376043604571888199745288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11623033662650944443/5000000000000000000)
  centralHi := (232460673253018888861/100000000000000000000)
  directionLo := (234389840549317022427/100000000000000000000)
  directionHi := (58597460137329255607/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree062.table
  base := (-5163632234519772945894363050472944115929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-229843160693679328233085533123000000000000000)
      constant := (4758637936711518129326937372029565769607755598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree062.table
  base := (-322727020216032859505285877130351067077/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-263661866209404330968490979560000000000000)
      constant := (5524264484253854909225447810013229446340912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234389840549317022427/100000000000000000000)
  centralHi := (58597460137329255607/25000000000000000000)
  directionLo := (118151629375372671107/50000000000000000000)
  directionHi := (47260651750149068443/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree063.table
  base := (-4951658337344794697853331994427564995893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-3705817768345721341521903342060000000000000)
      constant := (77982835159743828673246137258507126810517482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree063.table
  base := (-4951658403766758702082699946620080384369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-89273159347331034890737910160000000000000)
      constant := (1901110899204953985963010971160139758846893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118151629375372671107/50000000000000000000)
  centralHi := (47260651750149068443/20000000000000000000)
  directionLo := (119100653692275291399/50000000000000000000)
  directionHi := (238201307384550582799/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree064.table
  base := (-946191959503909249416709952452215945369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-237089878117881560798674287976560000000000000)
      constant := (5069655365289120800208415585302371549128304390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree064.table
  base := (-946191969422806470495039772464807606149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-271977089874581878375936481400000000000000)
      constant := (5885251173930261489384883827199083657723295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119100653692275291399/50000000000000000000)
  centralHi := (238201307384550582799/100000000000000000000)
  directionLo := (120042175487614142607/50000000000000000000)
  directionHi := (48016870195045657043/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree065.table
  base := (-4501536821462815895826827005740106457689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-240713236829982677081468665403340000000000000)
      constant := (5228848185748744569165468693125110034938864718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree065.table
  base := (-2250768429241974494278668104557031657331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-276134701707170652079659232320000000000000)
      constant := (6070019911355183083145343162317973430168042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120042175487614142607/50000000000000000000)
  centralHi := (48016870195045657043/20000000000000000000)
  directionLo := (241952739861907837257/100000000000000000000)
  directionHi := (120976369930953918629/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree066.table
  base := (-4263389607136666640893958243395994077731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-27148510615787088151584782536680000000000000)
      constant := (598944119430145517468553542651784733223441258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree066.table
  base := (-4263389634765585326196370500342334983577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-93430771179919808594460661080000000000000)
      constant := (2085879636039208349575868530738972995049269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241952739861907837257/100000000000000000000)
  centralHi := (120976369930953918629/50000000000000000000)
  directionLo := (60951702739839174129/25000000000000000000)
  directionHi := (243806810959356696517/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree067.table
  base := (-2008259172409850825926810446287884252283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-247959954254184909647057420256900000000000000)
      constant := (5554602031146384512402918996186328549610755092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree067.table
  base := (-4016518365434497126303778276169842513477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-284449925372348199487104734160000000000000)
      constant := (6448108162512307384283467828034471417378707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60951702739839174129/25000000000000000000)
  centralHi := (243806810959356696517/100000000000000000000)
  directionLo := (245646888467285372691/100000000000000000000)
  directionHi := (61411722116821343173/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree068.table
  base := (-940230804434607564016354722649996613501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-251583312966286025929851797683680000000000000)
      constant := (5721163053119517103682699494031457307528116248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree068.table
  base := (-1880461616558183814293512297081345819613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-288607537204936973190827485080000000000000)
      constant := (6641427672895598940655562684252535775246966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245646888467285372691/100000000000000000000)
  centralHi := (61411722116821343173/25000000000000000000)
  directionLo := (247473284532182152663/100000000000000000000)
  directionHi := (30934160566522769083/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree069.table
  base := (-437075550323865132355074564901916795447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-28356296853154126912516241678940000000000000)
      constant := (654464459932008684718595857810327075091325968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree069.table
  base := (-3496604414059877037965622967535103811327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-97588383012508582298183412000000000000000)
      constant := (2279199145893753865333204846417394688566019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247473284532182152663/100000000000000000000)
  centralHi := (30934160566522769083/12500000000000000000)
  directionLo := (31160787483187963281/12500000000000000000)
  directionHi := (249286299865503706249/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree070.table
  base := (-1611781034994054059834197811145238464149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-36975718627212608356491507505320000000000000)
      constant := (865950469799679727741811867602022599163310068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree070.table
  base := (-805890519634984865914356626635517389849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-296922760870114520598272986920000000000000)
      constant := (7036617455336821123332662715041121373965436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31160787483187963281/12500000000000000000)
  centralHi := (249286299865503706249/100000000000000000000)
  directionLo := (125543112160844252357/50000000000000000000)
  directionHi := (50217244864337700943/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree071.table
  base := (-1176718553932643382279833301355448099/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-262453389102589374778234929964020000000000000)
      constant := (6235582499439567862976517763923916132475345000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree071.table
  base := (-2941796391206993222953922299952696267039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-301080372702703294301995737840000000000000)
      constant := (7238487724380423577799083827820425733596649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125543112160844252357/50000000000000000000)
  centralHi := (50217244864337700943/20000000000000000000)
  directionLo := (252873337439139136431/100000000000000000000)
  directionHi := (15804583589946196027/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree072.table
  base := (-26513075066421055644540357134145490479/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-29564083090521165673447700821200000000000000)
      constant := (712440863405248031468394890482848367739752200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree072.table
  base := (-2651307511394015325029988700034113822743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-101745994845097356001906162920000000000000)
      constant := (2481069414459357388772101324139897658531771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252873337439139136431/100000000000000000000)
  centralHi := (15804583589946196027/6250000000000000000)
  directionLo := (254647908947032537229/100000000000000000000)
  directionHi := (25464790894703253723/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree073.table
  base := (-2352095589848805659137400091085350046221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-269700106526791607343823684817580000000000000)
      constant := (6590809100994892315989365397889079491333097702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree073.table
  base := (-1176047796694988158792712769906839611409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-309395596367880841709441239680000000000000)
      constant := (7650779010941166153955024950341676886994638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254647908947032537229/100000000000000000000)
  centralHi := (25464790894703253723/10000000000000000000)
  directionLo := (256410199240559891931/100000000000000000000)
  directionHi := (64102549810139972983/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree074.table
  base := (-63880024501495330972429433034369872903/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-273323465238892723626618062244360000000000000)
      constant := (6772106489295053787281792210847841502364671552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree074.table
  base := (-2044160786686275250150906877113617271747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-313553208200469615413163990600000000000000)
      constant := (7861200025724282949269470695065977444554277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256410199240559891931/100000000000000000000)
  centralHi := (64102549810139972983/25000000000000000000)
  directionLo := (129080229913483524363/50000000000000000000)
  directionHi := (258160459826967048727/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree075.table
  base := (-431875808558907681928276841617135065627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-30771869327888204434379159963460000000000000)
      constant := (772873326044081705595229311250649747488467944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree075.table
  base := (-215937904525136162038899535063620848677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-105903606677686129705628913840000000000000)
      constant := (2691490428807719652565792778158473099631752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129080229913483524363/50000000000000000000)
  centralHi := (258160459826967048727/100000000000000000000)
  directionLo := (129949466872279351317/50000000000000000000)
  directionHi := (51979786748911740527/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree076.table
  base := (-56084923240860127351141619997673833537/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-280570182663094956192206817097920000000000000)
      constant := (7142069435183779928437460830787701627734582350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree076.table
  base := (-701061541242693393906316850704848025311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-321868431865647162820609492440000000000000)
      constant := (8290592791772835464253030809007312735544402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129949466872279351317/50000000000000000000)
  centralHi := (51979786748911740527/20000000000000000000)
  directionLo := (13081292797832135631/5000000000000000000)
  directionHi := (261625855956642712621/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree077.table
  base := (-534010230411676896916326194354400491907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-40599077339313724639285884932100000000000000)
      constant := (1047247855796186049109796366326289219684354924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree077.table
  base := (-1068020461913474717209256489357065793769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-326026043698235936524332243360000000000000)
      constant := (8509564540545943706003441782515786407856079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13081292797832135631/5000000000000000000)
  centralHi := (261625855956642712621/100000000000000000000)
  directionLo := (13167072686111120577/5000000000000000000)
  directionHi := (263341453722222411541/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree078.table
  base := (-362597753024323917726241902674866419223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-31979655565255243195310619105720000000000000)
      constant := (835761844390472459664110939121341535636490628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree078.table
  base := (-362597753430150251626295831654363283097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-110061218510274903409351664760000000000000)
      constant := (2910462177183703052059949170610073820301418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13167072686111120577/5000000000000000000)
  centralHi := (263341453722222411541/100000000000000000000)
  directionLo := (132522973472546312757/50000000000000000000)
  directionHi := (53009189389018525103/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree079.table
  base := (-5838255394734736682703314261642626303/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-291440258799398305040589949378260000000000000)
      constant := (7715434260986075274896314083905304173274034304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree079.table
  base := (-186824172933621540133771178983234903517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-334341267363413483931777745200000000000000)
      constant := (8956058763631459404373323868738301771736694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132522973472546312757/50000000000000000000)
  centralHi := (53009189389018525103/20000000000000000000)
  directionLo := (266739548502857561773/100000000000000000000)
  directionHi := (133369774251428780887/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree080.table
  base := (-13379103348037153199672307345193644891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-295063617511499421323384326805040000000000000)
      constant := (7911467973997461954705561996721893852846855242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree080.table
  base := (-13379103797766216375172264922096560759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-338498879196002257635500496120000000000000)
      constant := (9183581235663223276670781280015701130953169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266739548502857561773/100000000000000000000)
  centralHi := (133369774251428780887/50000000000000000000)
  directionLo := (268422464557264186859/100000000000000000000)
  directionHi := (13421123227863209343/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree081.table
  base := (355612098350652505554766726213475710093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-33187441802622281956242078247980000000000000)
      constant := (901106415287241149559865927903955285576302026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree081.table
  base := (88903024503991217614953796920208786149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-114218830342863677113074415680000000000000)
      constant := (3137984648851470428703512471603042505433788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268422464557264186859/100000000000000000000)
  centralHi := (13421123227863209343/5000000000000000000)
  directionLo := (54018978969426364173/20000000000000000000)
  directionHi := (135047447423565910433/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree082.table
  base := (366662570941822068900103421097447574927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-302310334935701653888973081658600000000000000)
      constant := (8310903550812918098274675108065563077699541052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree082.table
  base := (733325141634607723723897309205914729519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-346814102861179805042945997960000000000000)
      constant := (9647176895243569350583970568902853232565671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54018978969426364173/20000000000000000000)
  centralHi := (135047447423565910433/50000000000000000000)
  directionLo := (271757032965056200211/100000000000000000000)
  directionHi := (67939258241264050053/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree083.table
  base := (279939978141461253163997086373827263803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-305933693647802770171767459085380000000000000)
      constant := (8514305412770334945315476590852056763280272856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree083.table
  base := (223951982476113550637117102738292697981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-350971714693768578746668748880000000000000)
      constant := (9883250080698599118778997345023223171409145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271757032965056200211/100000000000000000000)
  centralHi := (67939258241264050053/25000000000000000000)
  directionLo := (136704533309486566889/50000000000000000000)
  directionHi := (273409066618973133779/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree084.table
  base := (151491629885152590809716417418629284519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-4913604005712760102453362484320000000000000)
      constant := (138415290834475728390424821741547472898493940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree084.table
  base := (757458149356851881212687299930201510599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-118376442175452450816797166600000000000000)
      constant := (3374057833971879773309280732119581209063594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136704533309486566889/50000000000000000000)
  centralHi := (273409066618973133779/100000000000000000000)
  directionLo := (55010235575916428177/20000000000000000000)
  directionHi := (137525588939791070443/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree085.table
  base := (239849274026974144493070597481510223553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-313180411072005002737356213938940000000000000)
      constant := (8928477279356355322180530396786540825236509712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree085.table
  base := (1918794192113285804511313866216126032877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-359286938358946126154114250720000000000000)
      constant := (10363947157918003384508117566595945134295893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55010235575916428177/20000000000000000000)
  centralHi := (137525588939791070443/50000000000000000000)
  directionLo := (276683543414553267623/100000000000000000000)
  directionHi := (34585442926819158453/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree086.table
  base := (582848371760495115491975204486633790137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-316803769784106119020150591365720000000000000)
      constant := (9139247282285103149023176435242199596104430024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree086.table
  base := (466278697393149893877198339186257639879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-363444550191534899857837001640000000000000)
      constant := (10608571047755169232829306751183381593794555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276683543414553267623/100000000000000000000)
  centralHi := (34585442926819158453/12500000000000000000)
  directionLo := (17394145919398117393/6250000000000000000)
  directionHi := (278306334710369878289/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree087.table
  base := (2752714080514530455585042892085545109853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-35603014277356359478104996532500000000000000)
      constant := (1039163703393562719413002326881774450786890346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree087.table
  base := (2752714080457847813759920665461855997249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-122534054008041224520519917520000000000000)
      constant := (3618681723500605880800601454436385567991747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17394145919398117393/6250000000000000000)
  centralHi := (278306334710369878289/100000000000000000000)
  directionLo := (34989964785324492687/12500000000000000000)
  directionHi := (279919718282595941497/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree088.table
  base := (3182755872516989594227729640135802689857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-324050487208308351585739346219280000000000000)
      constant := (9568155423332514891041157058175238001752084866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree088.table
  base := (1591377936237423955377733414298736197609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-371759773856712447265282503480000000000000)
      constant := (11106369525256916016883711697457377251556962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34989964785324492687/12500000000000000000)
  centralHi := (279919718282595941497/100000000000000000000)
  directionLo := (281523855875297579443/100000000000000000000)
  directionHi := (70380963968824394861/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree089.table
  base := (3621518765534783151659887786620789099987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-327673845920409467868533723646060000000000000)
      constant := (9786293559882383703818722834299270823875696806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree089.table
  base := (1810759382751728095430245131004569229263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-375917385689301220969005254400000000000000)
      constant := (11359544111142844714149419494318082246126734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281523855875297579443/100000000000000000000)
  centralHi := (70380963968824394861/25000000000000000000)
  directionLo := (11324756186011795657/4000000000000000000)
  directionHi := (141559452325147445713/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree090.table
  base := (4069002664562472107045424302595637459813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-36810800514723398239036455674760000000000000)
      constant := (1111876415493057526455813484871589352239555066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree090.table
  base := (4069002664539187415716196553731702053881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-126691665840629998224242668440000000000000)
      constant := (3871856309101521122351232868061195106161643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11324756186011795657/4000000000000000000)
  centralHi := (141559452325147445713/50000000000000000000)
  directionLo := (28470501736687082339/10000000000000000000)
  directionHi := (284705017366870823391/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree091.table
  base := (4525207477015222716179256552865960039009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-47845794763515957204874639785660000000000000)
      constant := (1461419708751854083375778957264594998684236206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree091.table
  base := (4525207476997917789762023910950383540133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-384232609354478768376450756240000000000000)
      constant := (11874443972908814861436503970918553451861197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28470501736687082339/10000000000000000000)
  centralHi := (284705017366870823391/100000000000000000000)
  directionLo := (8946323204766209639/3125000000000000000)
  directionHi := (286282342552518708449/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree092.table
  base := (998026622528848759593902270527119536663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-338543922056712816716916855926400000000000000)
      constant := (10455444224642371336007609555981941374410154470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree092.table
  base := (4990133112631384500256179821841329825377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-388390221187067542080173507160000000000000)
      constant := (12136169247143364831983159461916571968428393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8946323204766209639/3125000000000000000)
  centralHi := (286282342552518708449/100000000000000000000)
  directionLo := (287851024665268667633/100000000000000000000)
  directionHi := (143925512332634333817/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree093.table
  base := (5463779483455967360396793468688665281589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-38018586752090436999967914817020000000000000)
      constant := (1187045169875244783612571329985818402778361498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree093.table
  base := (2731889741723206362695506810619714752091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-130849277673218771927965419360000000000000)
      constant := (4133581583072091568432465407063718288512546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287851024665268667633/100000000000000000000)
  centralHi := (143925512332634333817/50000000000000000000)
  directionLo := (289411204248094993697/100000000000000000000)
  directionHi := (144705602124047496849/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree094.table
  base := (1189229300726953181776351795278633287843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-345790639480915049282505610779960000000000000)
      constant := (10913824873286269282095079110449708955194488670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree094.table
  base := (5946146503627667493569437500425341909981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-396705444852245089487619009000000000000000)
      constant := (12668170478355206466634840458463828077189829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289411204248094993697/100000000000000000000)
  centralHi := (144705602124047496849/50000000000000000000)
  directionLo := (18185188629741977271/6250000000000000000)
  directionHi := (290963018075871636337/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree095.table
  base := (6437234089469015219052480401874538999091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-349413998193016165565299988206740000000000000)
      constant := (11146699257205067151660356617426355090574784358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree095.table
  base := (6437234089463742189251565591312403199813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-400863056684833863191341759920000000000000)
      constant := (12938446433806757456455633200921811628798317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18185188629741977271/6250000000000000000)
  centralHi := (290963018075871636337/100000000000000000000)
  directionLo := (292506599295310688621/100000000000000000000)
  directionHi := (146253299647655344311/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree096.table
  base := (108391283738755077546566946553238850781/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-39226372989457475760899373959280000000000000)
      constant := (1264669964442803733198430742579197226648885888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree096.table
  base := (6937042159276408341585510197886832497099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-135006889505807545631688170280000000000000)
      constant := (4403857538278607872840702486433660497491297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292506599295310688621/100000000000000000000)
  centralHi := (146253299647655344311/50000000000000000000)
  directionLo := (18377629847393068317/6250000000000000000)
  directionHi := (294042077558289093073/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree097.table
  base := (3722785316677885846755527007945755050761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-356660715617218398130888743060300000000000000)
      constant := (11619816140994007437148129923148741807185881636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree097.table
  base := (3722785316676431437915868438305016199647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-409178280350011410598787261760000000000000)
      constant := (13487549020724989725161607423609490291593646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/6250000000000000000)
  centralHi := (294042077558289093073/100000000000000000000)
  directionLo := (147784789574470708751/50000000000000000000)
  directionHi := (295569579148941417503/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree098.table
  base := (1592563886776595915130067172195964280113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-51469153475617073487669017212440000000000000)
      constant := (1694294091373387718195561481501171117468240710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree098.table
  base := (7962819433880819465389300239674072373219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-413335892182600184302510012680000000000000)
      constant := (13766375650773945199434724585357066651358971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147784789574470708751/50000000000000000000)
  centralHi := (295569579148941417503/100000000000000000000)
  directionLo := (148544613552435646717/50000000000000000000)
  directionHi := (59417845420974258687/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree099.table
  base := (4244394242443952054034210676641188584191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-40434159226824514521830833101540000000000000)
      constant := (1344750797249030156021858088571470056662512924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree099.table
  base := (8488788484886300158217569490738018247993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-139164501338396319335410921200000000000000)
      constant := (4682684168099641413257697755792214054743979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148544613552435646717/50000000000000000000)
  centralHi := (59417845420974258687/20000000000000000000)
  directionLo := (59720228266562156157/20000000000000000000)
  directionHi := (149300570666405390393/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree100.table
  base := (902347771217518305795624275139741894173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-367530791753521746979271875340640000000000000)
      constant := (12347911747287716782227468823322592711559452740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree100.table
  base := (1804695542434798438878952115155746172079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-421651115847777731709955514520000000000000)
      constant := (14332579580632169031337417413182008577743555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59720228266562156157/20000000000000000000)
  centralHi := (149300570666405390393/50000000000000000000)
  directionLo := (300105438719035356517/100000000000000000000)
  directionHi := (150052719359517678259/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree101.table
  base := (9566887043270927061728312203962530680477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-371154150465622863262066252767420000000000000)
      constant := (12595522355177752427693026846482169568541626426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree101.table
  base := (4783443521635021491984249249445965365631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-425808727680366505413678265440000000000000)
      constant := (14619956879121414900818125647810027376581358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300105438719035356517/100000000000000000000)
  centralHi := (150052719359517678259/50000000000000000000)
  directionLo := (37700279154352784071/12500000000000000000)
  directionHi := (301602233234822272569/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree102.table
  base := (2529754101841957480072107007612706961331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-41641945464191553282762292243800000000000000)
      constant := (1427287666483256660442774579742437630159575768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree102.table
  base := (10119016407367173658651813497215605694269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-143322113170985093039133672120000000000000)
      constant := (4970061466376465446133545081131646817082807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37700279154352784071/12500000000000000000)
  centralHi := (301602233234822272569/100000000000000000000)
  directionLo := (303091636037221554079/100000000000000000000)
  directionHi := (1894322725232634713/625000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree103.table
  base := (10679865735272485619533355432255400686013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-378400867889825095827655007620980000000000000)
      constant := (13098111676253132074163350459090558370645571194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree103.table
  base := (5339932867635999257319773657082362060607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-434123951345544052821123767280000000000000)
      constant := (15203262140033372872750699775627482517090926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303091636037221554079/100000000000000000000)
  centralHi := (1894322725232634713/625000000000000000)
  directionLo := (304573755565391789879/100000000000000000000)
  directionHi := (7614343889134794747/2500000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree104.table
  base := (11249434959354805598812886936803740788967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-382024226601926212110449385047760000000000000)
      constant := (13353090388352371175233723223790748094382820046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree104.table
  base := (11249434959354444082666673795782902310017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-438281563178132826524846518200000000000000)
      constant := (15499190101224673842644934009122046120790153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304573755565391789879/100000000000000000000)
  centralHi := (7614343889134794747/2500000000000000000)
  directionLo := (15302434881636849589/5000000000000000000)
  directionHi := (306048697632736991781/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree105.table
  base := (2365544802699887165072024345561991250709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-6121390243079798863384821626580000000000000)
      constant := (216040081494003231220380727827029054487946670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree105.table
  base := (11827724013499167542196851474471899821177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-147479725003573866742856423040000000000000)
      constant := (5265989427369420387566170290223415699463531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15302434881636849589/5000000000000000000)
  centralHi := (306048697632736991781/100000000000000000000)
  directionLo := (19219785344691629127/6250000000000000000)
  directionHi := (307516565515066066033/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree106.table
  base := (3103683208264769713951532916684532142647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-389270944026128444676038139901320000000000000)
      constant := (13870415913049459002008675795463107264593327544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree106.table
  base := (6207366416529439889557692714475136018149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-446596786843310373932292020040000000000000)
      constant := (16099596682102309230884398105980552448326682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19219785344691629127/6250000000000000000)
  centralHi := (307516565515066066033/100000000000000000000)
  directionLo := (308977460034982757107/100000000000000000000)
  directionHi := (77244365008745689277/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree107.table
  base := (2602092270961926262939320381756729449391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-392894302738229560958832517328100000000000000)
      constant := (14132762724632264548013436699633519591846328790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree107.table
  base := (13010461354809483604858598324674029550609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-450754398675899147636014770960000000000000)
      constant := (16404075300637801172505522619042066265955481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308977460034982757107/100000000000000000000)
  centralHi := (77244365008745689277/25000000000000000000)
  directionLo := (310431479642701206721/100000000000000000000)
  directionHi := (155215739821350603361/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree108.table
  base := (13614909516907052126899554083085022628597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-44057517938925630804625210528320000000000000)
      constant := (1599729507597744689649318991256240989958422554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree108.table
  base := (6807454758453471269681507148123814486191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-151637336836162640446579173960000000000000)
      constant := (5570468045719380219747104375688742886917146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310431479642701206721/100000000000000000000)
  centralHi := (155215739821350603361/50000000000000000000)
  directionLo := (311878720493470443161/100000000000000000000)
  directionHi := (155939360246735221581/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree109.table
  base := (7114038629422940717137811823365693609971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-400141020162431793524421272181660000000000000)
      constant := (14664824443811479638146068184739428751751899596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree109.table
  base := (2845615451769160027386989970703401059593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-459069622341076695043460272800000000000000)
      constant := (17021583191118778583080526478641653047681685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311878720493470443161/100000000000000000000)
  centralHi := (155939360246735221581/50000000000000000000)
  directionLo := (31331927652178010773/10000000000000000000)
  directionHi := (313319276521780107731/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree110.table
  base := (1484996452141933443185452360869229783371/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-403764378874532909807215649608440000000000000)
      constant := (14934539350457613384138174351798499460203989980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree110.table
  base := (7424982260709637063267184560127645865271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-463227234173665468747183023720000000000000)
      constant := (17334612461986853903583802350882297625574878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31331927652178010773/10000000000000000000)
  centralHi := (313319276521780107731/100000000000000000000)
  directionLo := (314753239512509472599/100000000000000000000)
  directionHi := (1573766197562547363/500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree111.table
  base := (15480571246680898397017420820740252027439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-45265304176292669565556669670580000000000000)
      constant := (1689634476428680447425337902772527902288201198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree111.table
  base := (1935071405835106708366990475557825029313/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-155794948668751414150301924880000000000000)
      constant := (5883497316413616007726704203053387800703512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314753239512509472599/100000000000000000000)
  centralHi := (1573766197562547363/500000000000000000)
  directionLo := (19761293698073265587/6250000000000000000)
  directionHi := (316180699169172249393/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree112.table
  base := (16119897377907364976636394038890835923103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-58715870899819306053257772066000000000000000)
      constant := (2211619607937534676901219866481062207936798802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree112.table
  base := (16119897377907331801771005145016327536511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-471542457838843016154628525560000000000000)
      constant := (17969221652370252079262139774625146947828599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19761293698073265587/6250000000000000000)
  centralHi := (316180699169172249393/100000000000000000000)
  directionLo := (39700217897425097133/12500000000000000000)
  directionHi := (63520348635880155413/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree113.table
  base := (670717714382529334379669550791779901567/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-414634455010836258655598781888780000000000000)
      constant := (15758420253130628713140206158774343721465971150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree113.table
  base := (4191985714890802189170704772743973941973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-475700069671431789858351276480000000000000)
      constant := (18290801570875246573860672700818783061911028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39700217897425097133/12500000000000000000)
  centralHi := (63520348635880155413/20000000000000000000)
  directionLo := (63803291455560972453/20000000000000000000)
  directionHi := (159508228638902431133/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree114.table
  base := (17424707637266423310673106753405988994283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-46473090413659708326488128812840000000000000)
      constant := (1781995475570010777602036006742804082292957606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree114.table
  base := (8712353818633202533193540179641889322647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-159952560501340187854024675800000000000000)
      constant := (6205077234755464263929384273397851335935882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63803291455560972453/20000000000000000000)
  centralHi := (159508228638902431133/50000000000000000000)
  directionLo := (64084985061266556163/20000000000000000000)
  directionHi := (20026557831645798801/6250000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree115.table
  base := (723607666310209607832497607891448195043/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-421881172435038491221187536742340000000000000)
      constant := (16319954336138356262135279128343732894306283350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree115.table
  base := (18090191657755226667728188284728812462653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-484015293336609337265796778320000000000000)
      constant := (18942512052064335486476179726762559312163877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64084985061266556163/20000000000000000000)
  centralHi := (20026557831645798801/6250000000000000000)
  directionLo := (80456807318063673503/25000000000000000000)
  directionHi := (321827229272254694013/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree116.table
  base := (18764394868856537089195953775746505941733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-425504531147139607503981914169120000000000000)
      constant := (16604405420741256063994755333834515764165476554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree116.table
  base := (9382197434428263529452242477829738737999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-488172905169198110969519529240000000000000)
      constant := (19272642613799516339408538499320935297283982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80456807318063673503/25000000000000000000)
  centralHi := (321827229272254694013/100000000000000000000)
  directionLo := (323223449403881950843/100000000000000000000)
  directionHi := (80805862350970487711/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree117.table
  base := (155578537755640174828150260345547414377/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-47680876651026747087419587955100000000000000)
      constant := (1876812503725893690556758517691051602435064250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree117.table
  base := (194473172194550144171794724744827501293/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-164110172333928961557747426720000000000000)
      constant := (6535207796337299241393533552263448250387900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323223449403881950843/100000000000000000000)
  centralHi := (80805862350970487711/25000000000000000000)
  directionLo := (6492273284082588041/2000000000000000000)
  directionHi := (324613664204129402051/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree118.table
  base := (20138958659463659711478312822720515815651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-432751248571341840069570669022680000000000000)
      constant := (17180675674116126833121264957131295454544637638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree118.table
  base := (20138958659463654198658698008258388236077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-496488128834375658376965031080000000000000)
      constant := (19941454377250696329897316123674325494124693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6492273284082588041/2000000000000000000)
  centralHi := (324613664204129402051/100000000000000000000)
  directionLo := (325997950502021912877/100000000000000000000)
  directionHi := (162998975251010956439/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree119.table
  base := (10419659569897562155581391190634065333529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (14193)
      previous := (0)
      next := (7353)
      square := (392894318179639115001799961940000000000000)
      linear := (-62339229611920422336052149492780000000000000)
      constant := (2496070691728693103106370665566283060176443772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree119.table
  base := (20839319139795120224603140986328484278941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-500645740666964432080687782000000000000000)
      constant := (20280135578074126220950033714836956358510469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (325997950502021912877/100000000000000000000)
  centralHi := (162998975251010956439/50000000000000000000)
  directionLo := (8184409587556017471/2500000000000000000)
  directionHi := (327376383502240698841/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree120.table
  base := (10774199306167126313918317699475728073279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-48888662888393785848351047097360000000000000)
      constant := (1974085559678364412976718324735475184321264156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree120.table
  base := (5387099653083562399687145490936356386777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-168267784166517735261470177640000000000000)
      constant := (6873888997016383643757458485091236276641324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8184409587556017471/2500000000000000000)
  centralHi := (327376383502240698841/100000000000000000000)
  directionLo := (3287490368327998963/1000000000000000000)
  directionHi := (328749036832799896301/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree121.table
  base := (11133098514955730626664887823020691147977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-443621324707645188917953801303020000000000000)
      constant := (18063501258754978665164821524225591492665282852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree121.table
  base := (22266197029911459008225791250777910352947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-508960964332141979488133283840000000000000)
      constant := (20966048615751244211048518277777001193176523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3287490368327998963/1000000000000000000)
  centralHi := (328749036832799896301/100000000000000000000)
  directionLo := (330115982590938892169/100000000000000000000)
  directionHi := (33011598259093889217/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree122.table
  base := (5748178586569270927268471186127341620409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-447244683419746305200748178729800000000000000)
      constant := (18362688506682818714360789152498135351131226568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree122.table
  base := (22992714346277082045155480668645023083883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-513118576164730753191856034760000000000000)
      constant := (21313280451764159062607548588737805207754947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330115982590938892169/100000000000000000000)
  centralHi := (33011598259093889217/10000000000000000000)
  directionLo := (20717330711706959497/6250000000000000000)
  directionHi := (331477291387311351953/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree123.table
  base := (4745590103215318077527519464960948470329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-50096449125760824609282506239620000000000000)
      constant := (2073814642280975067594953069903712782754150890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree123.table
  base := (11863975258038294577267693040162637366421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-172425395999106508965192928560000000000000)
      constant := (7221120832893234906651482003640975824198526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20717330711706959497/6250000000000000000)
  centralHi := (331477291387311351953/100000000000000000000)
  directionLo := (8320825809713689539/2500000000000000000)
  directionHi := (332833032388547581561/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree124.table
  base := (24471905494826654587635469429600562178899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-454491400843948537766336933583360000000000000)
      constant := (18968431079939740699790589299998169262576100262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree124.table
  base := (12235952747413326836931481816249582860717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-521433799829908300599301536600000000000000)
      constant := (22016294756097531243126687649652492491492906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8320825809713689539/2500000000000000000)
  centralHi := (332833032388547581561/100000000000000000000)
  directionLo := (41772909169782852053/12500000000000000000)
  directionHi := (13367330934330512657/4000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree125.table
  base := (12612289619446014932376567069172909342959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-458114759556049654049131311010140000000000000)
      constant := (19274986404569337402393856720477064108728817084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree125.table
  base := (788268101215375912114321092187343890589/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-525591411662497074303024287520000000000000)
      constant := (22372077223624921414384954059549955040489632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41772909169782852053/12500000000000000000)
  centralHi := (13367330934330512657/4000000000000000000)
  directionLo := (167764040348290116787/50000000000000000000)
  directionHi := (13421123227863209343/4000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree126.table
  base := (25985971705463205583657714977372637692513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1577)
      previous := (0)
      next := (817)
      square := (43654924242182123889088884660000000000000)
      linear := (-7329176480446837624316280768840000000000000)
      constant := (310857107207583235249858849478128952349256638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree126.table
  base := (12992985852731602540984797989332494426177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-176583007831695282668915679480000000000000)
      constant := (7576903300292196546067893241375994966557062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167764040348290116787/50000000000000000000)
  centralHi := (13421123227863209343/4000000000000000000)
  directionLo := (336867519478233911871/100000000000000000000)
  directionHi := (5263554991847404873/1562500000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree127.table
  base := (5351216570506961825500422060658096713401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-465361476980251886614720065863700000000000000)
      constant := (19895465128131521306999809397088114858554885690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree127.table
  base := (6689020713133702188950770655327734998127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-533906635327674621710469789360000000000000)
      constant := (23092192787474487561173920046511798459932572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336867519478233911871/100000000000000000000)
  centralHi := (5263554991847404873/1562500000000000000)
  directionLo := (338201653489313607279/100000000000000000000)
  directionHi := (4227520668616420091/1250000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree128.table
  base := (5506982527776944941817983414083024153421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (99351)
      previous := (0)
      next := (51471)
      square := (2750260227257473805012599733580000000000000)
      linear := (-468984835692353002897514443290480000000000000)
      constant := (20209388526403448706051197312998395228649279490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree128.table
  base := (27534912638884724433716019172712261447571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (114)
      previous := (0)
      next := (57)
      square := (3118208874441580277792063190000000000000)
      linear := (-538064247160263395414192540280000000000000)
      constant := (23456525883047616141316690585354410353028139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell183.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338201653489313607279/100000000000000000000)
  centralHi := (4227520668616420091/1250000000000000000)
  directionLo := (339530545262710049639/100000000000000000000)
  directionHi := (8488263631567751241/2500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree129.table
  base := (7080615256013475033879420892733235063229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11039)
      previous := (0)
      next := (5719)
      square := (305584469695274867223622192620000000000000)
      linear := (-52512021600494902131145424524140000000000000)
      constant := (2280640883174706895732000407244037853303071912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree129.table
  base := (7080615256013474982879642995636168249893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (38)
      previous := (0)
      next := (19)
      square := (1039402958147193425930687730000000000000)
      linear := (-180740619664284056372638430400000000000000)
      constant := (7941236395743947969658094279267634018998716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell183.Kernel129
