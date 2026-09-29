import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell183.Parameters
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2557_4752.Batch050_099
import ForestUnimodality.BinomialMassData.Q427_792.Batch000_049
import ForestUnimodality.BinomialMassData.Q427_792.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree000.table
  base := (352325692628987944721075109/10000000000000000000000000)
  polynomial :=
    { denominator := 7920000000000000000000000000000000000000000
      center := (33241)
      previous := (0)
      next := (28535)
      square := (1307065070307252658832197732800000000000000)
      linear := (-5001065567534292206630652799200000000000000)
      constant := (279041948562158452219091486328000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree000.table
  base := (352325692628987944721075109/10000000000000000000000000)
  polynomial :=
    { denominator := 1320000000000000000000000000000000000000000
      center := (5551)
      previous := (0)
      next := (4745)
      square := (217844178384542109805366288800000000000000)
      linear := (-833510927922382034438442133200000000000000)
      constant := (46506991427026408703181914388000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree001.table
  base := (223879164346877124604148958567610864094791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-5709261439963921249345635245125800000000000000)
      constant := (160720152882965142058080796756034124937499354552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree001.table
  base := (223631769255693246606954256735119281603209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-317317343720597074893385867548600000000000000)
      constant := (8919532311279543695411436548678428815972205636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6230819941265383747/12500000000000000000)
  directionHi := (49846559530123069977/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree002.table
  base := (72870646405353916200324113101323343033307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-6962573459254788142583358846164400000000000000)
      constant := (108989733714151044203884439340885317249999634608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree002.table
  base := (72721572096054090587529736868070606634527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-387081941848246685558554421536800000000000000)
      constant := (6044110867757648909987727985733630124999993016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6230819941265383747/12500000000000000000)
  centralHi := (49846559530123069977/100000000000000000000)
  directionLo := (1409873610502757953/2000000000000000000)
  directionHi := (70493680525137897651/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree003.table
  base := (19440047508586936360072746347241515896389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-912876164282850559535675827467000000000000000)
      constant := (8757705863218942168480389942739295142020343560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree003.table
  base := (19385246302882329748123057492635210049247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-50760726663988477358191441725000000000000000)
      constant := (485505802300408515170218362105307374872599660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/2000000000000000000)
  centralHi := (70493680525137897651/100000000000000000000)
  directionLo := (86336773688679780039/100000000000000000000)
  directionHi := (2158419342216994501/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree004.table
  base := (33131513680540768981214611323559719733409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-9469197497836521929058806048241600000000000000)
      constant := (61745906087143148969974237038217169087428391696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree004.table
  base := (13206944578617921279230753048231079286819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-526611138103545906888891529513200000000000000)
      constant := (3423592898367358336899775535727456161802260380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/100000000000000000000)
  centralHi := (2158419342216994501/2500000000000000000)
  directionLo := (6230819941265383747/6250000000000000000)
  directionHi := (99693119060246139953/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree005.table
  base := (9189060542028220816097413340511738694273/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-10722509517127388822296529649280200000000000000)
      constant := (52840726692767943412900618948574779589325082280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree005.table
  base := (22881449070338807429488002629810220225333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-596375736231195517554060083501400000000000000)
      constant := (2931580646519338133452231069495472247427909864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6230819941265383747/6250000000000000000)
  centralHi := (99693119060246139953/100000000000000000000)
  directionLo := (111460295553845160497/100000000000000000000)
  directionHi := (55730147776922580249/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree006.table
  base := (4018610704984594476306139191497185326647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-1330646837379806190614917027813200000000000000)
      constant := (5467982795038387074551253551937915456733903808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree006.table
  base := (16002747100529190942820846467575943534177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-74015592706538347579914293054400000000000000)
      constant := (303619192478621522341944196369271620069750024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111460295553845160497/100000000000000000000)
  centralHi := (55730147776922580249/50000000000000000000)
  directionLo := (122098636282067533599/100000000000000000000)
  directionHi := (152623295352584417/125000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree007.table
  base := (5611254038203999296846952449945339482569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-13229133555709122608771976851357400000000000000)
      constant := (49145353549939358571593869677380941663373725472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree007.table
  base := (2791572760080416873777728441334780189241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-735904932486494738884397191477800000000000000)
      constant := (2731306219467478644037215084315222280312033312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/100000000000000000000)
  centralHi := (152623295352584417/125000000000000000)
  directionLo := (26376320045776455019/20000000000000000000)
  directionHi := (16485200028610284387/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree008.table
  base := (15376115827486483789133445601548126726123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-14482445574999989502009700452396000000000000000)
      constant := (51612679596712335881717038550720469683076669656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree008.table
  base := (15287540492984231737051914096110290010957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-805669530614144349549565745466000000000000000)
      constant := (2870675727085076065883592160447507809589558228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26376320045776455019/20000000000000000000)
  centralHi := (16485200028610284387/12500000000000000000)
  directionLo := (1409873610502757953/1000000000000000000)
  directionHi := (140987361050275795301/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree009.table
  base := (10053722642113076930272322454344684089887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-194268612275195757966017580906600000000000000)
      constant := (691195808936226048579228804340882137791095544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree009.table
  base := (2495844637263178581447356160519622495761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-32423486249696072600545714794600000000000000)
      constant := (115403987568404378793037056608335467455379888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/1000000000000000000)
  centralHi := (140987361050275795301/100000000000000000000)
  directionLo := (149539678590369209929/100000000000000000000)
  directionHi := (14953967859036920993/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree010.table
  base := (5926057791649016393003318785639975370497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-16989069613581723288485147654473200000000000000)
      constant := (61878521478390323354779200417722757699649358984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree010.table
  base := (5869691091397359415267961703260276299641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-945198726869443570879902853442400000000000000)
      constant := (3445423947460279527955352742017365872051125764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149539678590369209929/100000000000000000000)
  centralHi := (14953967859036920993/10000000000000000000)
  directionLo := (157628661638361411633/100000000000000000000)
  directionHi := (78814330819180705817/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree011.table
  base := (2642945602884647399975342289497868851463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2692521)
      previous := (0)
      next := (2311335)
      square := (105872270694887465365408016356800000000000000)
      linear := (-1658398330261144561974806477773800000000000000)
      constant := (6276413935701379330478103667212711032559054376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree011.table
  base := (2597401984368476483021870157635776391277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5881792816382636964744889797600000000000000)
      linear := (-92269393181553925595006491584600000000000000)
      constant := (349594490509377227297355023438251407058511228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157628661638361411633/100000000000000000000)
  centralHi := (78814330819180705817/50000000000000000000)
  directionLo := (16532233505153238537/10000000000000000000)
  directionHi := (165322335051532385371/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree012.table
  base := (-23239153007478397627222770997958944377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-2166188183573717452773399428505600000000000000)
      constant := (8590258579592414960572437747573492035089288184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree012.table
  base := (-60293419991710580881208039563752514633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-120525324791638088023359995713200000000000000)
      constant := (478595817706332387749429990116460294046258652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16532233505153238537/10000000000000000000)
  centralHi := (165322335051532385371/100000000000000000000)
  directionLo := (86336773688679780039/50000000000000000000)
  directionHi := (172673547377359560079/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree013.table
  base := (-1112129100051893234272726573507990132927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-20749005671454323968198318457589000000000000000)
      constant := (86586749249887550071080145471037020423834276112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree013.table
  base := (-140910296520504354846764841687677293777/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1154492521252392402875408515407000000000000000)
      constant := (4824966384835636095182249262357533289996263872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/50000000000000000000)
  centralHi := (172673547377359560079/100000000000000000000)
  directionLo := (179724326291326905781/100000000000000000000)
  directionHi := (89862163145663452891/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree014.table
  base := (-1015976314995530312788964708172952464147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-22002317690745190861436042058627600000000000000)
      constant := (96790575070289338272525729007384930154881832864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree014.table
  base := (-408878382232788550402132098593106706749/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1224257119380042013540577069395200000000000000)
      constant := (5394298882671207007320204711176508446686122040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179724326291326905781/100000000000000000000)
  centralHi := (89862163145663452891/50000000000000000000)
  directionLo := (37301749534230397923/20000000000000000000)
  directionHi := (11656796729446999351/6250000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree015.table
  base := (-224596727831405477221023612266965214041/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-2583958856670673083852640628851800000000000000)
      constant := (11985830622686388465044887124959576037436831800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree015.table
  base := (-5635387315454541140510244479525376605747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-143780190834187958245082847042600000000000000)
      constant := (668057782887521528431354645748999959505366068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37301749534230397923/20000000000000000000)
  centralHi := (11656796729446999351/6250000000000000000)
  directionLo := (193054894925903253463/100000000000000000000)
  directionHi := (24131861865737906683/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree016.table
  base := (-1385883046308285757523344741090231439401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-24508941729326924647911489260704800000000000000)
      constant := (119795672480165316920607840631402870998475087640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree016.table
  base := (-86828445745096030538290377126107950857/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1363786315635341234870914177371600000000000000)
      constant := (6677595170096086624727696060047845111568173760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193054894925903253463/100000000000000000000)
  centralHi := (24131861865737906683/12500000000000000000)
  directionLo := (39877247624098455981/20000000000000000000)
  directionHi := (99693119060246139953/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree017.table
  base := (-1609093967951305584811595077969295524393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-25762253748617791541149212861743400000000000000)
      constant := (132533298314762877334588758995909887693552714520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree017.table
  base := (-8059361655694104327479402066419156370437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1433550913762990845536082731359800000000000000)
      constant := (7388037921549635625977728598456115893653387852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39877247624098455981/20000000000000000000)
  centralHi := (99693119060246139953/50000000000000000000)
  directionLo := (3211291094005250627/1562500000000000000)
  directionHi := (205522630016336040129/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree018.table
  base := (-4495675321142060860503435849584609790849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-333525503307514301659097981022000000000000000)
      constant := (1803276601642585705502599324583262759004247024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree018.table
  base := (-1800558501060558502628362245844649453043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-55678352292245942822268566124000000000000000)
      constant := (301583141387305413462577640488217844970907820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3211291094005250627/1562500000000000000)
  centralHi := (205522630016336040129/100000000000000000000)
  directionLo := (4229620831508273859/2000000000000000000)
  directionHi := (211481041575413692951/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree019.table
  base := (-1957664972190197855996420348478911776629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-28268877787199525327624660063820600000000000000)
      constant := (160376984052064064491846303136497328093813301560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree019.table
  base := (-9797741382328169112165180187900205652717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1573080110018290066866419839336200000000000000)
      constant := (8940885784709561312779953562182572837590882732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4229620831508273859/2000000000000000000)
  centralHi := (211481041575413692951/100000000000000000000)
  directionLo := (217276115674990742787/100000000000000000000)
  directionHi := (54319028918747685697/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree020.table
  base := (-10452560005963095556329519913097790364227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-29522189806490392220862383664859200000000000000)
      constant := (175456627312544680671027212770045956078095204456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree020.table
  base := (-10460301293292353389201438194422947868931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1642844708145939677531588393324400000000000000)
      constant := (9781829913078887910197386171063842751746429076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217276115674990742787/100000000000000000000)
  centralHi := (54319028918747685697/25000000000000000000)
  directionLo := (44584118221538064199/20000000000000000000)
  directionHi := (55730147776922580249/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree021.table
  base := (-10996446329243455138910233808627028331011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-3419500202864584346011123029544200000000000000)
      constant := (21255065673404030348033608741272703212622089512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree021.table
  base := (-11002802359392945059638495212278755566139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-190289922919287698688528549701400000000000000)
      constant := (1185010423610421695166647388624126240753898516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44584118221538064199/20000000000000000000)
  centralHi := (55730147776922580249/25000000000000000000)
  directionLo := (57106408044977844273/25000000000000000000)
  directionHi := (228425632179911377093/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree022.table
  base := (-71434611640234388654638873667575705781/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2692521)
      previous := (0)
      next := (2311335)
      square := (105872270694887465365408016356800000000000000)
      linear := (-2911710349552011455212530078812400000000000000)
      constant := (18898830298519958642110991948030904331637966080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree022.table
  base := (-11434749390887828878883657723081451727659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5881792816382636964744889797600000000000000)
      linear := (-162033991309203536260175045572800000000000000)
      constant := (1053664077852084839794207863503387706042623324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106408044977844273/25000000000000000000)
  centralHi := (228425632179911377093/100000000000000000000)
  directionLo := (233801088393066012937/100000000000000000000)
  directionHi := (116900544196533006469/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree023.table
  base := (-11759235793359859958989827648854196271541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-33282125864362992900575554467975000000000000000)
      constant := (225226031170786975635007453987789592858669119448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree023.table
  base := (-11763502885716917170856730924753903124633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1852138502528888509527094055289000000000000000)
      constant := (12557174483755065531159814130844860481901887868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233801088393066012937/100000000000000000000)
  centralHi := (116900544196533006469/50000000000000000000)
  directionLo := (59763925380812070077/25000000000000000000)
  directionHi := (239055701523248280309/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree024.table
  base := (-2398258673018125886775393893411333496909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-3837270875961539977090364229890400000000000000)
      constant := (27034247202143082648265657096657420815871795640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree024.table
  base := (-2398956448054992713448928380492884995563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-213544788961837568910251401030800000000000000)
      constant := (1507275385713770246154861678343664964796637860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59763925380812070077/25000000000000000000)
  centralHi := (239055701523248280309/100000000000000000000)
  directionLo := (122098636282067533599/50000000000000000000)
  directionHi := (244197272564135067199/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree025.table
  base := (-606509711256966491056365219120758063879/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-35788749902944726687051001670052200000000000000)
      constant := (262130550244716512220195833081376859560927566240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree025.table
  base := (-12133042852328735039576852885032759491473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-1991667698784187730857431163265400000000000000)
      constant := (14615042149965484958086268384062988196896292508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/50000000000000000000)
  centralHi := (244197272564135067199/100000000000000000000)
  directionLo := (249232797650615349881/100000000000000000000)
  directionHi := (124616398825307674941/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree026.table
  base := (-243588783171729792346162192694082026807/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-37042061922235593580288725271090800000000000000)
      constant := (281690537041063934087192587957823712398952534800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree026.table
  base := (-12181761897675186528074634964065810989281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2061432296911837341522599717253600000000000000)
      constant := (15705729200179779937760919255879513945976227676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249232797650615349881/100000000000000000000)
  centralHi := (124616398825307674941/50000000000000000000)
  directionLo := (254168579729561929419/100000000000000000000)
  directionHi := (12708428986478096471/5000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree027.table
  base := (-6070882653612521757256081742751995806593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-472782394339832845352178381137400000000000000)
      constant := (3728225354123539575621514610837670475065923568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree027.table
  base := (-12143656789463194532889464966240117691989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-78933218334795813043991417453400000000000000)
      constant := (623608632911175133337250711964056849111231972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254168579729561929419/100000000000000000000)
  centralHi := (12708428986478096471/5000000000000000000)
  directionLo := (259010321066039340117/100000000000000000000)
  directionHi := (129505160533019670059/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree028.table
  base := (-1502414362793274315805585264395695153859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-39548685960817327366764172473168000000000000000)
      constant := (323016188460905101021558732329039188075088094016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree028.table
  base := (-300521332270040815155504065362362428923/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2200961493167136562852936825230000000000000000)
      constant := (18010070476814410666380415757094957733460108320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259010321066039340117/100000000000000000000)
  centralHi := (129505160533019670059/50000000000000000000)
  directionLo := (263763200457764550191/100000000000000000000)
  directionHi := (16485200028610284387/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree029.table
  base := (-590688289964900748290610185550372593131/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-40801997980108194260001896074206600000000000000)
      constant := (344779157356219935390788486295665830679201219360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree029.table
  base := (-11815015533346830728688831783420859970279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2270726091294786173518105379218200000000000000)
      constant := (19223576124200371376024549897776281105725182084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263763200457764550191/100000000000000000000)
  centralHi := (16485200028610284387/6250000000000000000)
  directionLo := (16776996133647111001/6250000000000000000)
  directionHi := (268431938138353776017/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree030.table
  base := (-2881608211278083340609535502685475486269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-4672812222155451239248846630582800000000000000)
      constant := (40808248057690729358970488595401373952290480992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree030.table
  base := (-11527446950462648652940947956135424443073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-260054521046937309353697103689600000000000000)
      constant := (2275322103439779330143939824914824091125974012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16776996133647111001/6250000000000000000)
  centralHi := (268431938138353776017/100000000000000000000)
  directionLo := (273020850686725191591/100000000000000000000)
  directionHi := (34127606335840648949/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree031.table
  base := (-5579173409047604704746231028775921182019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-43308622018689928046477343276283800000000000000)
      constant := (390500686558506193785597829945925807545284576464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree031.table
  base := (-11159168848592499222101669273021694830533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2410255287550085394848442487194600000000000000)
      constant := (21772998857789530895091262636730769975863784268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273020850686725191591/100000000000000000000)
  centralHi := (34127606335840648949/12500000000000000000)
  directionLo := (6938347444037610791/2500000000000000000)
  directionHi := (277533897761504431641/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree032.table
  base := (-5355158014660742577865430549271294951001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-44561934037980794939715066877322400000000000000)
      constant := (414457949071596018117149253669846853498674444656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree032.table
  base := (-5355490847943532530533070508545612446761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2480019885677735005513611041182800000000000000)
      constant := (23108844523141542785785573259593155619274363512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6938347444037610791/2500000000000000000)
  centralHi := (277533897761504431641/100000000000000000000)
  directionLo := (1409873610502757953/500000000000000000)
  directionHi := (281974722100551590601/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree033.table
  base := (-101829744673840189994940769451855813697/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (299169)
      previous := (0)
      next := (256815)
      square := (11763585632765273929489779595200000000000000)
      linear := (-462780263204764260938917075539000000000000000)
      constant := (4435813865358461996502169327247260925996778400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree033.table
  base := (-101835130011373446447437269518351713011/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3960000000000000000000000000000000000000000
      center := (16653)
      previous := (0)
      next := (14235)
      square := (653532535153626329416098866400000000000000)
      linear := (-25755398826317016325038177729000000000000000)
      constant := (247327387132923306456242864604410772164764400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/500000000000000000)
  centralHi := (281974722100551590601/100000000000000000000)
  directionLo := (286346683935179177191/100000000000000000000)
  directionHi := (35793335491897397149/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree034.table
  base := (-9576819467956458704164911836509534434463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-47068558076562528726190514079399600000000000000)
      constant := (464563206399321858030812490307201868816563625864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree034.table
  base := (-9577254757880726653745200963160484469593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2619549081933034226843948149159200000000000000)
      constant := (25902679978728484769404008866038206366854076028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286346683935179177191/100000000000000000000)
  centralHi := (35793335491897397149/12500000000000000000)
  directionLo := (145326445371845092587/50000000000000000000)
  directionHi := (11626115629747607407/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree035.table
  base := (-4446120605660345571513291284569749706899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-48321870095853395619428237680438200000000000000)
      constant := (490710574918798499574798920235707972419666337744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree035.table
  base := (-4446296375604413619989518920675175519741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2689313680060683837509116703147400000000000000)
      constant := (27360635356530043356874049224519513337848147672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145326445371845092587/50000000000000000000)
  centralHi := (11626115629747607407/4000000000000000000)
  directionLo := (58979244618646518157/20000000000000000000)
  directionHi := (147448111546616295393/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree036.table
  base := (-1016193229300661806694797363430613334739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-612039285372151389045258781252800000000000000)
      constant := (6389968669094555539435095898967839973022030656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree036.table
  base := (-8129829508975850935317182169273229645221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-102188084377345683265714268782800000000000000)
      constant := (1068861688861558772855950257624215270555139108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58979244618646518157/20000000000000000000)
  centralHi := (147448111546616295393/50000000000000000000)
  directionLo := (149539678590369209929/50000000000000000000)
  directionHi := (299079357180738419859/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree037.table
  base := (-7288973547458443035674388652251229971367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-50828494134435129405903684882515400000000000000)
      constant := (545193698723257105664007858882678951293645506376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree037.table
  base := (-364460114164839533834839436499796167539/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2828842876315983058839453811123800000000000000)
      constant := (30398561405692699117014147843925752320956020880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149539678590369209929/50000000000000000000)
  centralHi := (299079357180738419859/100000000000000000000)
  directionLo := (303204784574112241821/100000000000000000000)
  directionHi := (151602392287056120911/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree038.table
  base := (-1592678209875075432542190650830850888961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-52081806153725996299141408483554000000000000000)
      constant := (573529151487168982720561303451387992165940452832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree038.table
  base := (-637089714276637361466255934459329277953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-2898607474443632669504622365112000000000000000)
      constant := (31978515481188692423374567398541914549871305880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303204784574112241821/100000000000000000000)
  centralHi := (151602392287056120911/50000000000000000000)
  directionLo := (38409353695914666957/12500000000000000000)
  directionHi := (307274829567317335657/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree039.table
  base := (-5374911619495041403410647316658620203043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-5926124241446318132486570231621400000000000000)
      constant := (66954857345908896164476739237117612157119804456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree039.table
  base := (-1343765004771076638943659065330540401667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-329819119174586920018865657677800000000000000)
      constant := (3733235789404856831171947978111293164041354192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38409353695914666957/12500000000000000000)
  centralHi := (307274829567317335657/100000000000000000000)
  directionLo := (15564583224633258629/5000000000000000000)
  directionHi := (311291664492665172581/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree040.table
  base := (-1075421488923356945584640003776977961597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-54588430192307730085616855685631200000000000000)
      constant := (632387310695175699591135750605006769631535687264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree040.table
  base := (-4301805367697179266340116609589947035493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3038136670698931890834959473088400000000000000)
      constant := (35260376788946428183334737621443635716420532428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15564583224633258629/5000000000000000000)
  centralHi := (311291664492665172581/100000000000000000000)
  directionLo := (157628661638361411633/50000000000000000000)
  directionHi := (315257323276722823267/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree041.table
  base := (-1575563465881133197950433534418529746539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-55841742211598596978854579286669800000000000000)
      constant := (662909870957962563061872544271065145803400661584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree041.table
  base := (-1575611479303671313471007253001106008243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3107901268826581501500128027076600000000000000)
      constant := (36962276014753670367813808368440501780105682856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157628661638361411633/50000000000000000000)
  centralHi := (315257323276722823267/100000000000000000000)
  directionLo := (319173713479970378777/100000000000000000000)
  directionHi := (159586856739985189389/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree042.table
  base := (-1923306025979370227261885865272758236411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-6343894914543273763565811431967600000000000000)
      constant := (77129038495702377227671722661423718572199486312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree042.table
  base := (-961691600749636160079029124732606499291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-353073985217136790240588509007200000000000000)
      constant := (4300535224636018649924996309306879532178176808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319173713479970378777/100000000000000000000)
  centralHi := (159586856739985189389/50000000000000000000)
  directionLo := (323042627022478765827/100000000000000000000)
  directionHi := (80760656755619691457/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree043.table
  base := (-618279331920977162440187317707165186673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-58348366250180330765330026488747000000000000000)
      constant := (726141697621586064611152132676727030578390090744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree043.table
  base := (-309170660892277758774218028940798984539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3247430465081880722830465135053000000000000000)
      constant := (40487997644800884764394367248513222333220266088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323042627022478765827/100000000000000000000)
  centralHi := (80760656755619691457/25000000000000000000)
  directionLo := (326865749766742051019/100000000000000000000)
  directionHi := (16343287488337102551/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree044.table
  base := (76390912969961857560610255493528000047/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2692521)
      previous := (0)
      next := (2311335)
      square := (105872270694887465365408016356800000000000000)
      linear := (-5418334388133745241687977280889600000000000000)
      constant := (68986444852233798180662647612616308082590151440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree044.table
  base := (763859364333264041383722476553269393809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5881792816382636964744889797600000000000000)
      linear := (-301563187564502757590512153549200000000000000)
      constant := (3846528744165034307659866279105635852119535276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326865749766742051019/100000000000000000000)
  centralHi := (16343287488337102551/5000000000000000000)
  directionLo := (330644670103064770741/100000000000000000000)
  directionHi := (165322335051532385371/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree045.table
  base := (2223224812250725347072635275837028355097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-751296176404469932738339181368200000000000000)
      constant := (9781344559773924223143363740007873441029605064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree045.table
  base := (2223184881304151170731665131050956763043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-125442950419895553487437120112200000000000000)
      constant := (1636158196770006745536635701280223489219938436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330644670103064770741/100000000000000000000)
  centralHi := (165322335051532385371/50000000000000000000)
  directionLo := (334380886661535481493/100000000000000000000)
  directionHi := (167190443330767740747/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree046.table
  base := (1879820301941562099212576261642723462809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-62108302308052931445043197291862800000000000000)
      constant := (826455726390861448835743723143902512902894705296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree046.table
  base := (3759608579728336154268769835227953231699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3456724259464829554825970797017600000000000000)
      constant := (46081361980962230428131323350078026678495527596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334380886661535481493/100000000000000000000)
  centralHi := (167190443330767740747/50000000000000000000)
  directionLo := (338075815256792274931/100000000000000000000)
  directionHi := (84518953814198068733/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree047.table
  base := (5373135227235712915426984483660468372997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-63361614327343798338280920892901400000000000000)
      constant := (861351329507254576548958085087856781287709538984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree047.table
  base := (1343277389091294604834762842819042168899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3526488857592479165491139351005800000000000000)
      constant := (48027087370840876207174602072219023416758065584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338075815256792274931/100000000000000000000)
  centralHi := (84518953814198068733/25000000000000000000)
  directionLo := (341730795156852733097/100000000000000000000)
  directionHi := (170865397578426366549/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree048.table
  base := (7063691983623936290168067142894486962481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-7179436260737185025724293832660000000000000000)
      constant := (99663967434119235307953248675507270933754210248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree048.table
  base := (220739731716179098426209530124569695519/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-399583717302236530684034211666000000000000000)
      constant := (5557049648847299329292513970953524018997784448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341730795156852733097/100000000000000000000)
  centralHi := (170865397578426366549/50000000000000000000)
  directionLo := (86336773688679780039/25000000000000000000)
  directionHi := (345347094754719120157/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree049.table
  base := (4415648883773720916300362971389288730689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-65868238365925532124756368094978600000000000000)
      constant := (933328849342132427761250259518188075564325536016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree049.table
  base := (8831281294084784494970985487819613120651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3666018053847778386821476458982200000000000000)
      constant := (52040439883102231066538281153264492612782001804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/25000000000000000000)
  centralHi := (345347094754719120157/100000000000000000000)
  directionLo := (174462958355430744917/50000000000000000000)
  directionHi := (69785183342172297967/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree050.table
  base := (5337971146661996134244816323003207135641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-67121550385216399017994091696017200000000000000)
      constant := (970410749554114550776186956855848263371644111504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree050.table
  base := (10675929105232284484934122822320693885817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3735782651975427997486645012970400000000000000)
      constant := (54108066105755678064035937320465010483099569668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174462958355430744917/50000000000000000000)
  centralHi := (69785183342172297967/20000000000000000000)
  directionLo := (1409873610502757953/400000000000000000)
  directionHi := (352468402625689488251/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree051.table
  base := (787351093011650660158797951355427618403/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-7597206933834140656803535033006200000000000000)
      constant := (112024600205143747495948814265478553149259878784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree051.table
  base := (12597606934472546950738810232512477322491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-422838583344786400905757062995400000000000000)
      constant := (6246258355258886909552486473216136851216770796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1409873610502757953/400000000000000000)
  centralHi := (352468402625689488251/100000000000000000000)
  directionLo := (355975637293474419009/100000000000000000000)
  directionHi := (35597563729347441901/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree052.table
  base := (729815850800514326024476261619023263097/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-69628174423798132804469538898094400000000000000)
      constant := (1046760801747444373032700282175987487682323723680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree052.table
  base := (1824538571711541796824346998874513895597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3875311848230727218816982120946800000000000000)
      constant := (58365216914442272068700154155904211542103878304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355975637293474419009/100000000000000000000)
  centralHi := (35597563729347441901/10000000000000000000)
  directionLo := (179724326291326905781/50000000000000000000)
  directionHi := (359448652582653811563/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree053.table
  base := (8336017951777023182891861229870914469831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-70881486443088999697707262499133000000000000000)
      constant := (1086028945748089159633622685274161517161509162864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree053.table
  base := (16672029152719231631027102350214920704329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-3945076446358376829482150674935000000000000000)
      constant := (60554741066162308349640146335966738251292514116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179724326291326905781/50000000000000000000)
  centralHi := (359448652582653811563/100000000000000000000)
  directionLo := (362888430981859025821/100000000000000000000)
  directionHi := (181444215490929512911/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree054.table
  base := (941238512357296241124241340057557117689/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-890553067436788476431419581483600000000000000)
      constant := (13901553470290323769388943726640853752186131360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree054.table
  base := (18824764850814100249313216963641596772617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-148697816462445423709159971441600000000000000)
      constant := (2325366574174141994229116558254057598513839884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362888430981859025821/100000000000000000000)
  centralHi := (181444215490929512911/50000000000000000000)
  directionLo := (366295908846202600797/100000000000000000000)
  directionHi := (183147954423101300399/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree055.table
  base := (10527258491251073295210965274783018371587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2692521)
      previous := (0)
      next := (2311335)
      square := (105872270694887465365408016356800000000000000)
      linear := (-6671646407424612134925700881928200000000000000)
      constant := (106068314147395119073611213376707854139148098448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree055.table
  base := (2631814083797725925059419056775723403371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5881792816382636964744889797600000000000000)
      linear := (-371327785692152368255680707537400000000000000)
      constant := (5914153282413011724082810179484726925676913952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366295908846202600797/100000000000000000000)
  centralHi := (183147954423101300399/50000000000000000000)
  directionLo := (7393439587484452227/2000000000000000000)
  directionHi := (369671979374222611351/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree056.table
  base := (1460079606505491514856456223875043109813/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-74641422500961600377420433302248800000000000000)
      constant := (1208205817634060826244321497329757590742207349376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree056.table
  base := (5840317564870526647593270183692696392107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4154370240741325661477656336899600000000000000)
      constant := (67367106785480728288258159697655953877424651312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7393439587484452227/2000000000000000000)
  centralHi := (369671979374222611351/100000000000000000000)
  directionLo := (37301749534230397923/10000000000000000000)
  directionHi := (373017495342303979231/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree057.table
  base := (5149007704671457034073319109251160317321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-8432748280028051918962017433698600000000000000)
      constant := (138932101755440654230325811242905506140802524840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree057.table
  base := (1287251788630820527466363207389968684503/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-469348315429886141349202765654200000000000000)
      constant := (7746573274129300577656376592233926571793901360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37301749534230397923/10000000000000000000)
  centralHi := (373017495342303979231/100000000000000000000)
  directionLo := (94083317905074128599/25000000000000000000)
  directionHi := (376333271620296514397/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree058.table
  base := (28205809957504697327190321655678854001461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-77148046539543334163895880504326000000000000000)
      constant := (1293300749069687022853889462632531633260918986792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree058.table
  base := (28205807761535914298513295712963532870129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4293899436996624882807993444876000000000000000)
      constant := (72111844094814913546468760979623372342640537316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94083317905074128599/25000000000000000000)
  centralHi := (376333271620296514397/100000000000000000000)
  directionLo := (23726255468084723091/6250000000000000000)
  directionHi := (379620087489355569457/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree059.table
  base := (15371793421079657396545151477628230770819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-78401358558834201057133604105364600000000000000)
      constant := (1336941316624560369348923701760049618979010770736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree059.table
  base := (30743585089596726519034722341162349032641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4363664035124274493473161998864200000000000000)
      constant := (74545160623873366215676258099304941231475657764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23726255468084723091/6250000000000000000)
  centralHi := (379620087489355569457/100000000000000000000)
  directionLo := (382878688780684266477/100000000000000000000)
  directionHi := (191439344390342133239/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree060.table
  base := (33358368262870367774282540803712872765143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-8850518953125007550041258634044800000000000000)
      constant := (153478957535364847104012875186613018927769332344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree060.table
  base := (1042448964518247923593407761294406896429/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-492603181472436011570925616983600000000000000)
      constant := (8557678779928963303507097694318349966107031168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382878688780684266477/100000000000000000000)
  centralHi := (191439344390342133239/50000000000000000000)
  directionLo := (386109789851806506927/100000000000000000000)
  directionHi := (24131861865737906683/6250000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree061.table
  base := (18025076750669057291274459724749140970371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-80907982597415934843609051307441800000000000000)
      constant := (1426408652143972771298857733212306632863687288624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree061.table
  base := (7210030477204331921882089106067065528311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4503193231379573714803499106840600000000000000)
      constant := (79533689253815367859387376097849578684859522220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386109789851806506927/100000000000000000000)
  centralHi := (24131861865737906683/6250000000000000000)
  directionLo := (389314075415205462223/100000000000000000000)
  directionHi := (24332129713450341389/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree062.table
  base := (38818941993216947457730389434915520691239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-82161294616706801736846774908480400000000000000)
      constant := (1472235419203384917717822314609505930317228007608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree062.table
  base := (38818941103845144214559047570237898439477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4572957829507223325468667660828800000000000000)
      constant := (82088901305672721729769474928708556570421256308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389314075415205462223/100000000000000000000)
  centralHi := (24332129713450341389/6250000000000000000)
  directionLo := (392492202232587531879/100000000000000000000)
  directionHi := (9812305055814688297/2500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree063.table
  base := (20832366647499945960034405434125399850527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-1029809958469107020124499981599000000000000000)
      constant := (18750505168932711228369502898487032216995582448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree063.table
  base := (41664732585984571081138538382018938595837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-171952682504995293930882822771000000000000000)
      constant := (3136472042888661713514985295003428998841155324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392492202232587531879/100000000000000000000)
  centralHi := (9812305055814688297/2500000000000000000)
  directionLo := (395644800686646825287/100000000000000000000)
  directionHi := (49455600085830853161/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree064.table
  base := (22293763529014945356731477937221512631389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-84667918655288535523322222110557600000000000000)
      constant := (1566075150338429323731152528039087558523235076816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree064.table
  base := (5573440811617350244443455119891120966601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4712487025762522546799004768805200000000000000)
      constant := (87321220797468998840698575743236892050997004832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395644800686646825287/100000000000000000000)
  centralHi := (49455600085830853161/12500000000000000000)
  directionLo := (398772476240984559811/100000000000000000000)
  directionHi := (99693119060246139953/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree065.table
  base := (1903492920324158676564952561541337689219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-85921230674579402416559945711596200000000000000)
      constant := (1614088113974526697285726655836875002495663754200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree065.table
  base := (23793661278915814857847308485336702369783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4782251623890172157464173322793400000000000000)
      constant := (89998328213635504633136908753617092659409945464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398772476240984559811/100000000000000000000)
  centralHi := (99693119060246139953/25000000000000000000)
  directionLo := (40187581079775963333/10000000000000000000)
  directionHi := (401875810797759633331/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree066.table
  base := (6333015116183314088518748819280280384857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 71280000000000000000000000000000000000000000
      center := (299169)
      previous := (0)
      next := (256815)
      square := (11763585632765273929489779595200000000000000)
      linear := (-880550936301719892018158275885200000000000000)
      constant := (16796260701409990291761623162576513708666085568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree066.table
  base := (50664120570768243257792837460766499453049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3960000000000000000000000000000000000000000
      center := (16653)
      previous := (0)
      next := (14235)
      square := (653532535153626329416098866400000000000000)
      linear := (-49010264868866886546761029058400000000000000)
      constant := (936525933315804721896027787824713533783407404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40187581079775963333/10000000000000000000)
  centralHi := (401875810797759633331/100000000000000000000)
  directionLo := (404955363961692451301/100000000000000000000)
  directionHi := (202477681980846225651/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree067.table
  base := (53817920652247041041868350617642673586313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-88427854713161136203035392913673400000000000000)
      constant := (1712300236613743502187035011430330522005000667336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree067.table
  base := (1345448009164114226202289599718181803399/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4921780820145471378794510430769800000000000000)
      constant := (95474438344880610925590939300577076476818175840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404955363961692451301/100000000000000000000)
  centralHi := (202477681980846225651/50000000000000000000)
  directionLo := (204005837109098979083/50000000000000000000)
  directionHi := (408011674218197958167/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree068.table
  base := (14262180510650265499754693380304267364759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-89681166732452003096273116514712000000000000000)
      constant := (1762499395402539778305442498942726591839296852192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree068.table
  base := (14262180453780534902241415134741478038421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-4991545418273120989459678984758000000000000000)
      constant := (98273441048382954687796655486813219620073027536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204005837109098979083/50000000000000000000)
  centralHi := (408011674218197958167/100000000000000000000)
  directionLo := (3211291094005250627/781250000000000000)
  directionHi := (411045260032672080257/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree069.table
  base := (60356524994972307374593946714922503261111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-10103830972415874443278982235083400000000000000)
      constant := (201491920636832196038095470596716574885697191288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree069.table
  base := (6035652481387799613486892272906621074229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-562367779600085622236094170971800000000000000)
      constant := (11234786167194535613034585389887424913993415240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3211291094005250627/781250000000000000)
  centralHi := (411045260032672080257/100000000000000000000)
  directionLo := (82811324175457334731/20000000000000000000)
  directionHi := (51757077609660834207/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree070.table
  base := (63741329426019744976349616080022657740113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-92187790771033736882748563716789200000000000000)
      constant := (1865083907541782027430119833421021373932781020936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree070.table
  base := (15935332320470540484363073424943457707477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5131074614528420210790016092734400000000000000)
      constant := (103993341710810645528044741157907683263855713232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82811324175457334731/20000000000000000000)
  centralHi := (51757077609660834207/12500000000000000000)
  directionLo := (83409247638210288211/20000000000000000000)
  directionHi := (13032694943470357533/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree071.table
  base := (1344062705397021814534099054111907301467/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-93441102790324603775986287317827800000000000000)
      constant := (1917469260786918227677629674395214923712041041200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree071.table
  base := (67203135155151720680782659872979357788291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5200839212656069821455184646722600000000000000)
      constant := (106914239664054043467963151648859595242732160364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83409247638210288211/20000000000000000000)
  centralHi := (13032694943470357533/3125000000000000000)
  directionLo := (105003644069592090931/25000000000000000000)
  directionHi := (16800583051134734549/4000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree072.table
  base := (7074194247428164264152943673542547342767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-1169066849501425563817580381714400000000000000)
      constant := (24328189449753988667491893902284626724501861040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree072.table
  base := (4421371398939138768182191970714418086187/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-195207548547545164152605674100400000000000000)
      constant := (4069472939351663776813317117523237360978296384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105003644069592090931/25000000000000000000)
  centralHi := (16800583051134734549/4000000000000000000)
  directionLo := (422962083150827385901/100000000000000000000)
  directionHi := (211481041575413692951/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree073.table
  base := (74357750997897778615727105972922522947147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-95947726828906337562461734519905000000000000000)
      constant := (2024426161442022157059613750655348513863159117784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree073.table
  base := (74357750925308487931549679816368456957543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5340368408911369042785521754699000000000000000)
      constant := (112877930804557391082159673456052321486563515772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422962083150827385901/100000000000000000000)
  centralHi := (211481041575413692951/50000000000000000000)
  directionLo := (425889191316564786451/100000000000000000000)
  directionHi := (106472297829141196613/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree074.table
  base := (39025280403875976094556993223516335861357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-97201038848197204455699458120943600000000000000)
      constant := (2078997708799515291650289762825994664519911033808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree074.table
  base := (39025280375010751795605707979747332284621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5410133007039018653450690308687200000000000000)
      constant := (115920723988987823700033616901641978829772563368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425889191316564786451/100000000000000000000)
  centralHi := (106472297829141196613/25000000000000000000)
  directionLo := (53599539815140266299/12500000000000000000)
  directionHi := (428796318521122130393/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree075.table
  base := (2556886621173540334206397060435181165141/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-10939372318609785705437464635775800000000000000)
      constant := (237144220831555528126904885978784285163484016896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree075.table
  base := (81820371831648500557507837093381112656823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-608877511685185362679539873630600000000000000)
      constant := (13222683212753984500598751019969080626733120988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53599539815140266299/12500000000000000000)
  centralHi := (428796318521122130393/100000000000000000000)
  directionLo := (86336773688679780039/20000000000000000000)
  directionHi := (107920967110849725049/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree076.table
  base := (21416796046561787139968700952497524292381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-99707662886778938242174905323020800000000000000)
      constant := (2190326997480617867684863036827354831849812340128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree076.table
  base := (2677099504679753308521163386618166083647/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5549662203294317874781027416663600000000000000)
      constant := (122128205581150274728789010021459314660585503616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86336773688679780039/20000000000000000000)
  centralHi := (107920967110849725049/25000000000000000000)
  directionLo := (17382089253999259423/4000000000000000000)
  directionHi := (54319028918747685697/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree077.table
  base := (44795498858449960821574736384092287432989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2692521)
      previous := (0)
      next := (2311335)
      square := (105872270694887465365408016356800000000000000)
      linear := (-9178270446006345921401148084005400000000000000)
      constant := (204280430797947278634228403641719020596802220656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree077.table
  base := (22397749421972700318283312702991922973097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5881792816382636964744889797600000000000000)
      linear := (-510856981947451589586017815513800000000000000)
      constant := (11390263089766953917111702781215990353904470832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17382089253999259423/4000000000000000000)
  centralHi := (54319028918747685697/12500000000000000000)
  directionLo := (437401784710851328397/100000000000000000000)
  directionHi := (218700892355425664199/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree078.table
  base := (93591812455823441304470850879198244044211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-11357142991706741336516705836122000000000000000)
      constant := (256063467929416331964066204351149000919018496088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree078.table
  base := (93591812432768607319462316923511075383079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-632132377727735232901262724960000000000000000)
      constant := (14277579348124806667307238956832964244368692124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437401784710851328397/100000000000000000000)
  centralHi := (218700892355425664199/50000000000000000000)
  directionLo := (27514555861201394709/6250000000000000000)
  directionHi := (88046578755844463069/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree079.table
  base := (97669628391887402776301880188570480076399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-103467598944651538921888076126136600000000000000)
      constant := (2362786415234744291359195823370810039066472635128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree079.table
  base := (97669628373567715326711014215012135621157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5758955997677266706776533078628200000000000000)
      constant := (131744166017786474109713356492508848264891839028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27514555861201394709/6250000000000000000)
  centralHi := (88046578755844463069/20000000000000000000)
  directionLo := (44304591213802903229/10000000000000000000)
  directionHi := (443045912138029032291/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree080.table
  base := (10182444551597937576387113307924240627383/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-104720910963942405815125799727175200000000000000)
      constant := (2421730350380981589113340449820931147320066163760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree080.table
  base := (101824445501424632870040385853569829530859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5828720595804916317441701632616400000000000000)
      constant := (135030749641078651043049961772735351596927796236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44304591213802903229/10000000000000000000)
  centralHi := (443045912138029032291/100000000000000000000)
  directionLo := (44584118221538064199/10000000000000000000)
  directionHi := (445841182215380641991/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree081.table
  base := (106056263820580650931180844900385937517533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-1308323740533744107510660781829800000000000000)
      constant := (30634605145656211583758981530049693537652747496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree081.table
  base := (53028131904509455942460029879365819990143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-218462414590095034374328525429800000000000000)
      constant := (5124369074174548146661226583153115841251375272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44584118221538064199/10000000000000000000)
  centralHi := (445841182215380641991/100000000000000000000)
  directionLo := (448619035771107629787/100000000000000000000)
  directionHi := (112154758942776907447/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree082.table
  base := (22073016659886601583786444328024095189067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-107227535002524139601601246929252400000000000000)
      constant := (2541804414481842687995219887142140321501296440120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree082.table
  base := (110365083290250197892339907995295845744971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-5968249792060215538772038740592800000000000000)
      constant := (141725812102449762563127711354133528336585843084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448619035771107629787/100000000000000000000)
  centralHi := (112154758942776907447/25000000000000000000)
  directionLo := (28211237147272403577/6250000000000000000)
  directionHi := (451379794356358457233/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree083.table
  base := (114750903947276852090032884680969034331017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-108480847021815006494838970530291000000000000000)
      constant := (2602934543428338689578821346441524361644437428424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree083.table
  base := (57375451969992285057074795369169189220447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6038014390187865149437207294581000000000000000)
      constant := (145134290940088268622687136677237230288396808376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28211237147272403577/6250000000000000000)
  centralHi := (451379794356358457233/100000000000000000000)
  directionLo := (113530942437012120381/25000000000000000000)
  directionHi := (18164950789921939261/4000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree084.table
  base := (59606862879822687398638587411846558204679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-12192684337900652598675188236814400000000000000)
      constant := (296088155959387671249287885543748029871424942064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree084.table
  base := (29803431438463811343623428771494578547259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-678642109812834973344708427618800000000000000)
      constant := (16509266835050791418989462099013321536607440816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113530942437012120381/25000000000000000000)
  centralHi := (18164950789921939261/4000000000000000000)
  directionLo := (57106408044977844273/12500000000000000000)
  directionHi := (91370252871964550837/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree085.table
  base := (30938387183175673496565156885866060915083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-110987471060396740281314417732368200000000000000)
      constant := (2727380995097586868428433050208599281002273803104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree085.table
  base := (123753548728105936992094257970602040238783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6177543586443164370767544402557400000000000000)
      constant := (152073143828409063544728954379438794885521248732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57106408044977844273/12500000000000000000)
  centralHi := (91370252871964550837/20000000000000000000)
  directionLo := (229781285815533049531/50000000000000000000)
  directionHi := (459562571631066099063/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree086.table
  base := (6418518643155826164814300526717979019791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-112240783079687607174552141333406800000000000000)
      constant := (2790697317815280669952621650070340218817079091040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree086.table
  base := (128370372859467684170990118757260864353317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6247308184570813981432712956545600000000000000)
      constant := (155603517878815934605113664152901404926107439668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229781285815533049531/50000000000000000000)
  centralHi := (459562571631066099063/100000000000000000000)
  directionLo := (28891123524711058623/6250000000000000000)
  directionHi := (462257976395376937969/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree087.table
  base := (26612839629591590292500160145508477720393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-12610455010997608229754429437160600000000000000)
      constant := (317193596865055955016229528868880324855502871720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree087.table
  base := (133064198145061947359496080317283646920171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-701896975855384843566431278948200000000000000)
      constant := (17686058185173876187497224551021700065984264876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28891123524711058623/6250000000000000000)
  centralHi := (462257976395376937969/100000000000000000000)
  directionLo := (92987551045962913973/20000000000000000000)
  directionHi := (232468877614907284933/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree088.table
  base := (68917512292311254895438170228180747367231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 641520000000000000000000000000000000000000000
      center := (2692521)
      previous := (0)
      next := (2311335)
      square := (105872270694887465365408016356800000000000000)
      linear := (-10431582465297212814638871685044000000000000000)
      constant := (265410559727856158488773889867673302610205206224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree088.table
  base := (34458756145581079514354335692829875617683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (149877)
      previous := (0)
      next := (128115)
      square := (5881792816382636964744889797600000000000000)
      linear := (-580621580075101200251186369502000000000000000)
      constant := (14798741926505034701906489805804582706805688848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92987551045962913973/20000000000000000000)
  centralHi := (232468877614907284933/50000000000000000000)
  directionLo := (233801088393066012937/50000000000000000000)
  directionHi := (3740817414289056207/800000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree089.table
  base := (35670713042691989493669991871329194696891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-116000719137560207854265312136522600000000000000)
      constant := (2985018673476370261242230085018740593170577863008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree089.table
  base := (142682852168944409683054769054866070936759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6456601978953762813428218618510200000000000000)
      constant := (166438430453696846310053831897389981945004699836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233801088393066012937/50000000000000000000)
  centralHi := (3740817414289056207/800000000000000000)
  directionLo := (94050300421023466609/20000000000000000000)
  directionHi := (235125751052558666523/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree090.table
  base := (147607680904265201472201758895971203388337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87120000000000000000000000000000000000000000
      center := (365651)
      previous := (0)
      next := (313885)
      square := (14377715773379779247154175060800000000000000)
      linear := (-1447580631566062651203741181945200000000000000)
      constant := (37669752113504428473330618821200326123919191944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree090.table
  base := (29521536180563690316235797244443808186109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14520000000000000000000000000000000000000000
      center := (61061)
      previous := (0)
      next := (52195)
      square := (2396285962229963207859029176800000000000000)
      linear := (-241717280632644904596051376759200000000000000)
      constant := (6301160424181733452961286693438912047431151340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94050300421023466609/20000000000000000000)
  centralHi := (235125751052558666523/50000000000000000000)
  directionLo := (472885984915084234899/100000000000000000000)
  directionHi := (4728859849150842349/1000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree091.table
  base := (152609510783159525084708524392279444642663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-118507343176141941640740759338599800000000000000)
      constant := (3118209900157503690885442459177272901509877284536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree091.table
  base := (6104380431280474308152815285551005801289/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6596131175209062034758555726486600000000000000)
      constant := (173864864189109408969249513666107353285843348900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472885984915084234899/100000000000000000000)
  centralHi := (4728859849150842349/1000000000000000000)
  directionLo := (237752935957739214631/50000000000000000000)
  directionHi := (475505871915478429263/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree092.table
  base := (78844170902819966394144135460474782941733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-119760655195432808533978482939638400000000000000)
      constant := (3185898610366027245693031065036977422056117219152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree092.table
  base := (19711042725591203669365743472479272463711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6665895773336711645423724280474800000000000000)
      constant := (177639028662234292399058088561355819181338608352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237752935957739214631/50000000000000000000)
  centralHi := (475505871915478429263/100000000000000000000)
  directionLo := (478111403046496560617/100000000000000000000)
  directionHi := (239055701523248280309/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree093.table
  base := (162844173970014859011733771904939092608661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-13445996357191519491912911837853000000000000000)
      constant := (361590672424248408922531221789251695623259891688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree093.table
  base := (81422086984646456252075127616258563067793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-748406707940484584009876981607000000000000000)
      constant := (20161536096912848413997200361411057101446612616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478111403046496560617/100000000000000000000)
  centralHi := (239055701523248280309/50000000000000000000)
  directionLo := (240351405872775988489/50000000000000000000)
  directionHi := (480702811745551976979/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree094.table
  base := (168077007274692889453264082447689540189939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-122267279234014542320453930141715600000000000000)
      constant := (3323462224513005978201525889429092198204914634008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree094.table
  base := (5252406477316262246123285133667458927079/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6805424969592010866754061388451200000000000000)
      constant := (185309252818991445065937066882814519912870563712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240351405872775988489/50000000000000000000)
  centralHi := (480702811745551976979/100000000000000000000)
  directionLo := (483280325191363120079/100000000000000000000)
  directionHi := (6041004064892039001/1250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree095.table
  base := (3467736834363348443905638055984234518791/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-123520591253305409213691653742754200000000000000)
      constant := (3393337128449274972600871023305283868317214127600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree095.table
  base := (5418338803678546492036781207219637314937/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-6875189567719660477419229942439400000000000000)
      constant := (189205312502502970099400743511169149661433284736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483280325191363120079/100000000000000000000)
  centralHi := (6041004064892039001/1250000000000000000)
  directionLo := (485844164536386903609/100000000000000000000)
  directionHi := (48584416453638690361/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree096.table
  base := (178773677299004429576213631868690014544447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 784080000000000000000000000000000000000000000
      center := (3290859)
      previous := (0)
      next := (2824965)
      square := (129399441960418013224387575547200000000000000)
      linear := (-13863767030288475122992153038199200000000000000)
      constant := (384882307069558967814757603500320246660401000376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree096.table
  base := (89386838649322271967078795059832710030481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (183183)
      previous := (0)
      next := (156585)
      square := (7188857886689889623577087530400000000000000)
      linear := (-771661573983034454231599832936400000000000000)
      constant := (21460222658077137888175082387577262569785550472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485844164536386903609/100000000000000000000)
  centralHi := (48584416453638690361/10000000000000000000)
  directionLo := (122098636282067533599/25000000000000000000)
  directionHi := (488394545128270134397/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree097.table
  base := (36847502803166532312586310557558789133427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-126027215291887143000167100944831400000000000000)
      constant := (3535273130042305538643990811803978760476818489720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree097.table
  base := (92118757007773685048291891141867586007707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-7014718763974959698749567050415800000000000000)
      constant := (197119327079511697622125593436213566183692290456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell183.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122098636282067533599/25000000000000000000)
  centralHi := (488394545128270134397/100000000000000000000)
  directionLo := (490931676720946573631/100000000000000000000)
  directionHi := (7670807448764790213/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2557
  qDenominator := 4752
  table := BinomialMassData.Q2557_4752.Degree098.table
  base := (189778351867335772870852877654532425770613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7056720000000000000000000000000000000000000000
      center := (29617731)
      previous := (0)
      next := (25424685)
      square := (1164594977643762119019488179924800000000000000)
      linear := (-127280527311178009893404824545870000000000000000)
      constant := (3607334227697170549524726059104199630958400016936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2557_4752.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 427
  qDenominator := 792
  table := BinomialMassData.Q427_792.Degree098.table
  base := (189778351867109638335729160953048819055167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1648647)
      previous := (0)
      next := (1409265)
      square := (64699720980209006612193787773600000000000000)
      linear := (-7084483362102609309414735604404000000000000000)
      constant := (201137281972903891482187037014095675902238767068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q427_792.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell183.Kernel098
