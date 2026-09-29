import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell184.Parameters
import ForestUnimodality.BinomialMassData.Q2_3.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_3.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_3.Batch100_149
import ForestUnimodality.BinomialMassData.Q35_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q35_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q35_52.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree000.table
  base := (295425258143736744531171467/50000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-293000451147795090700576280000000000000)
      constant := (29542525814373674453117146700000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree000.table
  base := (295425258143736744531171467/50000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-15236023459685344716429966560000000000000)
      constant := (1536211342347431071562091628400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree001.table
  base := (2742206415293083314963379211675796402449/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-4611288874091289610723798380000000000000)
      constant := (199854959545909147153039631540657340976328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree001.table
  base := (341652291631342237573947328948456922101/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-347784903352795460723667631330000000000000)
      constant := (14964945344095166268046411103869790277777664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29863125692764953999/100000000000000000000)
  directionHi := (14931562846382477/50000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree002.table
  base := (8093056254931279389688055384381236645299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-6585573687852423405142410240000000000000)
      constant := (151823397754218081828683394758862259615382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree002.table
  base := (3215618233473807062605505983139287886259/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-497501501729681440133745697380000000000000)
      constant := (11336961614424077145657701265185793055555420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29863125692764953999/100000000000000000000)
  centralHi := (14931562846382477/50000000000000000)
  directionLo := (21116418684780313781/50000000000000000000)
  directionHi := (42232837369560627563/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree003.table
  base := (2955618322027060653185045630093531359577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-951095389068173022173446900000000000000)
      constant := (13066569128324210725614205700374125438308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree003.table
  base := (11700566743070667311882678851875701793481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-647218100106567419543823763430000000000000)
      constant := (8762997277293271820044502437661724412393156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/50000000000000000000)
  centralHi := (42232837369560627563/100000000000000000000)
  directionLo := (12931112743171106689/25000000000000000000)
  directionHi := (51724450972684426757/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree004.table
  base := (8499722623151423665469839738027069179633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-10534143315374690993979633960000000000000)
      constant := (94059033442635942069608318282243622616697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree004.table
  base := (16754454866895338223820943440668617283227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-796934698483453398953901829480000000000000)
      constant := (7002432865052074350780794222045992641730726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12931112743171106689/25000000000000000000)
  centralHi := (51724450972684426757/100000000000000000000)
  directionLo := (59726251385529907999/100000000000000000000)
  directionHi := (14931562846382477/25000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree005.table
  base := (11921067354086420135745307127184425333763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-25016856258271649576796491640000000000000)
      constant := (157774380151664383237385871944659828003867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree005.table
  base := (11689881577538440376409626012594005628659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-946651296860339378363979895530000000000000)
      constant := (5877390841682450063030056050350523902486742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/100000000000000000000)
  centralHi := (14931562846382477/25000000000000000)
  directionLo := (267103916278571747/400000000000000000)
  directionHi := (66775979069642936751/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree006.table
  base := (8037924161511812076757245086149023503329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-3218380653977101907292635040000000000000)
      constant := (15646687274057196254144820286149023503329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree006.table
  base := (244628767671730477679991993729468133787/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1096367895237225357774057961580000000000000)
      constant := (5259670155413959117821466294952927335040192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/400000000000000000)
  centralHi := (66775979069642936751/100000000000000000000)
  directionLo := (2925976802874901777/4000000000000000000)
  directionHi := (36574710035936272213/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree007.table
  base := (100891996862678293766483587392368697353/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-16456997756658092377235469540000000000000)
      constant := (67253370200408528549053671303282956904425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree007.table
  base := (48591543693778488647165881970119926557/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1246084493614111337184136027630000000000000)
      constant := (5044484904297358113696733447733803517626600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925976802874901777/4000000000000000000)
  centralHi := (36574710035936272213/50000000000000000000)
  directionLo := (79010403954119537181/100000000000000000000)
  directionHi := (39505201977059768591/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree008.table
  base := (136213546324938783038959470603855487119/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-18431282570419226171654081400000000000000)
      constant := (68441316851242842441397733474346993840710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree008.table
  base := (160212776968338625851469748117800398969/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1395801091990997316594214093680000000000000)
      constant := (5157617535832601282971912095021064557624352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79010403954119537181/100000000000000000000)
  centralHi := (39505201977059768591/50000000000000000000)
  directionLo := (21116418684780313781/25000000000000000000)
  directionHi := (675725397912970041/800000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree009.table
  base := (914121270657214129292655335625907346221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-4534570529817857770238376280000000000000)
      constant := (16275835566997557984211241855625907346221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree009.table
  base := (97062377345304510387429839518977718281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1545517690367883296004292159730000000000000)
      constant := (5543510404238768058156194357003065750231824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/25000000000000000000)
  centralHi := (675725397912970041/800000000000000000)
  directionLo := (44794688539147430999/50000000000000000000)
  directionHi := (89589377078294861999/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree010.table
  base := (-254130487701924789830216312064359100313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-22379852197941493760491305120000000000000)
      constant := (81102346471588175480849691991420768097183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree010.table
  base := (-624764522342405194672200590721212319141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1695234288744769275414370225780000000000000)
      constant := (6160521012623628244727583958711230236130342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44794688539147430999/50000000000000000000)
  centralHi := (89589377078294861999/100000000000000000000)
  directionLo := (94435495241030970819/100000000000000000000)
  directionHi := (4721774762051548541/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree011.table
  base := (-163504276281898259071013248848593493823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-24354137011702627554909916980000000000000)
      constant := (91609824831434784036259783301813292777965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree011.table
  base := (-1732868604391631903426188075012384790243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1844950887121655254824448291830000000000000)
      constant := (6977390305538344026383723190139563940897866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94435495241030970819/100000000000000000000)
  centralHi := (4721774762051548541/5000000000000000000)
  directionLo := (99044782990123520443/100000000000000000000)
  directionHi := (24761195747530880111/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree012.table
  base := (-2535726975527640079070968198167758504511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-5850760405658613633184117520000000000000)
      constant := (23211318256289175179270112121832241495489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree012.table
  base := (-1308673418429133723403310456043343488977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-1994667485498541234234526357880000000000000)
      constant := (7970615922981033492692907206014699801451548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99044782990123520443/100000000000000000000)
  centralHi := (24761195747530880111/25000000000000000000)
  directionLo := (103448901945368853513/100000000000000000000)
  directionHi := (51724450972684426757/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree013.table
  base := (-1631405682803595858597304280330996005957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-28302706639224895143747140700000000000000)
      constant := (119389428552839524766184346097021035946387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree013.table
  base := (-1665283358144891411919211608639402620209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-164952621836571324126508032610000000000000)
      constant := (701730588547588572768054742719501063749132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103448901945368853513/100000000000000000000)
  centralHi := (51724450972684426757/50000000000000000000)
  directionLo := (26918257732722527187/25000000000000000000)
  directionHi := (107673030930890108749/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree014.table
  base := (-482002064991973420563183251334882191381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-30276991452986028938165752560000000000000)
      constant := (136246571389097819047256451991944241110284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree014.table
  base := (-3912036465664503395560696254006617449783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-2294100682252313193054682489980000000000000)
      constant := (10419681710584523914227920311120763301973346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26918257732722527187/25000000000000000000)
  centralHi := (107673030930890108749/100000000000000000000)
  directionLo := (11173758484049266577/10000000000000000000)
  directionHi := (111737584840492665771/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree015.table
  base := (-4345448207166904176868034415655776269613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-7166950281499369496129858760000000000000)
      constant := (34419307711807894210787022184344223730387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree015.table
  base := (-2195808194503946697014694859098895623637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-2443817280629199172464760556030000000000000)
      constant := (11852075318618043986987622176092896558421388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11173758484049266577/10000000000000000000)
  centralHi := (111737584840492665771/100000000000000000000)
  directionLo := (23131877694755499209/20000000000000000000)
  directionHi := (57829694236888748023/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree016.table
  base := (-4753965642170611719650251181574487008571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-68451122161016593054005952560000000000000)
      constant := (350415004056074652851768142565829616922861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree016.table
  base := (-95838329807405582383986548612639834371/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-2593533879006085151874838622080000000000000)
      constant := (13412036293850201374879086798846386799130100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23131877694755499209/20000000000000000000)
  centralHi := (57829694236888748023/50000000000000000000)
  directionLo := (59726251385529907999/50000000000000000000)
  directionHi := (119452502771059815999/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree017.table
  base := (-509895746492482484662247664819961422621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-36199845894269430321421588140000000000000)
      constant := (197130174483902609637317244823101735982055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree017.table
  base := (-320630565988962928219497011878340686873/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-2743250477382971131284916688130000000000000)
      constant := (15093767163588745835113106513405683565390816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/50000000000000000000)
  centralHi := (119452502771059815999/100000000000000000000)
  directionLo := (123128821542366478273/100000000000000000000)
  directionHi := (61564410771183239137/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree018.table
  base := (-2696837735577820658589304976357505050397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-4241570078670062679537800000000000000000)
      constant := (24510585443329325962840952703642494949603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree018.table
  base := (-5419170865942634751037525812659574003911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-2892967075759857110694994754180000000000000)
      constant := (16892861495999206309585932825896063986678082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123128821542366478273/100000000000000000000)
  centralHi := (61564410771183239137/50000000000000000000)
  directionLo := (63349256054340941343/50000000000000000000)
  directionHi := (126698512108681882687/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree019.table
  base := (-1412059432709574602270413271365200730121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-40148415521791697910258811860000000000000)
      constant := (245557254231332730760704550855426386857822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree019.table
  base := (-5669089753388058098072758528580520749443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3042683674136743090105072820230000000000000)
      constant := (18805963683642470593557277678533533986688266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63349256054340941343/50000000000000000000)
  centralHi := (126698512108681882687/100000000000000000000)
  directionLo := (26034069406603100597/20000000000000000000)
  directionHi := (65085173516507751493/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree020.table
  base := (-11465594206224380323261912838650602061/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-42122700335552831704677423720000000000000)
      constant := (271981300254745611208421954419749012851456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree020.table
  base := (-1177484133748890378663393772954122474181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3192400272513629069515150886280000000000000)
      constant := (20830513393220884736790771409207533018634110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26034069406603100597/20000000000000000000)
  centralHi := (65085173516507751493/50000000000000000000)
  directionLo := (267103916278571747/200000000000000000)
  directionHi := (133551958139285873501/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree021.table
  base := (-6066047040991255125627902981973172371991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-9799330033180881222021341240000000000000)
      constant := (66631269507344044698329553618026827628009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree021.table
  base := (-3039977273398406366736702829216998908327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3342116870890515048925228952330000000000000)
      constant := (22964553288777119889600715910943058737970948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/200000000000000000)
  centralHi := (133551958139285873501/100000000000000000000)
  directionLo := (8553127123442247507/6250000000000000000)
  directionHi := (136850033975075960113/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree022.table
  base := (-3119890601965983829406652164978346018193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-46071269963075099293514647440000000000000)
      constant := (329114994087278016340685579555194885836263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree022.table
  base := (-3125563533066141092096074719565008557119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3491833469267401028335307018380000000000000)
      constant := (25206584110948722202797383964749054215387556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553127123442247507/6250000000000000000)
  centralHi := (136850033975075960113/100000000000000000000)
  directionLo := (140070475386932712809/100000000000000000000)
  directionHi := (14007047538693271281/10000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree023.table
  base := (-639509101063745910974430020040729526193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-48045554776836233087933259300000000000000)
      constant := (359788374870407082271978733718167171321315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree023.table
  base := (-320217119283564835545408092728725230351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3641550067644287007745385084430000000000000)
      constant := (27555455254020584151063758533697567442827240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140070475386932712809/100000000000000000000)
  centralHi := (14007047538693271281/10000000000000000000)
  directionLo := (71609259791006081199/50000000000000000000)
  directionHi := (143218519582012162399/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree024.table
  base := (-6534677427455352211782504862626836142973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-11115519909021637084967082480000000000000)
      constant := (87077489063082465919163375457373163857027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree024.table
  base := (-3271109014854121707270592233988218732503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3791266666021172987155463150480000000000000)
      constant := (30010281994781202894288966969423964136827972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71609259791006081199/50000000000000000000)
  centralHi := (143218519582012162399/100000000000000000000)
  directionLo := (2925976802874901777/2000000000000000000)
  directionHi := (146298840143745088851/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree025.table
  base := (-6660626108337799680308695450867428952159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-103988248808717001353540966040000000000000)
      constant := (850573172769770744428482899942193139430569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree025.table
  base := (-1666692618060002986530990352405903206747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-3940983264398058966565541216530000000000000)
      constant := (32570382765019629730423941755890968864478056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925976802874901777/2000000000000000000)
  centralHi := (146298840143745088851/100000000000000000000)
  directionLo := (149315628463824769997/100000000000000000000)
  directionHi := (74657814231912384999/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree026.table
  base := (-3387275255153013445319646772889595972257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-53968409218119634471189094880000000000000)
      constant := (460094771116854394817073617843993636249687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree026.table
  base := (-6779556046947182018440681869850689980299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-314669220213457303536586098660000000000000)
      constant := (2710402424919371439734432842058882060512226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149315628463824769997/100000000000000000000)
  centralHi := (74657814231912384999/50000000000000000000)
  directionLo := (76136330322141275627/50000000000000000000)
  directionHi := (30454532128856510251/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree027.table
  base := (-6877701037974933515943941568003843429023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-12431709784862392947912823720000000000000)
      constant := (110281695146446914647881844951996156570977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree027.table
  base := (-3440889070971505981767587161127153338219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-4240416461151830925385697348630000000000000)
      constant := (38004421526395518536429208517971794343363956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76136330322141275627/50000000000000000000)
  centralHi := (30454532128856510251/20000000000000000000)
  directionLo := (155173352918053280269/100000000000000000000)
  directionHi := (15517335291805328027/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree028.table
  base := (-1394209687450394883046927441388249005529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-115833957691283804120052637200000000000000)
      constant := (1067601578309543977287743027377528794751195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree028.table
  base := (-3487184451884648536998995533017236744049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-4390133059528716904795775414680000000000000)
      constant := (40877637706819572381173079792380347961022876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155173352918053280269/100000000000000000000)
  centralHi := (15517335291805328027/10000000000000000000)
  directionLo := (158020807908239074363/100000000000000000000)
  directionHi := (39505201977059768591/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree029.table
  base := (-352767381706501662165221437725809705293/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-59891263659403035854444930460000000000000)
      constant := (572690856937169036555714534744677126523630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree029.table
  base := (-7058051633089191657547068251161746690421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-4539849657905602884205853480730000000000000)
      constant := (43854635589599844094770578351301079618637702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158020807908239074363/100000000000000000000)
  centralHi := (39505201977059768591/25000000000000000000)
  directionLo := (20102231688964004449/12500000000000000000)
  directionHi := (160817853511712035593/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree030.table
  base := (-3565593348244275425029238059321842238491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-6873949830351574405429282480000000000000)
      constant := (68103909466749419536269349540678157761509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree030.table
  base := (-1783347131866192539523927690188753025143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-4689566256282488863615931546780000000000000)
      constant := (46935225151960352515179007144239805910006664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20102231688964004449/12500000000000000000)
  centralHi := (160817853511712035593/100000000000000000000)
  directionLo := (32713415159078912293/20000000000000000000)
  directionHi := (81783537897697280733/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree031.table
  base := (-1439804891349497062374045508862509659113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-127679666573850606886564308360000000000000)
      constant := (1309063418399218790224639659901187065339915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree031.table
  base := (-7200817282906539077297328003366703151263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-4839282854659374843026009612830000000000000)
      constant := (50119258452649546444839513791105804334873106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32713415159078912293/20000000000000000000)
  centralHi := (81783537897697280733/50000000000000000000)
  directionLo := (166270846994890321109/100000000000000000000)
  directionHi := (16627084699489032111/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree032.table
  base := (-7259219475681771136463543625944297375213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-131628236201372874475401532080000000000000)
      constant := (1394957630820551378257288428646501323623083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree032.table
  base := (-7260679207944590757117100928788244795639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-4988999453036260822436087678880000000000000)
      constant := (53406620129384254672167867130869573259074018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166270846994890321109/100000000000000000000)
  centralHi := (16627084699489032111/10000000000000000000)
  directionLo := (21116418684780313781/12500000000000000000)
  directionHi := (168931349478242510249/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree033.table
  base := (-1462410476331802005973201720367426994647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-15064089536543904673804306200000000000000)
      constant := (164838942445575433377394037758162865026765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree033.table
  base := (-3656620429669151841647471835379778043327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-5138716051413146801846165744930000000000000)
      constant := (56797220085979807268983976186327020042710948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21116418684780313781/12500000000000000000)
  centralHi := (168931349478242510249/100000000000000000000)
  directionLo := (171550596363527644699/100000000000000000000)
  directionHi := (1715505963635276447/1000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree034.table
  base := (-7357743132051749833301599963453121103969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-139525375456417409653075979520000000000000)
      constant := (1574839992351748426071397596008921910064279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree034.table
  base := (-919838840419677180864123933828152913759/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-5288432649790032781256243810980000000000000)
      constant := (60290987854077032253502079245903674521195664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171550596363527644699/100000000000000000000)
  centralHi := (1715505963635276447/1000000000000000000)
  directionLo := (17413044934423118483/10000000000000000000)
  directionHi := (174130449344231184831/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree035.table
  base := (-1849116093768219585566874776908976461983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-71736972541969838620956601620000000000000)
      constant := (834412304005671982561183782315638423684306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree035.table
  base := (-924656512594173043356083863971094915651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-5438149248166918760666321877030000000000000)
      constant := (63887868238021938748701606124415909348079696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17413044934423118483/10000000000000000000)
  centralHi := (174130449344231184831/100000000000000000000)
  directionLo := (176672634171129460127/100000000000000000000)
  directionHi := (5521019817847795629/3125000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree036.table
  base := (-3714175905626329151615420152327496124831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-8190139706192330268375023720000000000000)
      constant := (98083505982455175157291779847672503875169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree036.table
  base := (-1857248269307976234812703515245563121441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-5587865846543804740076399943080000000000000)
      constant := (67587817944845999966604251583287998659811768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176672634171129460127/100000000000000000000)
  centralHi := (5521019817847795629/3125000000000000000)
  directionLo := (179178754156589723997/100000000000000000000)
  directionHi := (89589377078294861999/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree037.table
  base := (-1863378060529722549147304232143226935659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-75685542169492106209793825340000000000000)
      constant := (932437265078272892437236336761421915158138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree037.table
  base := (-7454034252152130344477609695442004041967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-5737582444920690719486478009130000000000000)
      constant := (71390802971965822828528947815834352633815154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179178754156589723997/100000000000000000000)
  centralHi := (89589377078294861999/50000000000000000000)
  directionLo := (90825151000768363171/50000000000000000000)
  directionHi := (181650302001536726343/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree038.table
  base := (-1868007458199725256657343327147129936099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-77659826983253240004212437200000000000000)
      constant := (983469058971127959106724387231351661150218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree038.table
  base := (-7472454739664573608800913151383594775577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-5887299043297576698896556075180000000000000)
      constant := (75296796578798533924835807718407344965854974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90825151000768363171/50000000000000000000)
  centralHi := (181650302001536726343/100000000000000000000)
  directionLo := (23011083774112862257/12500000000000000000)
  directionHi := (184088670192902898057/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree039.table
  base := (-7483970992808839429603466064852070531371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-17696469288225416399695788680000000000000)
      constant := (230188141483964246124656770055147929468629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree039.table
  base := (-3742158418049046791614038796624594630279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-464385818590343282946664164710000000000000)
      constant := (6100444439168075304914180455494271079225492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23011083774112862257/12500000000000000000)
  centralHi := (184088670192902898057/100000000000000000000)
  directionLo := (46623790044309229127/25000000000000000000)
  directionHi := (186495160177236916509/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree040.table
  base := (-468086761618464254359795665255654127539/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-81608396610775507593049660920000000000000)
      constant := (1089569762111546085810826011301592902817192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree040.table
  base := (-748966965577747533425338188323072196657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-6186732240051348657716712207280000000000000)
      constant := (83417729762483380593199496169468015975299340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46623790044309229127/25000000000000000000)
  centralHi := (186495160177236916509/100000000000000000000)
  directionLo := (94435495241030970819/50000000000000000000)
  directionHi := (188870990482061941639/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree041.table
  base := (-3744161454210408538427670006895542515799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-83582681424536641387468272780000000000000)
      constant := (1144638248538619218272388247037940117357809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree041.table
  base := (-7488551967586315011340104963037200653117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-6336448838428234637126790273330000000000000)
      constant := (87632639634811083314262670180237176179246454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94435495241030970819/50000000000000000000)
  centralHi := (188870990482061941639/100000000000000000000)
  directionLo := (191217303928846907229/100000000000000000000)
  directionHi := (19121730392884690723/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree042.table
  base := (-7480808021135203009237234920304620339943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-19012659164066172262641529920000000000000)
      constant := (266900432907929471207360319799695379660057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree042.table
  base := (-935124301401654911508149722585114921013/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-6486165436805120616536868339380000000000000)
      constant := (91950496969953331310052858533304849253580848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191217303928846907229/100000000000000000000)
  centralHi := (19121730392884690723/10000000000000000000)
  directionLo := (1548281392470170103/800000000000000000)
  directionHi := (48383793514692815719/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree043.table
  base := (-1866717394316116949095498562110109599071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-87531251052058908976305496500000000000000)
      constant := (1258810743513219823610367482502018027216722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree043.table
  base := (-7467021231161840440243506363648117318899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-6635882035182006595946946405430000000000000)
      constant := (96371293573267910395400643271380686346212138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1548281392470170103/800000000000000000)
  centralHi := (48383793514692815719/25000000000000000000)
  directionLo := (97912805436904890437/50000000000000000000)
  directionHi := (1566604886990478247/800000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree044.table
  base := (-186163206440643395134661362065443791797/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-89505535865820042770724108360000000000000)
      constant := (1317914541757553768152190613068220117476540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree044.table
  base := (-1489330327053899394626216453746058927539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-6785598633558892575357024471480000000000000)
      constant := (100895022952505786631473478968269160412459090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97912805436904890437/50000000000000000000)
  centralHi := (1566604886990478247/800000000000000000)
  directionLo := (99044782990123520443/50000000000000000000)
  directionHi := (198089565980247040887/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree045.table
  base := (-1854950124669992188927551064827328691937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-10164424519953464062793635580000000000000)
      constant := (153151474317178902924558075770345342616126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree045.table
  base := (-7419900860402147375678713542415785014611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-6935315231935778554767102537530000000000000)
      constant := (105521679957606272810357999264257214665061482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99044782990123520443/50000000000000000000)
  centralHi := (198089565980247040887/100000000000000000000)
  directionLo := (801311748835715241/400000000000000000)
  directionHi := (200327937208928810251/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree046.table
  base := (-7386699380297360742680277885980401194231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-186908210986684620719122664160000000000000)
      constant := (2880313731889946049375784069426176389251921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree046.table
  base := (-3693390504727697619572538394737518261801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-7085031830312664534177180603580000000000000)
      constant := (110251260497790654918208771466932437655022524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (801311748835715241/400000000000000000)
  centralHi := (200327937208928810251/100000000000000000000)
  directionLo := (40508314555175658373/20000000000000000000)
  directionHi := (101270786387939145933/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree047.table
  base := (-1469447065045007992350059464078398790981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-190856780614206888307959887880000000000000)
      constant := (3006590572252560772746514745196472054405855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree047.table
  base := (-7347301709495180297531205397977793822193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-7234748428689550513587258669630000000000000)
      constant := (115083761319110645324933446291127255688098766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40508314555175658373/20000000000000000000)
  centralHi := (101270786387939145933/50000000000000000000)
  directionLo := (204731275037958674717/100000000000000000000)
  directionHi := (102365637518979337359/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree048.table
  base := (-3650708325399617025255598975507995560801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-10822519457873841994266506200000000000000)
      constant := (174197610218946576334217720704492004439199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree048.table
  base := (-912683828727988350010225191777084294201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-7384465027066436492997336735680000000000000)
      constant := (120019179829342031394287314404634764068480496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204731275037958674717/100000000000000000000)
  centralHi := (102365637518979337359/50000000000000000000)
  directionLo := (103448901945368853513/50000000000000000000)
  directionHi := (206897803890737707027/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree049.table
  base := (-1449850000913212057387876791635183359419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-198753919869251423485634335320000000000000)
      constant := (3267212907127463797682209114256416748826145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree049.table
  base := (-3624646945103237740032420144966214303939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-7534181625443322472407414801730000000000000)
      constant := (125057513960004276678425800226446589130537236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103448901945368853513/50000000000000000000)
  centralHi := (206897803890737707027/100000000000000000000)
  directionLo := (52260469962338669499/25000000000000000000)
  directionHi := (209041879849354677997/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree050.table
  base := (-3595370354288977998850773882115900210687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-101351244748386845537235779520000000000000)
      constant := (1700779146956682553902692469060956898103817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree050.table
  base := (-7190776382859745850626374638749369051391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-7683898223820208451817492867780000000000000)
      constant := (130198762057528082661905537851477713260629842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52260469962338669499/25000000000000000000)
  centralHi := (209041879849354677997/100000000000000000000)
  directionLo := (211164186847803137811/100000000000000000000)
  directionHi := (52791046711950784453/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree051.table
  base := (-1781473257941391568223038247615219876319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-11480614395794219925739376820000000000000)
      constant := (196588505882131472143033126204769560247362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree051.table
  base := (-1781480506664647593804857250341965111601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-7833614822197094431227570933830000000000000)
      constant := (135442922797333742452079405025531413169115448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211164186847803137811/100000000000000000000)
  centralHi := (52791046711950784453/25000000000000000000)
  directionLo := (213265374787460034137/100000000000000000000)
  directionHi := (106632687393730017069/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree052.table
  base := (-1763677601400382056959538497717730694727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-105299814375909113126073003240000000000000)
      constant := (1839158656069607117975950262881080847494914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree052.table
  base := (-7054733968004805969365825227796637376981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-614102416967229262356742230760000000000000)
      constant := (10829999624302880668577001997177287428198494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213265374787460034137/100000000000000000000)
  centralHi := (106632687393730017069/50000000000000000000)
  directionLo := (215346061861780217497/100000000000000000000)
  directionHi := (107673030930890108749/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree053.table
  base := (-3488597797503417331526590056994892043869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-107274099189670246920491615100000000000000)
      constant := (1910365443905809692366337518107045971605179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree053.table
  base := (-6977214739682965712962684002952893352827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-8133048018950866390047727065930000000000000)
      constant := (146239978157258015679165173873295672046744474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215346061861780217497/100000000000000000000)
  centralHi := (107673030930890108749/50000000000000000000)
  directionLo := (217406836680725269753/100000000000000000000)
  directionHi := (108703418340362634877/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree054.table
  base := (-430834427118575924993957393976097595467/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-12138709333714597857212247440000000000000)
      constant := (220324100710574465662479167808191219236264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree054.table
  base := (-6893366386590818787226724367597889314857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-8282764617327752369457805131980000000000000)
      constant := (151792871230120004191820597719726913411578334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217406836680725269753/100000000000000000000)
  centralHi := (108703418340362634877/50000000000000000000)
  directionLo := (8777930408624705331/4000000000000000000)
  directionHi := (54862065053904408319/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree055.table
  base := (-6803177932767903575402516635469678832157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-222445337634385029018657677640000000000000)
      constant := (4113626070780920113094624946080772890510587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree055.table
  base := (-6803190565327739218812450192766395337079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-8432481215704638348867883198030000000000000)
      constant := (157448673774592825808458075194188708376067298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8777930408624705331/4000000000000000000)
  centralHi := (54862065053904408319/25000000000000000000)
  directionLo := (221470867582631073359/100000000000000000000)
  directionHi := (2768385844782888417/1250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree056.table
  base := (-335333918207391954657608642821345561499/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-113196953630953648303747450680000000000000)
      constant := (2132053824265299067655131116546078899465090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree056.table
  base := (-1676672155783653148270380609122120379681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-8582197814081524328277961264080000000000000)
      constant := (163207385335309061201225364892866893246671288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221470867582631073359/100000000000000000000)
  centralHi := (2768385844782888417/1250000000000000000)
  directionLo := (223475169680985331541/100000000000000000000)
  directionHi := (111737584840492665771/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree057.table
  base := (-825481666315483757057806856222059897491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-12796804271634975788685118060000000000000)
      constant := (245404363067610711680096965035111760410036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree057.table
  base := (-6603861660510892455037665126585879117347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-8731914412458410307688039330130000000000000)
      constant := (169069005540299895071911208094357722858336714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223475169680985331541/100000000000000000000)
  centralHi := (111737584840492665771/50000000000000000000)
  directionLo := (112730827350027756153/50000000000000000000)
  directionHi := (225461654700055512307/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree058.table
  base := (-3247351909184176656017928420807001434053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-117145523258475915892584674400000000000000)
      constant := (2286569360980926463134375955332736987093523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree058.table
  base := (-50739926413425284532899492074187510627/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-8881631010835296287098117396180000000000000)
      constant := (175033534084195219546466378026477351540233472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112730827350027756153/50000000000000000000)
  centralHi := (225461654700055512307/100000000000000000000)
  directionLo := (113715394753996415739/50000000000000000000)
  directionHi := (227430789507992831479/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree059.table
  base := (-3189615320571173179506924346823666842139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-119119808072237049687003286260000000000000)
      constant := (2365844100722014482949504312218586998420749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree059.table
  base := (-1275847226052422256432778854788773461631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-9031347609212182266508195462230000000000000)
      constant := (181100970714879189648666931445100722849843610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113715394753996415739/50000000000000000000)
  centralHi := (227430789507992831479/100000000000000000000)
  directionLo := (45876604186609462043/20000000000000000000)
  directionHi := (28672877616630913777/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree060.table
  base := (-2444310341229253116955914611150329797/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-13454899209555353720157988680000000000000)
      constant := (271829275977289532227467728497727577859840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree060.table
  base := (-3128719464135628582065143454054573313291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-9181064207589068245918273528280000000000000)
      constant := (187271315222883288416859660106559108440215284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45876604186609462043/20000000000000000000)
  centralHi := (28672877616630913777/12500000000000000000)
  directionLo := (231318776947554992091/100000000000000000000)
  directionHi := (57829694236888748023/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree061.table
  base := (-6129315878821857070091228127651599565407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-246136755399518634551681019960000000000000)
      constant := (5056855015334241858783103937851135603911337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree061.table
  base := (-306465974673030833396900466102695521303/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-9330780805965954225328351594330000000000000)
      constant := (193544567432949532851626802616139528275991720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231318776947554992091/100000000000000000000)
  centralHi := (57829694236888748023/25000000000000000000)
  directionLo := (116619233881738582979/50000000000000000000)
  directionHi := (233238467763477165959/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree062.table
  base := (-5994875330518457933805202382020789724341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-250085325027040902140518243680000000000000)
      constant := (5223472340411158963240411257441812892480931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree062.table
  base := (-1498719565749573792738725397108688330023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-9480497404342840204738429660380000000000000)
      constant := (199920727197315103335418029029284053377808904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116619233881738582979/50000000000000000000)
  centralHi := (233238467763477165959/100000000000000000000)
  directionLo := (235142486847435666589/100000000000000000000)
  directionHi := (23514248684743566659/10000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree063.table
  base := (-1170822645975252667207971335197056565089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-28225988294951463303261718600000000000000)
      constant := (599197659912311859841880437684014717174555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree063.table
  base := (-5854115608531442089065407642360089476443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-9630214002719726184148507726430000000000000)
      constant := (206399794390363263365664397295926039756962266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235142486847435666589/100000000000000000000)
  centralHi := (23514248684743566659/10000000000000000000)
  directionLo := (47406242372471722309/20000000000000000000)
  directionHi := (118515605931179305773/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree064.table
  base := (-713378739962789821768227623480535298419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-128991232141042718659096345560000000000000)
      constant := (2782387404323960888558243156594700729256916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree064.table
  base := (-5707031848801770279470905381003803982347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-9779930601096612163558585792480000000000000)
      constant := (212981768904359313996631841686820714253966714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47406242372471722309/20000000000000000000)
  centralHi := (118515605931179305773/50000000000000000000)
  directionLo := (59726251385529907999/25000000000000000000)
  directionHi := (238905005542119631997/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree065.table
  base := (-5553625695465020814017173098870268277789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-261931033909607704907029914840000000000000)
      constant := (5739459946063288504366051679510167585499899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree065.table
  base := (-173550851865948207062553026243703768161/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-763819015344115241766820296810000000000000)
      constant := (16897434665080668921045055393383988464890048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/25000000000000000000)
  centralHi := (238905005542119631997/100000000000000000000)
  directionLo := (6019105412622693593/2500000000000000000)
  directionHi := (240764216504907743721/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree066.table
  base := (-5393900814169088086775044084770976714897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-29542178170792219166207459840000000000000)
      constant := (657426038793762717560614428715229023285103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree066.table
  base := (-337118880147157113441120915182418949113/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10079363797850384122378741924580000000000000)
      constant := (226454439533940503412522780990468478323196896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6019105412622693593/2500000000000000000)
  centralHi := (240764216504907743721/100000000000000000000)
  directionLo := (242609180010493355417/100000000000000000000)
  directionHi := (121304590005246677709/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree067.table
  base := (-1306963875365465231403891588852123525991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-134914086582326120042352181140000000000000)
      constant := (3048449007929411786678077829140661776532162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree067.table
  base := (-5227856529451877354443773910765617851191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10229080396227270101788819990630000000000000)
      constant := (233345135496136189707805219885554971166297442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242609180010493355417/100000000000000000000)
  centralHi := (121304590005246677709/50000000000000000000)
  directionLo := (48888043733209798797/20000000000000000000)
  directionHi := (122220109333024496993/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree068.table
  base := (-5055489957329090258765356609961780614861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-273776742792174507673541586000000000000000)
      constant := (6279650944408294091943889528750343974466251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree068.table
  base := (-631936348810065680841037785956505994507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10378796994604156081198898056680000000000000)
      constant := (240338738468592159694964685175473607790853072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48888043733209798797/20000000000000000000)
  centralHi := (122220109333024496993/50000000000000000000)
  directionLo := (123128821542366478273/50000000000000000000)
  directionHi := (246257643084732956547/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree069.table
  base := (-487680436066525564062117990682095191417/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-15429184023316487514576600540000000000000)
      constant := (359171840732345872101064476906589524042915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree069.table
  base := (-2438402517898577917022216717454509419099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10528513592981042060608976122730000000000000)
      constant := (247435248393727849537160252042694501632689076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123128821542366478273/50000000000000000000)
  centralHi := (246257643084732956547/100000000000000000000)
  directionLo := (15503859531302702023/6250000000000000000)
  directionHi := (248061752500843232369/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree070.table
  base := (-29323742955908633479696558090672956239/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-140836941023609521425608016720000000000000)
      constant := (3326612290363671586205926553774715471507920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree070.table
  base := (-2345899709970416329221621729383577477391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10678230191357928040019054188780000000000000)
      constant := (254634665219309055554378656763311701625283684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15503859531302702023/6250000000000000000)
  centralHi := (248061752500843232369/100000000000000000000)
  directionLo := (124926417672495798219/50000000000000000000)
  directionHi := (249852835344991596439/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree071.table
  base := (-225023682058957859438476487714262854697/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-142811225837370655220026628580000000000000)
      constant := (3422022642860279653843723406805716343077270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree071.table
  base := (-2250237042143796574211214891643511749811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10827946789734814019429132254830000000000000)
      constant := (261936988897550677163387677607992736057127764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124926417672495798219/50000000000000000000)
  centralHi := (249852835344991596439/100000000000000000000)
  directionLo := (251631169782428504839/100000000000000000000)
  directionHi := (6290779244560712621/2500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree072.table
  base := (-4302828800291461460480462540696933039219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-32174557922473730892098942320000000000000)
      constant := (781950582994172244303521814579303066960781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree072.table
  base := (-537853644898409129507721229053466736479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-10977663388111699998839210320880000000000000)
      constant := (269342219384394469886744349807439425944560784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251631169782428504839/100000000000000000000)
  centralHi := (6290779244560712621/2500000000000000000)
  directionLo := (253397024217363765373/100000000000000000000)
  directionHi := (126698512108681882687/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree073.table
  base := (-81977289500883534015573059018063478589/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-146759795464892922808863852300000000000000)
      constant := (3616877231642729451392276006340935717317475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree073.table
  base := (-2049432382843536223365523368508202057213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-11127379986488585978249288386930000000000000)
      constant := (276850356638926480082073686663432205409324012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253397024217363765373/100000000000000000000)
  centralHi := (126698512108681882687/50000000000000000000)
  directionLo := (127575328882935979777/50000000000000000000)
  directionHi := (51030131553174391911/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree074.table
  base := (-3888580781590938971259539449473218244247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-297468160557308113206564928320000000000000)
      constant := (7432642933688902695291654911834741035801777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree074.table
  base := (-3888581016925055390325769253453970341769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-11277096584865471957659366452980000000000000)
      constant := (284461400622906042114031006216307558024482078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127575328882935979777/50000000000000000000)
  centralHi := (51030131553174391911/20000000000000000000)
  directionLo := (64223080174935452881/25000000000000000000)
  directionHi := (10275692827989672461/4000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree075.table
  base := (-458997228592243395114015436996910601719/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-16745373899157243377522341780000000000000)
      constant := (424123369843256988125116889752012357593124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree075.table
  base := (-3671978019259826887101622955447556492167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-11426813183242357937069444519030000000000000)
      constant := (292175351300383947485769886742152475905647554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64223080174935452881/25000000000000000000)
  centralHi := (10275692827989672461/4000000000000000000)
  directionLo := (258622254863422133783/100000000000000000000)
  directionHi := (32327781857927766723/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree076.table
  base := (-1724527859484604060619607084397539496359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-152682649906176324192119687880000000000000)
      constant := (3919243816416136057001187021040422144532769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree076.table
  base := (-3449055873189157511965545065407252724481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-11576529781619243916479522585080000000000000)
      constant := (299992208637391949742971783459792348579125422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258622254863422133783/100000000000000000000)
  centralHi := (32327781857927766723/12500000000000000000)
  directionLo := (26034069406603100597/10000000000000000000)
  directionHi := (260340694066031005971/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree077.table
  base := (-1609907274641418741672131967581292877879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-154656934719937457986538299740000000000000)
      constant := (4022721929888429318931266959631768364099089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree077.table
  base := (-3219814674099609262984827141834897228407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-11726246379996129895889600651130000000000000)
      constant := (307911972601689390930289951822453554736798434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26034069406603100597/10000000000000000000)
  centralHi := (260340694066031005971/100000000000000000000)
  directionLo := (65511966112556791321/25000000000000000000)
  directionHi := (52409572890045433057/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree078.table
  base := (-2984254411875663017825223963245502911737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-34806937674155242617990424800000000000000)
      constant := (917232148575845989766355787396754497088263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree078.table
  base := (-2984254512880691383022772130795747175499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-913535613721001221176898362860000000000000)
      constant := (24302664858658124378741276571874310573437026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65511966112556791321/25000000000000000000)
  centralHi := (52409572890045433057/20000000000000000000)
  directionLo := (263743984839591191901/100000000000000000000)
  directionHi := (131871992419795595951/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree079.table
  base := (-1371187697352950877731469033934440340079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-158605504347459725575375523460000000000000)
      constant := (4233712032128956985414675474834590036939289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree079.table
  base := (-1371187738215144954434623393232980174507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12025679576749901854709756783230000000000000)
      constant := (324060220290619142242576739332618255402033268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263743984839591191901/100000000000000000000)
  centralHi := (131871992419795595951/50000000000000000000)
  directionLo := (265429267066027190929/100000000000000000000)
  directionHi := (26542926706602719093/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree080.table
  base := (-2494177581957717675710478678727668558207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-321159578322441718739588270640000000000000)
      constant := (8682448040245101350843902856691450982976137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree080.table
  base := (-249417764807271316278788242544485850767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12175396175126787834119834849280000000000000)
      constant := (332288703957716350674185276132199637824407540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265429267066027190929/100000000000000000000)
  centralHi := (26542926706602719093/10000000000000000000)
  directionLo := (267103916278571747/100000000000000000)
  directionHi := (267103916278571747001/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree081.table
  base := (-8748675993854322311062599964097941783/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-18061563774997999240468083020000000000000)
      constant := (494453403578723093685737788304595463451776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree081.table
  base := (-1119830553953196845746782747749073449657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12325112773503673813529912915330000000000000)
      constant := (340620094136773972017672574213765376348031868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/100000000000000000)
  centralHi := (267103916278571747001/100000000000000000000)
  directionLo := (67192032808721146499/25000000000000000000)
  directionHi := (268768131234884585997/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree082.table
  base := (-395765177968310754559115875724354061487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-329056717577486253917262718080000000000000)
      constant := (9120563736074098807741370942872404067233085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree082.table
  base := (-1978825933094860230677299500716809033079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12474829371880559792939990981380000000000000)
      constant := (349054390801710733560375074392932718546819298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67192032808721146499/25000000000000000000)
  centralHi := (268768131234884585997/100000000000000000000)
  directionLo := (135211052288296704283/50000000000000000000)
  directionHi := (270422104576593408567/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree083.table
  base := (-855836081567038473103177413320501677579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-166502643602504260753049970900000000000000)
      constant := (4671827727270982178827564091900115484901789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree083.table
  base := (-1711672198111862343689684028018576214421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12624545970257445772350069047430000000000000)
      constant := (357591593927354507949880274009323471239525702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135211052288296704283/50000000000000000000)
  centralHi := (270422104576593408567/100000000000000000000)
  directionLo := (26568947567341083/9765625000000000)
  directionHi := (272066023089572689921/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree084.table
  base := (-143819994666743810305123382961421017049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-18719658712918377171940953640000000000000)
      constant := (531635356620519104302437220845192894914755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree084.table
  base := (-11505599799594826995030583226898395361/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12774262568634331751760147113480000000000000)
      constant := (366231703489372014955967513969763542795997750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26568947567341083/9765625000000000)
  centralHi := (272066023089572689921/100000000000000000000)
  directionLo := (8553127123442247507/3125000000000000000)
  directionHi := (10948002718006076809/4000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree085.table
  base := (-144801163803796926964870501146205857971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-170451213230026528341887194620000000000000)
      constant := (4898953314663169361778048794258736589113044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree085.table
  base := (-1158409333295301320980499531210760831007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-12923979167011217731170225179530000000000000)
      constant := (374974719464208721395233099483544512839119634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8553127123442247507/3125000000000000000)
  centralHi := (10948002718006076809/4000000000000000000)
  directionLo := (137662207479085973601/50000000000000000000)
  directionHi := (275324414958171947203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree086.table
  base := (-174460064440750606562154109383131937701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-344850996087575324272611612960000000000000)
      constant := (10029066084402921118654399997077759062803455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree086.table
  base := (-21807508517172809075766704199770107063/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-13073695765388103710580303245580000000000000)
      constant := (383820641829037051578993878011994108152508240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137662207479085973601/50000000000000000000)
  centralHi := (275324414958171947203/100000000000000000000)
  directionLo := (55387846951547605713/20000000000000000000)
  directionHi := (138469617378869014283/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree087.table
  base := (-144968261926122492755902293891693502531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-19377753650838755103413824260000000000000)
      constant := (570161932433757710643805811072216612994938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree087.table
  base := (-57987306264374660886735802661910816093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-13223412363764989689990381311630000000000000)
      constant := (392769470561711394190631595681146491441605660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55387846951547605713/20000000000000000000)
  centralHi := (138469617378869014283/50000000000000000000)
  directionLo := (34818086630806780057/12500000000000000000)
  directionHi := (278544693046454240457/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree088.table
  base := (-281127550710937643287994458955737674469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-352748135342619859450286060400000000000000)
      constant := (10499452726966486579642036764109398360929779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree088.table
  base := (-70281890696080831431938586048969776527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-13373128962141875669400459377680000000000000)
      constant := (401821205640728689717820083880861792862135496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34818086630806780057/12500000000000000000)
  centralHi := (278544693046454240457/100000000000000000000)
  directionLo := (280140950773865425619/100000000000000000000)
  directionHi := (14007047538693271281/5000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree089.table
  base := (11968053413508758519770317315815714987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-178348352485071063519561642060000000000000)
      constant := (5369339956660957752457393847395842341434883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree089.table
  base := (23936097070891782241848374557907292023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-13522845560518761648810537443730000000000000)
      constant := (410975847045193620752557895068544322664703774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280140950773865425619/100000000000000000000)
  centralHi := (14007047538693271281/5000000000000000000)
  directionLo := (140864082164889685837/50000000000000000000)
  directionHi := (11269126573191174867/4000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree090.table
  base := (167658932345242472987724778861313232509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-20035848588759133034886694880000000000000)
      constant := (610033130129553086240605859578861313232509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree090.table
  base := (6706357136155755913434582020753486537/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-13672562158895647628220615509780000000000000)
      constant := (420233394754787617804098063536525733922475300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140864082164889685837/50000000000000000000)
  centralHi := (11269126573191174867/4000000000000000000)
  directionLo := (283306485723092912457/100000000000000000000)
  directionHi := (141653242861546456229/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree091.table
  base := (16325441607615042478543072470976275371/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-182296922112593331108398865780000000000000)
      constant := (5612601006734716477695494006144775729566780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree091.table
  base := (81627207242039883270009217232797388581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-1063252212097887200586976428910000000000000)
      constant := (33045680673057003495636982778453171856824848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283306485723092912457/100000000000000000000)
  centralHi := (141653242861546456229/50000000000000000000)
  directionLo := (71219015687925180067/25000000000000000000)
  directionHi := (284876062751700720269/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree092.table
  base := (488517724330170081155312371337831123603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-184271206926354464902817477640000000000000)
      constant := (5736248463110633232783492845582040480112427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree092.table
  base := (977035443516105903764270337727113046507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-13971995355649419587040771641880000000000000)
      constant := (439057209010808055334905429980451764209719366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71219015687925180067/25000000000000000000)
  centralHi := (284876062751700720269/100000000000000000000)
  directionLo := (71609259791006081199/25000000000000000000)
  directionHi := (286437039164024324797/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree093.table
  base := (326842790560923458579759364533828552199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-20693943526679510966359565500000000000000)
      constant := (651248948893768334686023913909067657104398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree093.table
  base := (1307371158088694734440482402042747441319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-14121711954026305566450849707930000000000000)
      constant := (448623475519243690170945208381684198635165822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71609259791006081199/25000000000000000000)
  centralHi := (286437039164024324797/100000000000000000000)
  directionLo := (35998694351582626873/12500000000000000000)
  directionHi := (57597910962532202997/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree094.table
  base := (1644024750971105731190786119547625645793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-376439553107753464983309402720000000000000)
      constant := (11975154474582371618879536715555928630812137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree094.table
  base := (1644024747615477994831710758973224985117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-14271428552403191545860927773980000000000000)
      constant := (458292648256782900594985445603507950044969546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35998694351582626873/12500000000000000000)
  centralHi := (57597910962532202997/20000000000000000000)
  directionLo := (18095859112538590477/6250000000000000000)
  directionHi := (289533745800617447633/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree095.table
  base := (993498081065107367709834770926301912279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-190194061367637866286073313220000000000000)
      constant := (6115258554615239999551374338038336717210511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree095.table
  base := (49674903985511481507817974146606026989/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-14421145150780077525271005840030000000000000)
      constant := (468064727205621199815502811728305863484891280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18095859112538590477/6250000000000000000)
  centralHi := (289533745800617447633/100000000000000000000)
  directionLo := (58213948924112145239/20000000000000000000)
  directionHi := (72767436155140181549/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree096.table
  base := (58407133608129116141635636949435996069/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-21352038464599888897832436120000000000000)
      constant := (693809387976088469955889109538988719921380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree096.table
  base := (1168142671068598889221413589870546257801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-14570861749156963504681083906080000000000000)
      constant := (477939712348396730858172356969152489270273476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58213948924112145239/20000000000000000000)
  centralHi := (72767436155140181549/25000000000000000000)
  directionLo := (292597680287490177701/100000000000000000000)
  directionHi := (146298840143745088851/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree097.table
  base := (1345946123712928507636089294434810243149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-194142630995160133874910536940000000000000)
      constant := (6374655048574269056584699862189913292188341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree097.table
  base := (269189224565938605429333948470210538297/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-14720578347533849484091161972130000000000000)
      constant := (487917603668173561789708182106473061619443860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292597680287490177701/100000000000000000000)
  centralHi := (146298840143745088851/50000000000000000000)
  directionLo := (73529419616301455457/25000000000000000000)
  directionHi := (294117678465205821829/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree098.table
  base := (3053816822520638693898233081970966613877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-392233831617842535338658297600000000000000)
      constant := (13012740449527112082639860671977738699524893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree098.table
  base := (3053816821094610268684544083852291691597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-14870294945910735463501240038180000000000000)
      constant := (497998401148426056739227544552917074591759786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73529419616301455457/25000000000000000000)
  centralHi := (294117678465205821829/100000000000000000000)
  directionLo := (59125972317384878587/20000000000000000000)
  directionHi := (36953732698365549117/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree099.table
  base := (106939344433500111709188728822611285051/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-22010133402520266829305306740000000000000)
      constant := (737714446681982045147541159321161780560816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree099.table
  base := (3422059020720920781801694560131629557431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-15020011544287621442911318104230000000000000)
      constant := (508182104773024196728473060019518240790411678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59125972317384878587/20000000000000000000)
  centralHi := (36953732698365549117/12500000000000000000)
  directionLo := (29713434897037056133/10000000000000000000)
  directionHi := (297134348970370561331/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree100.table
  base := (759323759774991922730500381566018552311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-400130970872887070516332745040000000000000)
      constant := (13547668868974787374820976453170470834853995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree100.table
  base := (30372950383567220114878995996743748311/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-15169728142664507422321396170280000000000000)
      constant := (518468714526219745460646426758362423366139750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29713434897037056133/10000000000000000000)
  centralHi := (297134348970370561331/100000000000000000000)
  directionLo := (59726251385529907999/20000000000000000000)
  directionHi := (74657814231912384999/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree101.table
  base := (4177496108017770098503910400812451051543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-404079540500409338105169968760000000000000)
      constant := (13819166935214838138725140034207312059463887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree101.table
  base := (130546753352124549519759575099892359159/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-15319444741041393401731474236330000000000000)
      constant := (528858230392633172315723993974774185756663744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59726251385529907999/20000000000000000000)
  centralHi := (74657814231912384999/25000000000000000000)
  directionLo := (150060349435093704309/50000000000000000000)
  directionHi := (300120698870187408619/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree102.table
  base := (4564690904844825098425228196488837897431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-45336456680881289521556354720000000000000)
      constant := (1565928248732858734998980475716488837897431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree102.table
  base := (57058636302997219872288273302554455953/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-15469161339418279381141552302380000000000000)
      constant := (539350652357241258661547217867276072488969120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150060349435093704309/50000000000000000000)
  centralHi := (300120698870187408619/100000000000000000000)
  directionLo := (301602785409007103223/100000000000000000000)
  directionHi := (37700348176125887903/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree103.table
  base := (1239550786480359295207110339258852112019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-205988339877726936641422208100000000000000)
      constant := (7185115389363273308362368534726659338016342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree103.table
  base := (2479101572716616126302897409835224129301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-15618877937795165360551630368430000000000000)
      constant := (549945980405365324856420353466592361511407476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301602785409007103223/100000000000000000000)
  centralHi := (37700348176125887903/12500000000000000000)
  directionLo := (303077624450590984757/100000000000000000000)
  directionHi := (151538812225295492379/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree104.table
  base := (669754098600048320635563289368933339547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-207962624691488070435840819960000000000000)
      constant := (7324898277612633582950608503057281600223692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree104.table
  base := (334877049275406020413390613258173149341/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-1212968810474773179997054494960000000000000)
      constant := (43126478040204617269463926648315400030125856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303077624450590984757/100000000000000000000)
  centralHi := (151538812225295492379/50000000000000000000)
  directionLo := (76136330322141275627/25000000000000000000)
  directionHi := (304545321288565102509/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree105.table
  base := (5764179791990066278402409632426427613231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-46652646556722045384502095960000000000000)
      constant := (1659116840857607311085016107832426427613231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree105.table
  base := (5764179791672298875278212437980031498299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-15918311134548937319371786500530000000000000)
      constant := (571445354695102660024832084283381000646425062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76136330322141275627/25000000000000000000)
  centralHi := (304545321288565102509/100000000000000000000)
  directionLo := (306005978691425607483/100000000000000000000)
  directionHi := (76501494672856401871/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree106.table
  base := (772080514365512336790278986763506236749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-211911194319010338024678043680000000000000)
      constant := (7608497907920522559839190843923486224522964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree106.table
  base := (1544161028666941320982125811241189318631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16068027732925823298781864566580000000000000)
      constant := (582349400908982979802065284377573087958789112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306005978691425607483/100000000000000000000)
  centralHi := (76501494672856401871/25000000000000000000)
  directionLo := (307459696986514154823/100000000000000000000)
  directionHi := (38432462123314269353/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree107.table
  base := (1319085143586462391431377214578580628069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-427770958265542943638193311080000000000000)
      constant := (15504629299235973578939743374936036128263105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree107.table
  base := (6595425717725553400126501070010487204569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16217744331302709278191942632630000000000000)
      constant := (593356353150893422187206392757557294675144322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307459696986514154823/100000000000000000000)
  centralHi := (38432462123314269353/12500000000000000000)
  directionLo := (308906574140436479591/100000000000000000000)
  directionHi := (38613321767554559949/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree108.table
  base := (438782785138311183632414582354358397019/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-23984418216281400623723918600000000000000)
      constant := (877497334308557535188341132338834867176152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree108.table
  base := (7020524562046221650139698728542385155037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16367460929679595257602020698680000000000000)
      constant := (604466211407719775928333821994947326182402506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308906574140436479591/100000000000000000000)
  centralHi := (38613321767554559949/12500000000000000000)
  directionLo := (310346705836106560539/100000000000000000000)
  directionHi := (15517335291805328027/5000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree109.table
  base := (7451940609806233101640134297441831980591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-435668097520587478815867758520000000000000)
      constant := (16087963970453592484209466655356976487825319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree109.table
  base := (7451940609671749341842710760674113265203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16517177528056481237012098764730000000000000)
      constant := (615678975666632230031509191804301600283638614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310346705836106560539/100000000000000000000)
  centralHi := (15517335291805328027/5000000000000000000)
  directionLo := (311780185546587832223/100000000000000000000)
  directionHi := (9743130798330869757/3125000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree110.table
  base := (788967382356858544168974557950789904841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-219808333574054873202352491120000000000000)
      constant := (8191832578800176365171718701907785545717845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree110.table
  base := (3944836911730069017731246491624460185013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16666894126433367216422176830780000000000000)
      constant := (626994645915076789024089213251713135085068788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311780185546587832223/100000000000000000000)
  centralHi := (9743130798330869757/3125000000000000000)
  directionLo := (39150888075736587967/12500000000000000000)
  directionHi := (313207104605892703737/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree111.table
  base := (4166862083574237422818915465517127724353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-24642513154201778555196789220000000000000)
      constant := (926780865481508462321021438965517127724353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree111.table
  base := (8333724167061030161907031653315010833611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16816610724810253195832254896830000000000000)
      constant := (638413222140767032047720785692064223661760518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39150888075736587967/12500000000000000000)
  centralHi := (313207104605892703737/100000000000000000000)
  directionLo := (2458027752163219799/781250000000000000)
  directionHi := (314627552276892134273/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree112.table
  base := (2196022901240697788261401220772904787431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-223756903201577140791189714840000000000000)
      constant := (8491567616666871633535181539413912286173758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree112.table
  base := (8784091604892287249661802216237821420497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-16966327323187139175242332962880000000000000)
      constant := (649934704331676196299031999825888383640127986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2458027752163219799/781250000000000000)
  centralHi := (314627552276892134273/100000000000000000000)
  directionLo := (316041615816478148727/100000000000000000000)
  directionHi := (39505201977059768591/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree113.table
  base := (9240776102174316036410955373308593381199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-451462376030676549171216653400000000000000)
      constant := (17286904121286590601271849927599777340430791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree113.table
  base := (4620388051058737695417676260227683922187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-17116043921564025154652411028930000000000000)
      constant := (661559092476029567117155544825957664331398412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316041615816478148727/100000000000000000000)
  centralHi := (39505201977059768591/12500000000000000000)
  directionLo := (31744938053811390207/10000000000000000000)
  directionHi := (317449380538113902071/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree114.table
  base := (4851888812335015915918160470915957959669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-25300608092122156486669659840000000000000)
      constant := (977409013456593175855987133030915957959669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree114.table
  base := (9703777624624210100050813542575197180401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-17265760519940911134062489094980000000000000)
      constant := (673286386562297158546034038962365416646975538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31744938053811390207/10000000000000000000)
  centralHi := (317449380538113902071/100000000000000000000)
  directionLo := (249102288962420449/78125000000000000)
  directionHi := (318850929871898174721/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree115.table
  base := (5086548069520126371994152090266630003889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-229679757642860542174445550420000000000000)
      constant := (8951254797914657893660058951512399670035001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree115.table
  base := (10173096139003316629427553452968623551389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-17415477118317797113472567161030000000000000)
      constant := (685116586579186669520883828676697144760369482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249102288962420449/78125000000000000)
  centralHi := (318850929871898174721/100000000000000000000)
  directionLo := (2501924573611437203/781250000000000000)
  directionHi := (64049269084452792397/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree116.table
  base := (1331091451569817070763337683814970541251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-231654042456621675968864162280000000000000)
      constant := (9107173090911984243574028310217338939485036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree116.table
  base := (10648731612528765206119678131676775349663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-17565193716694683092882645227080000000000000)
      constant := (697049692515636701978483001756406750068186094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2501924573611437203/781250000000000000)
  centralHi := (64049269084452792397/20000000000000000000)
  directionLo := (64327141404684814237/20000000000000000000)
  directionHi := (160817853511712035593/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree117.table
  base := (2226136802632467658535778267976245676799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-51917406060085068836285060920000000000000)
      constant := (2058763555546008039982441217059881228383995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree117.table
  base := (445227360525533745690552180827681890759/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 260000000000000000000000000000000000000000
      center := (315)
      previous := (0)
      next := (153)
      square := (8555234192964913109147318060000000000000)
      linear := (-1362685408851659159407132561010000000000000)
      constant := (54545054181600786784564133440606743228993350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64327141404684814237/20000000000000000000)
  centralHi := (160817853511712035593/50000000000000000000)
  directionLo := (161509546396335163123/50000000000000000000)
  directionHi := (323019092792670326247/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree118.table
  base := (11618953309434369841180922624922859045913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-471205224168287887115402772000000000000000)
      constant := (18846087049816871812659145341864305731413217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree118.table
  base := (2323790661883006480169384228120226097073/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-17864626913448455051702801359180000000000000)
      constant := (721224622104088295579925629711098182104053370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161509546396335163123/50000000000000000000)
  centralHi := (323019092792670326247/100000000000000000000)
  directionLo := (324396579181627069483/100000000000000000000)
  directionHi := (81099144795406767371/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree119.table
  base := (60567697352923163029547858872734963613/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-237576896897905077352119997860000000000000)
      constant := (9582995665627628429074125386725461467251700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree119.table
  base := (3028384867642262385412480569989983823601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18014343511825341031112879425230000000000000)
      constant := (733466445735063957824464628975570208129508552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324396579181627069483/100000000000000000000)
  centralHi := (81099144795406767371/25000000000000000000)
  directionLo := (13030729641022164609/4000000000000000000)
  directionHi := (162884120512777057613/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree120.table
  base := (2522888493286618359004486386101573628209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (12)
      previous := (0)
      next := (6)
      square := (329047468960188965736435310000000000000)
      linear := (-53233595935925824699230802160000000000000)
      constant := (2165398315995289687020300620730507868141045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree120.table
  base := (100915539731364280521869150610258091257/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18164060110202227010522957491280000000000000)
      constant := (745811175243536422253140295051283404355608250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13030729641022164609/4000000000000000000)
  centralHi := (162884120512777057613/50000000000000000000)
  directionLo := (32713415159078912293/10000000000000000000)
  directionHi := (327134151590789122931/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree121.table
  base := (13121662267392963495129794623319554203121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-483050933050854689881914443160000000000000)
      constant := (19813867587657641732542002405009875987828089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree121.table
  base := (6560831133691423028769153817787266188999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18313776708579112989933035557330000000000000)
      constant := (758258810619505403561000422925567941943763324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32713415159078912293/10000000000000000000)
  centralHi := (327134151590789122931/100000000000000000000)
  directionLo := (65698876524082898799/20000000000000000000)
  directionHi := (82123595655103623499/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree122.table
  base := (13635198844454587201735387094906457057483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-486999502678376957470751666880000000000000)
      constant := (20141839562094273561685674773934158113517347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree122.table
  base := (13635198844446435743766116588604001537227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18463493306955998969343113623380000000000000)
      constant := (770809351853165674938163357172123152519582726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65698876524082898799/20000000000000000000)
  centralHi := (82123595655103623499/25000000000000000000)
  directionLo := (2576945346704916671/781250000000000000)
  directionHi := (329849004378229333889/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree123.table
  base := (7077526084584929088868984643189560986373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-27274892905883290281088271700000000000000)
      constant := (1137361153722859429332211751823189560986373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree123.table
  base := (7077526084581645556542139284552524411927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18613209905332884948753191689430000000000000)
      constant := (783462798934901807986967614055651256502462652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2576945346704916671/781250000000000000)
  centralHi := (329849004378229333889/100000000000000000000)
  directionLo := (16559904284555136929/5000000000000000000)
  directionHi := (331198085691102738581/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree124.table
  base := (14681222213637195480031513419517059620747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-494896641933421492648426114320000000000000)
      constant := (20805851202158116002936458431655653536586723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree124.table
  base := (14681222213631905196063510486323181733089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18762926503709770928163269755480000000000000)
      constant := (796219151855283093351746095891477235425784082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16559904284555136929/5000000000000000000)
  centralHi := (331198085691102738581/100000000000000000000)
  directionLo := (166270846994890321109/50000000000000000000)
  directionHi := (332541693989780642219/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree125.table
  base := (3803427237621755711437860279211414422933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-249422605780471880118631669020000000000000)
      constant := (10570945433643943100094917132525805459612794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree125.table
  base := (15213708950482761381831307966654861052487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-18912643102086656907573347821530000000000000)
      constant := (809078410605058634418023896201323093035740606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166270846994890321109/50000000000000000000)
  centralHi := (332541693989780642219/100000000000000000000)
  directionLo := (267103916278571747/80000000000000000)
  directionHi := (333879895348214683751/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree126.table
  base := (1969064044108467608911438270863530253493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-27932987843803668212561142320000000000000)
      constant := (1193367764564395329172637934283454121013972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree126.table
  base := (15752512352864308365950939036354425591013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-19062359700463542886983425887580000000000000)
      constant := (822040575175152606844901399578062795849762394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267103916278571747/80000000000000000)
  centralHi := (333879895348214683751/100000000000000000000)
  directionLo := (1309424822349523427/390625000000000000)
  directionHi := (335212754521477997313/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree127.table
  base := (4074408098608042515618899224920264936133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (54)
      previous := (0)
      next := (27)
      square := (1480713610320850345813958895000000000000)
      linear := (-253371175407994147707468892740000000000000)
      constant := (10911018943267340281120909541388564768850394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree127.table
  base := (4074408098607351358737451585876258315457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-19212076298840428866393503953630000000000000)
      constant := (835105645556659677071224868116748451242497864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1309424822349523427/390625000000000000)
  centralHi := (335212754521477997313/100000000000000000000)
  directionLo := (168270167491164744669/50000000000000000000)
  directionHi := (336540334982329489339/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree128.table
  base := (3369813809864889078913949830403591845581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (108)
      previous := (0)
      next := (54)
      square := (2961427220641700691627917790000000000000)
      linear := (-510690920443510563003775009200000000000000)
      constant := (22166145240181877326370237384608161633051145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree128.table
  base := (16849069049322218829196190074726237820619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-19361792897217314845803582019680000000000000)
      constant := (848273621740840573286238780520457468383369222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell184.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168270167491164744669/50000000000000000000)
  centralHi := (336540334982329489339/100000000000000000000)
  directionLo := (337862698956485020497/100000000000000000000)
  directionHi := (168931349478242510249/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2
  qDenominator := 3
  table := BinomialMassData.Q2_3.Degree129.table
  base := (8703411146083672002868839795174841668529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (6)
      previous := (0)
      next := (3)
      square := (164523734480094482868217655000000000000)
      linear := (-28591082781724046144034012940000000000000)
      constant := (1250718990159572845096456176255174841668529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_3.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree129.table
  base := (17406822292165550890922824310520619829779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3380000000000000000000000000000000000000000
      center := (4095)
      previous := (0)
      next := (1989)
      square := (111218044508543870418915134780000000000000)
      linear := (-19511509495594200825213660085730000000000000)
      constant := (861544503719117802681617800908399719502465302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell184.Kernel129
