import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell022.Parameters
import ForestUnimodality.BinomialMassData.Q64_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q64_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q64_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q65_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q65_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q65_153.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree000.table
  base := (60332111011498644265849123/3125000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (2047)
      previous := (1472)
      next := (0)
      square := (40060388374165853409003546240000000000000)
      linear := (140646486010289494678060508100000000000000)
      constant := (14769300775614868116279865310400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree000.table
  base := (60332111011498644265849123/3125000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (2024)
      previous := (1495)
      next := (0)
      square := (40060388374165853409003546240000000000000)
      linear := (140646486010289494678060508100000000000000)
      constant := (14769300775614868116279865310400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree001.table
  base := (123134792274370942628029940887550202913409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (10927455098454042299593869213720000000000000)
      constant := (955534844943791535495039241077074233333330427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree001.table
  base := (30513080328920043698883413693619576872143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (5437020623644243914190932242700000000000000)
      constant := (473508538666521674091309909723127116666663658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24664002959625108003/50000000000000000000)
  directionHi := (49328005919250216007/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree002.table
  base := (80351834104880607296412083945743476867871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (7508968623858556142025566601240000000000000)
      constant := (617843438300761696287184437045916349999997413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree002.table
  base := (39520818176520975553101219549361101499423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (3701070460763723599800778572300000000000000)
      constant := (303761253505420938849706193976664674999997669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24664002959625108003/50000000000000000000)
  centralHi := (49328005919250216007/100000000000000000000)
  directionLo := (17440083743955991781/25000000000000000000)
  directionHi := (558082679806591737/800000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree003.table
  base := (13440078861438421675445712202643066377567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (681747024877178330742877331460000000000000)
      constant := (67987298213954293248048261721029231296103534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree003.table
  base := (13138593329321572754754544865848080726693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (655040099294401095136874967300000000000000)
      constant := (66405864719763115952555164604641715940256986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/25000000000000000000)
  centralHi := (558082679806591737/800000000000000000)
  directionLo := (21359653122049923993/25000000000000000000)
  directionHi := (85438612488199695973/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree004.table
  base := (576225417447854966040513503763062016641/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (335997837333791913444480688140000000000000)
      constant := (137599168868694265586208448561381533307191136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree004.table
  base := (35874098586402881789025400239669632538051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (458340270005365942040942463000000000000000)
      constant := (267346789703707331881488042138142142694411953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/25000000000000000000)
  centralHi := (85438612488199695973/100000000000000000000)
  directionLo := (98656011838500432013/100000000000000000000)
  directionHi := (49328005919250216007/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree005.table
  base := (3233085395462615763482814713800286240189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-1373245399963951165339670618100000000000000)
      constant := (94845989063507724712318250447134534128779068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree005.table
  base := (12531549101868573225326062998036346290791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-1506780027877837343369682438900000000000000)
      constant := (91765664581226061067762713596177610107042173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98656011838500432013/100000000000000000000)
  centralHi := (49328005919250216007/50000000000000000000)
  directionLo := (55150387214977742483/50000000000000000000)
  directionHi := (110300774429955484967/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree006.table
  base := (9223063291488935335596101430865632123107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-1027496212420564748041273974780000000000000)
      constant := (22278136264608234017001375538801509152201307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree006.table
  base := (17815719094515487228923012361311706309061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-2161820127172238438506557406200000000000000)
      constant := (42999265250784894346436843553771748109867661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55150387214977742483/50000000000000000000)
  centralHi := (110300774429955484967/100000000000000000000)
  directionLo := (120828444531151298303/100000000000000000000)
  directionHi := (471986111449809759/390625000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree007.table
  base := (6632774347635318274060599761882511512731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-4791731874559437322907973230580000000000000)
      constant := (48269279958256994852816577321809237333839993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree007.table
  base := (1276917283597109616384131529207315018499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-4978680353638877972149989779700000000000000)
      constant := (46556175705282806040494379387523395446738485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120828444531151298303/100000000000000000000)
  centralHi := (471986111449809759/390625000000000000)
  directionLo := (130509636333058144167/100000000000000000000)
  directionHi := (16313704541632268021/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree008.table
  base := (1901367240655263095189856749607635756599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-13001950223714360803384249073640000000000000)
      constant := (71933073054754613061661357656821909043709985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree008.table
  base := (911183980969745926261466049979215095767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-6714630516519398286540143450100000000000000)
      constant := (34770964127329440287400607479939076961349505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130509636333058144167/100000000000000000000)
  centralHi := (16313704541632268021/12500000000000000000)
  directionLo := (17440083743955991781/12500000000000000000)
  directionHi := (139520669951647934249/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree009.table
  base := (6674464176760123070869950688702495118563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-5473478899436615653650850562040000000000000)
      constant := (18661925323916417207750234986755189803382363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree009.table
  base := (6355257198483446351186005505519066795283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-5633720452933279067286864747000000000000000)
      constant := (18158350307312013257526932250855092734531083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/12500000000000000000)
  centralHi := (139520669951647934249/100000000000000000000)
  directionLo := (7399200887887532401/5000000000000000000)
  directionHi := (147984017757750648021/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree010.table
  base := (4463660265996542947867338018528115644947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-19838923172905333118520854298600000000000000)
      constant := (46318530022589701038122422814574886377521441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree010.table
  base := (840262696974877577625594224611683538731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-20373061684560877830640901581800000000000000)
      constant := (45585555241698303242569664363224833263589965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7399200887887532401/5000000000000000000)
  centralHi := (147984017757750648021/100000000000000000000)
  directionLo := (77994425569549269357/50000000000000000000)
  directionHi := (31197770227819707743/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree011.table
  base := (1341916818718375215151339678933301577831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-11628704823750409638044578455540000000000000)
      constant := (20722077466547241177232108579676552211815293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree011.table
  base := (1232378994758415001243776128490296948641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-11922481005160959229710604461300000000000000)
      constant := (20713965081475335214860759516109787090245723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77994425569549269357/50000000000000000000)
  centralHi := (31197770227819707743/20000000000000000000)
  directionLo := (81801243645291585241/50000000000000000000)
  directionHi := (163602487290583170483/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree012.table
  base := (606651914514044047899863195692659859419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-4445982687016050905609576587260000000000000)
      constant := (6735529676311118284245703731676608294348819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree012.table
  base := (1027861354838806833813036497012527852689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-9105620778694319696067172087800000000000000)
      constant := (13694511169519697241643882940729584944844089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81801243645291585241/50000000000000000000)
  centralHi := (163602487290583170483/100000000000000000000)
  directionLo := (21359653122049923993/12500000000000000000)
  directionHi := (34175444995279878389/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree013.table
  base := (-13780468008118242994670158269329748929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-15047191298345895795612881068020000000000000)
      constant := (21302116321319520878574201725264419969107013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree013.table
  base := (-5819301261572536317237071674801594923/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-15394381330921999858490911802100000000000000)
      constant := (21976386614708473382185203318044370477053296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/12500000000000000000)
  centralHi := (34175444995279878389/20000000000000000000)
  directionLo := (35570930931649565993/20000000000000000000)
  directionHi := (88927327329123914983/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree014.table
  base := (-136545261148132342640367834641542494741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-16756434535643638874397032374260000000000000)
      constant := (23799533358752047839976447083728175654143908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree014.table
  base := (-1229163935536319391459274026285838935097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-34260662987605040345762130945000000000000000)
      constant := (49632351743184988084606561890891598789438109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35570930931649565993/20000000000000000000)
  centralHi := (88927327329123914983/50000000000000000000)
  directionLo := (184568497722591275553/100000000000000000000)
  directionHi := (92284248861295637777/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree015.table
  base := (-2018288857705451664228761228607911886879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-12310451848627587968787455787000000000000000)
      constant := (18369164247469673632269301100390821182227721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree015.table
  base := (-133554395069397213480590244034753844273/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-6288760552227680162423739714300000000000000)
      constant := (9640366267662125867105987024624842008367416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184568497722591275553/100000000000000000000)
  centralHi := (92284248861295637777/50000000000000000000)
  directionLo := (191046545426876968741/100000000000000000000)
  directionHi := (95523272713438484371/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree016.table
  base := (-353993440724478302912248656492825079883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-20174921010239125031965334986740000000000000)
      constant := (32460950940798777531939074840105943606691804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree016.table
  base := (-587013930098541121932979653029836917201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-41204463639127121603322745626600000000000000)
      constant := (68381517362697891565716160773040912675402985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191046545426876968741/100000000000000000000)
  centralHi := (95523272713438484371/50000000000000000000)
  directionLo := (197312023677000864027/100000000000000000000)
  directionHi := (49328005919250216007/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree017.table
  base := (-177646918817897258700813005959702215383/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6141)
      previous := (4416)
      next := (0)
      square := (120181165122497560227010638720000000000000)
      linear := (-1287303779266874594749969781940000000000000)
      constant := (2261451562576095531774959885364966831392030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree017.table
  base := (-728553927789802760002718452502668870809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (12144)
      previous := (8970)
      next := (0)
      square := (240362330244995120454021277440000000000000)
      linear := (-2628021409699303660711944292200000000000000)
      constant := (4770705518302504611451137864506374941493345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197312023677000864027/100000000000000000000)
  centralHi := (49328005919250216007/25000000000000000000)
  directionLo := (101692289353080912329/50000000000000000000)
  directionHi := (203384578706161824659/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree018.table
  base := (-1049021504607263739015128260157026053707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-7864469161611537063177879199740000000000000)
      constant := (15149028342676743549270034318343150468616186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree018.table
  base := (-534298169198001220993097129902330166367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-8024710715108200476813893384700000000000000)
      constant := (15981857697114768201119947375496156949117732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101692289353080912329/50000000000000000000)
  centralHi := (203384578706161824659/100000000000000000000)
  directionLo := (52320251231867975343/25000000000000000000)
  directionHi := (209281004927471901373/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree019.table
  base := (-4772858261032512828044426355368277931749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-50605301444264708536635577810920000000000000)
      constant := (106846869353207939581330327022981327298562553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree019.table
  base := (-2420546488847175672071679139420025614541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-25810082308205121744831833824500000000000000)
      constant := (56330883359536081474516431696605540129736577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52320251231867975343/25000000000000000000)
  centralHi := (209281004927471901373/100000000000000000000)
  directionLo := (21501579288838785809/10000000000000000000)
  directionHi := (215015792888387858091/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree020.table
  base := (-211691633335522998149475263935344146457/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-54023787918860194694203880423400000000000000)
      constant := (124676945223927925591590416823812740629900725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree020.table
  base := (-5351712319694776688170426296791316842027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-55092064942171284118443974989800000000000000)
      constant := (131345034455233037762553693386137354681663319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21501579288838785809/10000000000000000000)
  centralHi := (215015792888387858091/100000000000000000000)
  directionLo := (55150387214977742483/25000000000000000000)
  directionHi := (220601548859910969933/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree021.table
  base := (-288080349003800758086363824309629071671/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-9573712398909280141962030505980000000000000)
      constant := (24054672448460090440319567488426547845837290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree021.table
  base := (-5813299619580910223892274577650548220869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-19521321755977441582408094110200000000000000)
      constant := (50628629850161792089284495390530924077519731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55150387214977742483/25000000000000000000)
  centralHi := (220601548859910969933/100000000000000000000)
  directionLo := (2825616512577423101/1250000000000000000)
  directionHi := (226049321006193848081/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree022.table
  base := (-1546661321266815532479065409939412503829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-30430380434025583504670242824180000000000000)
      constant := (82877289641490317129326257273925528465244626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree022.table
  base := (-311577933521890916887577036277460716703/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-31017932796846682688002294835700000000000000)
      constant := (87119912653693202725760170262269740275664910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2825616512577423101/1250000000000000000)
  centralHi := (226049321006193848081/100000000000000000000)
  directionLo := (57842214091078658141/25000000000000000000)
  directionHi := (46273771272862926513/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree023.table
  base := (-6572164307447951188244119790118892835451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-64279247342646653166908788260840000000000000)
      constant := (188919447964039086462271719525382279204975847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree023.table
  base := (-165278379663826655491458092570298341957/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-32753882959727203002392448506100000000000000)
      constant := (99185295608675127068342877120979240754190580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57842214091078658141/25000000000000000000)
  centralHi := (46273771272862926513/20000000000000000000)
  directionLo := (236568805769696609849/100000000000000000000)
  directionHi := (4731376115393932197/2000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree024.table
  base := (-6922066019168346243331164014648967376657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-22565911272414046441492363624440000000000000)
      constant := (71264064548935996663138905640138035853315143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree024.table
  base := (-54342453030698769535797485582568943367/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-11496611040869241105594200725500000000000000)
      constant := (37374749711649193772649178787983243411355712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236568805769696609849/100000000000000000000)
  centralHi := (4731376115393932197/2000000000000000000)
  directionLo := (241656889062302596607/100000000000000000000)
  directionHi := (471986111449809759/195312500000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree025.table
  base := (-1447912830697420150472377009436589357349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-71116220291837625482045393485800000000000000)
      constant := (240347739570670071913676925536831466223028765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree025.table
  base := (-3634391773073322018503820311809996974351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-36225783285488243631172755846900000000000000)
      constant := (125924567500642378188998558219446593609139147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241656889062302596607/100000000000000000000)
  centralHi := (471986111449809759/195312500000000000)
  directionLo := (123320014798125540017/50000000000000000000)
  directionHi := (49328005919250216007/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree026.table
  base := (-940914252076802876149105183929320042483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-37267353383216555819806848049140000000000000)
      constant := (134282683190633538459044809372958062834020604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree026.table
  base := (-1888140864208767508365122391951516765499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-37961733448368763945562909517300000000000000)
      constant := (140576186413407515185039788484204629357622606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123320014798125540017/50000000000000000000)
  centralHi := (49328005919250216007/20000000000000000000)
  directionLo := (251524464748877247353/100000000000000000000)
  directionHi := (125762232374438623677/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree027.table
  base := (-1557502901343679837096711671973080926487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-25984397747009532599060666236920000000000000)
      constant := (99475972025397809535065174135750082551036565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree027.table
  base := (-1561860994668142944373419837898420222773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-26465122407499522839968708791800000000000000)
      constant := (104047193858875730540140058705131045002837135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251524464748877247353/100000000000000000000)
  centralHi := (125762232374438623677/50000000000000000000)
  directionLo := (64078959366149771979/25000000000000000000)
  directionHi := (256315837464599087917/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree028.table
  base := (-8021989506790697742261752085369205288729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-81371679715624083954750301323240000000000000)
      constant := (329921156896465137973595365663144091132047613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree028.table
  base := (-4020385700170264550948410523329927652463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-41433633774129804574343216858100000000000000)
      constant := (172401501092163495739299481836456574527831211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64078959366149771979/25000000000000000000)
  centralHi := (256315837464599087917/100000000000000000000)
  directionLo := (52203854533223257667/20000000000000000000)
  directionHi := (16313704541632268021/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree029.table
  base := (-4116126788103041931312322303581753077447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-42395083095109785056159301967860000000000000)
      constant := (181516635367640456149790762782911580736681059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree029.table
  base := (-1031052882020571336151197472138502971357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-43169583937010324888733370528500000000000000)
      constant := (189562619892992495574960773846113045258005316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52203854533223257667/20000000000000000000)
  centralHi := (16313704541632268021/6250000000000000000)
  directionLo := (265639441482468762717/100000000000000000000)
  directionHi := (132819720741234381359/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree030.table
  base := (-8419565431156038113997885651916890765733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-29402884221605018756628968849400000000000000)
      constant := (132584811943399542905177219099364167118328467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree030.table
  base := (-527091885690016609426415912405397875371/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-14968511366630281734374508066300000000000000)
      constant := (69183141825856097245475349739668481009280232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265639441482468762717/100000000000000000000)
  centralHi := (132819720741234381359/50000000000000000000)
  directionLo := (270180615587217008689/100000000000000000000)
  directionHi := (27018061558721700869/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree031.table
  base := (-8584971762527794080666388613472551976391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-91627139139410542427455209160680000000000000)
      constant := (434076484852225203563270581647793676928221027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree031.table
  base := (-8596916202725910324337019432570550671227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-93282968525542731035027355738600000000000000)
      constant := (452716005710893784465990216398651993112415719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270180615587217008689/100000000000000000000)
  centralHi := (27018061558721700869/10000000000000000000)
  directionLo := (274646713446669728731/100000000000000000000)
  directionHi := (68661678361667432183/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree032.table
  base := (-8729343303926049015877029379057971384439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-95045625614006028585023511773160000000000000)
      constant := (471992623467043184175712926066890649287222483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree032.table
  base := (-8739593447729319916525357302624227078229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-96754868851303771663807663079400000000000000)
      constant := (491970209643606109729988655943623156108579113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274646713446669728731/100000000000000000000)
  centralHi := (68661678361667432183/25000000000000000000)
  directionLo := (17440083743955991781/6250000000000000000)
  directionHi := (279041339903295868497/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree033.table
  base := (-8853404619845383060707235271916001172139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-32821370696200504914197271461880000000000000)
      constant := (170499065965967120570677175050706480951266461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree033.table
  base := (-8862192401981818405855704082379893179533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-33408923059021604097529323473400000000000000)
      constant := (177618691604507146347053777716729897840034667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/6250000000000000000)
  centralHi := (279041339903295868497/100000000000000000000)
  directionLo := (141683910115965782059/50000000000000000000)
  directionHi := (283367820231931564119/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree034.table
  base := (-4478879383106500812354319651811777913171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6141)
      previous := (4416)
      next := (0)
      square := (120181165122497560227010638720000000000000)
      linear := (-2996547016564617673534121088180000000000000)
      constant := (16252514779394110363573381956298393937854511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree034.table
  base := (-4482643008442025678736515254344676672329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6072)
      previous := (4485)
      next := (0)
      square := (120181165122497560227010638720000000000000)
      linear := (-3049960867730172144746125816500000000000000)
      constant := (16922621484731192207490648275255793407400989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141683910115965782059/50000000000000000000)
  centralHi := (283367820231931564119/100000000000000000000)
  directionLo := (71907307395948061179/25000000000000000000)
  directionHi := (287629229583792244717/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree035.table
  base := (-9042907740673294428910853772426446443253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-105301085037792487057728419610600000000000000)
      constant := (595253620183919183130909245389756438403296841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree035.table
  base := (-9049349766652836390506758696489703445329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-107170569828586893550148585101800000000000000)
      constant := (619505666520309569888483899806290844016097813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71907307395948061179/25000000000000000000)
  centralHi := (287629229583792244717/100000000000000000000)
  directionLo := (145914209279747197087/50000000000000000000)
  directionHi := (11673136742379775767/4000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree036.table
  base := (-9109269461864681763368984002960460063797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-36239857170795991071765574074360000000000000)
      constant := (213166096644108020165658104976939843374064003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree036.table
  base := (-9114778266838174612014235063394592435681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-36880823384782644726309630814200000000000000)
      constant := (221754201248910628301399478132110665074793719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145914209279747197087/50000000000000000000)
  centralHi := (11673136742379775767/4000000000000000000)
  directionLo := (295968035515501296041/100000000000000000000)
  directionHi := (147984017757750648021/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree037.table
  base := (-4578595939414655848658230121470999898247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-56069028993491729686432512417780000000000000)
      constant := (342658398349119251537730869457201787793978659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree037.table
  base := (-286309345197923721696603976092651779453/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-57057185240054487403854599891700000000000000)
      constant := (356318693226085776829350495023284610638851856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295968035515501296041/100000000000000000000)
  centralHi := (147984017757750648021/50000000000000000000)
  directionLo := (60010109219988800441/20000000000000000000)
  directionHi := (150025273049972001103/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree038.table
  base := (-4593482351335963414552028887619480805529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-57778272230789472765216663724020000000000000)
      constant := (366353439932956102185720208904145191274457213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree038.table
  base := (-9190983966007128048079009756394105079253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-117586270805870015436489507124200000000000000)
      constant := (761627893306274493693579742380856798066588841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60010109219988800441/20000000000000000000)
  centralHi := (150025273049972001103/50000000000000000000)
  directionLo := (38009781303395323621/12500000000000000000)
  directionHi := (304078250427162588969/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree039.table
  base := (-2299707291325373083209512540023901506531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-19829171822695738614666938343420000000000000)
      constant := (130277776183793251521893183170315664363025738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree039.table
  base := (-9202258689322783105502515804424806342409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-40352723710543685355089938155000000000000000)
      constant := (270744121152343960191120498973691078703394191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38009781303395323621/12500000000000000000)
  centralHi := (304078250427162588969/100000000000000000000)
  directionLo := (3850666227883774221/1250000000000000000)
  directionHi := (308053298230701937681/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree040.table
  base := (-574561633716214652206880866694932011949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-61196758705384958922784966336500000000000000)
      constant := (416097280499389534253781243561435564086095624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree040.table
  base := (-9195910539142873005399247236105655283289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-124530071457392096694050121805800000000000000)
      constant := (864449335224148807088898006976667571824495933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3850666227883774221/1250000000000000000)
  centralHi := (308053298230701937681/100000000000000000000)
  directionLo := (77994425569549269357/25000000000000000000)
  directionHi := (311977702278197077429/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree041.table
  base := (-4584801448312880763706474889016686013603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-62906001942682702001569117642740000000000000)
      constant := (442144643167306188512957184475562799035855791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree041.table
  base := (-1146511877098410904432431110808642325489/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-64000985891576568661415214573300000000000000)
      constant := (459138797615413087783871146049940655736837332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77994425569549269357/25000000000000000000)
  centralHi := (311977702278197077429/100000000000000000000)
  directionLo := (6317067005715641711/2000000000000000000)
  directionHi := (315853350285782085551/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree042.table
  base := (-1141102341515446049659699176135393043063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-21538415059993481693451089649660000000000000)
      constant := (156324957698142221009104790425567370779972548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree042.table
  base := (-9130941211741679370492349282648638439189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-43824624036304725983870245495800000000000000)
      constant := (324572045397269143721885980697830891419669411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6317067005715641711/2000000000000000000)
  centralHi := (315853350285782085551/100000000000000000000)
  directionLo := (39960251941523588551/12500000000000000000)
  directionHi := (319682015532188708409/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree043.table
  base := (-9070749647791917750696346072652974436177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-132648976834556376318274840510440000000000000)
      constant := (993175035399151709300408124729168840474510869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree043.table
  base := (-9072556291151459683521482100305169960751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-134945772434675218580391043828200000000000000)
      constant := (1030764121881856937522242323686318758796259947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39960251941523588551/12500000000000000000)
  centralHi := (319682015532188708409/100000000000000000000)
  directionLo := (64693073268377697921/20000000000000000000)
  directionHi := (161732683170944244803/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree044.table
  base := (-8995492250404276349938904712785403101549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-136067463309151862475843143122920000000000000)
      constant := (1049964400142854165617262070224055499598613153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree044.table
  base := (-8997029225840061815677658610203301451479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-138417672760436259209171351169000000000000000)
      constant := (1089420858061639441935751716532583638774109363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64693073268377697921/20000000000000000000)
  centralHi := (161732683170944244803/50000000000000000000)
  directionLo := (81801243645291585241/25000000000000000000)
  directionHi := (65440994916233268193/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree045.table
  base := (-8903126997344107018059192816143688101233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-46495316594582449544470481911800000000000000)
      constant := (369439070870332511532300271357210267248692967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree045.table
  base := (-445221694140278709619864436258609553341/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-23648262181032883306325276418300000000000000)
      constant := (191614294724494810070417635680413565517600590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81801243645291585241/25000000000000000000)
  centralHi := (65440994916233268193/20000000000000000000)
  directionLo := (165451161644933227449/50000000000000000000)
  directionHi := (330902323289866454899/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree046.table
  base := (-351748835957107489781938834666430821571/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-142904436258342834790979748347880000000000000)
      constant := (1168232949922083902988824050715766007482037175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree046.table
  base := (-8794831591979568505916307469880635566029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-145361473411958340466731965850600000000000000)
      constant := (1211558374180389139067987615338521400678275713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165451161644933227449/50000000000000000000)
  centralHi := (330902323289866454899/100000000000000000000)
  directionLo := (41819851694238930551/12500000000000000000)
  directionHi := (334558813553911444409/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree047.table
  base := (-8667329768392271750964037502221660428023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-146322922732938320948548050960360000000000000)
      constant := (1229711176565422972200720178885044383680136531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree047.table
  base := (-1083534159583172084958921045982032049079/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-74416686868859690547756136595700000000000000)
      constant := (637519139103682189436810456428308815684146252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41819851694238930551/12500000000000000000)
  centralHi := (334558813553911444409/100000000000000000000)
  directionLo := (338175770708917678887/100000000000000000000)
  directionHi := (42271971338614709861/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree048.table
  base := (-4262000047648988224368940709827884645753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-24956901534588967851019392262140000000000000)
      constant := (215458588297162859629280898463017672036396447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree048.table
  base := (-8524801221848538171302334386815559461803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-50768424687826807241430860177400000000000000)
      constant := (446708383492717471817147285299892729839850397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338175770708917678887/100000000000000000000)
  centralHi := (42271971338614709861/12500000000000000000)
  directionLo := (21359653122049923993/6250000000000000000)
  directionHi := (341754449952798783889/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree049.table
  base := (-522735662837092649884619285548428649709/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-76579947841064646631842328092660000000000000)
      constant := (678676853698864750700162184134284889970565384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree049.table
  base := (-8364450541946902833108811328266462690221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-155777174389241462353072887873000000000000000)
      constant := (1406818716994950766403956620398536791628205537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/6250000000000000000)
  centralHi := (341754449952798783889/100000000000000000000)
  directionLo := (21581002589671969503/6250000000000000000)
  directionHi := (345296041434751512049/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree050.table
  base := (-4093336779715873294375313083634432191591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-78289191078362389710626479398900000000000000)
      constant := (711758728839512339842634069768400525609015427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree050.table
  base := (-4093625199547563385996906751826009125903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-79624537357501251490926597606900000000000000)
      constant := (737559375102811355064500492840501650790578891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21581002589671969503/6250000000000000000)
  centralHi := (345296041434751512049/100000000000000000000)
  directionLo := (17440083743955991781/5000000000000000000)
  directionHi := (348801674879119835621/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree051.table
  base := (-7992735834631240698941519601480729525073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4094)
      previous := (2944)
      next := (0)
      square := (80120776748331706818007092480000000000000)
      linear := (-3137193502574907168212181596280000000000000)
      constant := (29240050409880920747526593688493448382663831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree051.table
  base := (-7993225014369314113256046209717249403581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4048)
      previous := (2990)
      next := (0)
      square := (80120776748331706818007092480000000000000)
      linear := (-3190607353740461639424186324600000000000000)
      constant := (30294609041433556983075865770913260841252107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17440083743955991781/5000000000000000000)
  centralHi := (348801674879119835621/100000000000000000000)
  directionLo := (352272423795063472951/100000000000000000000)
  directionHi := (44034052974382934119/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree052.table
  base := (-3890989912580890633688323831502376510781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-81707677552957875868194782011380000000000000)
      constant := (780264436165364629132501187623426956086375857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree052.table
  base := (-3891197253573756396239443911734282334937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-83096437683262292119706904947700000000000000)
      constant := (808268746362954973193102012414737394940486589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352272423795063472951/100000000000000000000)
  centralHi := (44034052974382934119/12500000000000000000)
  directionLo := (35570930931649565993/10000000000000000000)
  directionHi := (355709309316495659931/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree053.table
  base := (-3777212095971866126655251615106562249477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-83416920790255618946978933317620000000000000)
      constant := (815688108174134990067321811503963494767330969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree053.table
  base := (-151095511836367237798368584955974166527/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-84832387846142812434097058618100000000000000)
      constant := (844827957310821890066883659952213339464745475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35570930931649565993/10000000000000000000)
  centralHi := (355709309316495659931/100000000000000000000)
  directionLo := (179556651855610719977/50000000000000000000)
  directionHi := (71822660742244287991/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree054.table
  base := (-7310084486979289109127630389211782359969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-56750776018368908017175389749240000000000000)
      constant := (567928160534758664205941141297500154081720631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree054.table
  base := (-3655191078042197902288538477205547549807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-28856112669674444249495737429500000000000000)
      constant := (294063369739095005244023876973788370822951993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179556651855610719977/50000000000000000000)
  centralHi := (71822660742244287991/20000000000000000000)
  directionLo := (362485333593453894911/100000000000000000000)
  directionHi := (1415958334349429277/390625000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree055.table
  base := (-7048973673213520954395697815785844845703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-173670814529702210209094471860200000000000000)
      constant := (1777753566948886921374555259223423052668979491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree055.table
  base := (-3524612870492539509314675864001002814793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-88304288171903853062877365958900000000000000)
      constant := (920355157054978879511462032480700175036170221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362485333593453894911/100000000000000000000)
  centralHi := (1415958334349429277/390625000000000000)
  directionLo := (2926610262958314869/800000000000000000)
  directionHi := (182913141434894679313/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree056.table
  base := (-6771102557408516892595542712027488916839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-177089301004297696366662774472680000000000000)
      constant := (1853283388056938185130378156312769503981905283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree056.table
  base := (-6771315939343896912575793414567693260217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-180080476669568746754535039258600000000000000)
      constant := (1918646126795005306386064016842128289490526749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2926610262958314869/800000000000000000)
  centralHi := (182913141434894679313/50000000000000000000)
  directionLo := (369136995445182551107/100000000000000000000)
  directionHi := (92284248861295637777/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree057.table
  base := (-40478000941174659720372416711338230197/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-30084631246482197087371846180860000000000000)
      constant := (321728979102568682925574104907984741060608240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree057.table
  base := (-3238330363252290420377628249066704552469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-30592062832554964563885891099900000000000000)
      constant := (333031265709684256299276172657677501459028131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369136995445182551107/100000000000000000000)
  centralHi := (92284248861295637777/25000000000000000000)
  directionLo := (186209138856197326429/50000000000000000000)
  directionHi := (372418277712394652859/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree058.table
  base := (-6165113968173063342667235174614299179981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-183926273953488668681799379697640000000000000)
      constant := (2009024967981476594952374477719364623498608257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree058.table
  base := (-3082633367432458104954293415770002276599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-93512138660545414006047826970100000000000000)
      constant := (1039667332373329266861452151041746672235698003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186209138856197326429/50000000000000000000)
  centralHi := (372418277712394652859/100000000000000000000)
  directionLo := (375670900845721469859/100000000000000000000)
  directionHi := (18783545042286073493/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree059.table
  base := (-5837010279902691006292683961112957682493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-187344760428084154839367682310120000000000000)
      constant := (2089236619232359659003414551715755591203507121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree059.table
  base := (-5837139481760517453250994319836899591079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-190496177646851868640875961281000000000000000)
      constant := (2162087295208894494745427532365312672490810563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375670900845721469859/100000000000000000000)
  centralHi := (18783545042286073493/5000000000000000000)
  directionLo := (189447801458743165673/50000000000000000000)
  directionHi := (378895602917486331347/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree060.table
  base := (-343260894871291151840211000915915383457/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-31793874483779940166155997487100000000000000)
      constant := (361834797923581154187852812308941632701026744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree060.table
  base := (-2746141779313679662042037961264415710759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-32328012995435484878276044770300000000000000)
      constant := (374407574969639751643869060952751254736315841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189447801458743165673/50000000000000000000)
  centralHi := (378895602917486331347/100000000000000000000)
  directionLo := (382093090853753937483/100000000000000000000)
  directionHi := (95523272713438484371/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree061.table
  base := (-5130610450167866811877936863095685092807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-194181733377275127154504287535080000000000000)
      constant := (2254341438826283721261764889139184369220826979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree061.table
  base := (-1282675697006054009945386209631065369647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-98719989149186974949218287981300000000000000)
      constant := (1166204549373032231929048859022997593841288918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382093090853753937483/100000000000000000000)
  centralHi := (95523272713438484371/25000000000000000000)
  directionLo := (385264042243945529131/100000000000000000000)
  directionHi := (96316010560986382283/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree062.table
  base := (-950464464897025040589528182240805904649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-197600219851870613312072590147560000000000000)
      constant := (2339234544622180034395270603391954957630119265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree062.table
  base := (-4752400353977573525465200475086038998757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-200911878624134990527216883303400000000000000)
      constant := (2419978217148613687056352188578903637692699129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385264042243945529131/100000000000000000000)
  centralHi := (96316010560986382283/25000000000000000000)
  directionLo := (388409107017477423063/100000000000000000000)
  directionHi := (48551138377184677883/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree063.table
  base := (-871462597795578890169976725735540870061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-67006235442155366489880297586680000000000000)
      constant := (808562693714988337843049913253969290984856695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree063.table
  base := (-4357378910183114238589825754645975701791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-68127926316632010385332396881400000000000000)
      constant := (836384261439566256414152702057165817199641609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388409107017477423063/100000000000000000000)
  centralHi := (48551138377184677883/12500000000000000000)
  directionLo := (391528908999174432503/100000000000000000000)
  directionHi := (48941113624896804063/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree064.table
  base := (-3945584991982219738809346525916536312373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-204437192801061585627209195372520000000000000)
      constant := (2513702028509972498098700108423393267154553481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree064.table
  base := (-3156512535861772261685408775409013157/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-103927839637828535892388748992500000000000000)
      constant := (1299966391493413204765475581262427168959955625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391528908999174432503/100000000000000000000)
  centralHi := (48941113624896804063/12500000000000000000)
  directionLo := (78924809470800345611/20000000000000000000)
  directionHi := (49328005919250216007/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree065.table
  base := (-439642558176893230117187436354407530467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-103927839637828535892388748992500000000000000)
      constant := (1301638185040926893865764954920506232159063996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree065.table
  base := (-1758593740076114039935009673490888588071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-105663789800709056206778902662900000000000000)
      constant := (1346159099369482270407451746210250596347281987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78924809470800345611/20000000000000000000)
  centralHi := (49328005919250216007/12500000000000000000)
  directionLo := (397695097930591775371/100000000000000000000)
  directionHi := (99423774482647943843/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree066.table
  base := (-767995298542512528306043905697076947663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-35212360958375426323724300099580000000000000)
      constant := (449068515322180976486475079390083805718257074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree066.table
  base := (-1536010442179178644436836855766744542479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-35799913321196525507056352111100000000000000)
      constant := (464384836588920327517064224269150697445012121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397695097930591775371/100000000000000000000)
  centralHi := (99423774482647943843/25000000000000000000)
  directionLo := (8014852290241974683/2000000000000000000)
  directionHi := (400742614512098734151/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree067.table
  base := (-2610108673908665226379798341660216943553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-214692652224848044099914103209960000000000000)
      constant := (2787106182393020211631108373976505327189455941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree067.table
  base := (-2610142172994254502269673437326154395167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-218271380252940193671118420007400000000000000)
      constant := (2881905235300347554363167061139544017254511899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8014852290241974683/2000000000000000000)
  centralHi := (400742614512098734151/100000000000000000000)
  directionLo := (100941782495518843779/25000000000000000000)
  directionHi := (403767129982075375117/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree068.table
  base := (-2131524159191333161617701951340644071001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (12282)
      previous := (8832)
      next := (0)
      square := (240362330244995120454021277440000000000000)
      linear := (-12830066982320207662204847401320000000000000)
      constant := (169491860686607205728758585598574644371410541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree068.table
  base := (-2131552426622641046071428353836470359771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (12144)
      previous := (8970)
      next := (0)
      square := (240362330244995120454021277440000000000000)
      linear := (-13043722386982425547052866314600000000000000)
      constant := (175241578682812376122962706005589060104865111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100941782495518843779/25000000000000000000)
  centralHi := (403767129982075375117/100000000000000000000)
  directionLo := (101692289353080912329/25000000000000000000)
  directionHi := (406769157412323649317/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree069.table
  base := (-1636228703562108422304008688279726771123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-73843208391346338805016902811640000000000000)
      constant := (992392477183396152967482456042424430668309077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree069.table
  base := (-327250510248730757287081499170118592469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-75071726968154091642893011563000000000000000)
      constant := (1025971273128797138772454413534292607704940655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101692289353080912329/25000000000000000000)
  centralHi := (406769157412323649317/100000000000000000000)
  directionLo := (204874595539503945597/50000000000000000000)
  directionHi := (81949838215801578239/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree070.table
  base := (-140527899116847832771751496498292279051/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-112474055824317251286309505523700000000000000)
      constant := (1537276787556916389948833059139295301386260188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree070.table
  base := (-1124243307706591318217443148751831385043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-228687081230223315557459342029800000000000000)
      constant := (3178326174699183544108498717340289459702509471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204874595539503945597/50000000000000000000)
  centralHi := (81949838215801578239/20000000000000000000)
  directionLo := (51588463426591151771/12500000000000000000)
  directionHi := (412707707412729214169/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree071.table
  base := (-297754186700317409071460069842817259871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-114183299061614994365093656829940000000000000)
      constant := (1586745028270752605414901417487176496921226587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree071.table
  base := (-59552533613155905386285906902693237887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-116079490777992178093119824685300000000000000)
      constant := (1640171949275664797465230785517691423323838695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51588463426591151771/12500000000000000000)
  centralHi := (412707707412729214169/100000000000000000000)
  directionLo := (51955645735966535439/12500000000000000000)
  directionHi := (415645165887732283513/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree072.table
  base := (-25042437195571526579243973894621073303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-38630847432970912481292602712060000000000000)
      constant := (545664478486958654598896031308380090588338897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree072.table
  base := (-10019835237777559305601571042311824261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-78543627293915132271673318903800000000000000)
      constant := (1127988995577260659175407594120594734725485695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51955645735966535439/12500000000000000000)
  centralHi := (415645165887732283513/100000000000000000000)
  directionLo := (52320251231867975343/12500000000000000000)
  directionHi := (83712401970988760549/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree073.table
  base := (64005846503410239839355772060744000713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-117601785536210480522661959442420000000000000)
      constant := (1688022007051429363693270681929399941750254156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree073.table
  base := (102406943211982301948778329718494917399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-239102782207506437443800264052200000000000000)
      constant := (3489195435681892721999413114678967079202321985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52320251231867975343/12500000000000000000)
  centralHi := (83712401970988760549/20000000000000000000)
  directionLo := (421458667323119192483/100000000000000000000)
  directionHi := (105364666830779798121/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree074.table
  base := (109088611507952168090044324498595508223/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-119311028773508223601446110748660000000000000)
      constant := (1739830741283713680602375424487672703753320345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree074.table
  base := (136359494271938780810029638358584240751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-121287341266633739036290285696500000000000000)
      constant := (1798014621193137873570045425981448131322320212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421458667323119192483/100000000000000000000)
  centralHi := (105364666830779798121/25000000000000000000)
  directionLo := (424335551691994388499/100000000000000000000)
  directionHi := (848671103383988777/200000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree075.table
  base := (421608192972547126712953793365545317033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-40340090670268655560076754018300000000000000)
      constant := (597473212221313529769627066113087566739205666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree075.table
  base := (843212104861789554336100073876399607993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-41007763809838086450226813122300000000000000)
      constant := (617411400713692996896878684404652515380389793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424335551691994388499/100000000000000000000)
  centralHi := (848671103383988777/200000000000000000)
  directionLo := (21359653122049923993/5000000000000000000)
  directionHi := (427193062440998479861/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree076.table
  base := (1149343208162843711953260394678614210377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-122729515248103709759014413361140000000000000)
      constant := (1845788691919699869026945489249437226683571731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree076.table
  base := (1149339601312302307401427867986599157747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-124759241592394779665070593037300000000000000)
      constant := (1907256459592039490513340156011899433227899841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21359653122049923993/5000000000000000000)
  centralHi := (427193062440998479861/100000000000000000000)
  directionLo := (21501579288838785809/5000000000000000000)
  directionHi := (430031585776775716181/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree077.table
  base := (2927646769696378497401363598647856215023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-248877516970802905675597129334760000000000000)
      constant := (3799875811927367779102959672193529222045824469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree077.table
  base := (2927640693136650183385462022392041458521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-252990383510550599958921493415400000000000000)
      constant := (3926162785221332414930974422101725099500839363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21501579288838785809/5000000000000000000)
  centralHi := (430031585776775716181/100000000000000000000)
  directionLo := (432851495242488442519/100000000000000000000)
  directionHi := (10821287381062211063/2500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree078.table
  base := (1786656796503909579067019395478552847987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-42049333907566398638860905324540000000000000)
      constant := (651622425954485277732913815554519715957614187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree078.table
  base := (1786654237596890104882126461964718757599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-42743713972718606764616966792700000000000000)
      constant := (673236333464330964595170915652570233488514999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432851495242488442519/100000000000000000000)
  centralHi := (10821287381062211063/2500000000000000000)
  directionLo := (54456644036452805673/12500000000000000000)
  directionHi := (87130630458324489077/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree079.table
  base := (4235686680502109110352009052870812605113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-255714489919993877990733734559720000000000000)
      constant := (4021153613632502503929703593243070950757696739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree079.table
  base := (2117841185434994305341266798520450137099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-129967092081036340608241054048500000000000000)
      constant := (2077139282244841236739590768800355072419783497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54456644036452805673/12500000000000000000)
  centralHi := (87130630458324489077/20000000000000000000)
  directionLo := (438436906828790091403/100000000000000000000)
  directionHi := (109609226707197522851/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree080.table
  base := (2457382927136846609378746853991715025991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-129566488197294682074151018586100000000000000)
      constant := (2067066492127971622489446594661697352347807773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree080.table
  base := (2457381112888793182309537293691116960669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-131703042243916860922631207718900000000000000)
      constant := (2135372237563867667610256199862671785644100207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438436906828790091403/100000000000000000000)
  centralHi := (109609226707197522851/25000000000000000000)
  directionLo := (55150387214977742483/12500000000000000000)
  directionHi := (88240619543964387973/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree081.table
  base := (2805275479890029247478238723509155288359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-43758577144864141717645056630780000000000000)
      constant := (708112111065223110116102196684967312905021759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree081.table
  base := (5610547905241467222403518293178042520169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-88959328271198254158014240926200000000000000)
      constant := (1462938577216424839577580593307556088594959569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55150387214977742483/12500000000000000000)
  centralHi := (88240619543964387973/20000000000000000000)
  directionLo := (221976026636625972031/50000000000000000000)
  directionHi := (443952053273251944063/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree082.table
  base := (1580760465524450909562216745253388052231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-132984974671890168231719321198580000000000000)
      constant := (2182386329492940725366750368834264373943116986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree082.table
  base := (6323039291117617121370990853603775070843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-270349885139355803102823030119400000000000000)
      constant := (4508492333132422282284895667456670256877787929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221976026636625972031/50000000000000000000)
  centralHi := (443952053273251944063/100000000000000000000)
  directionLo := (446684091695132922301/100000000000000000000)
  directionHi := (223342045847566461151/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree083.table
  base := (3526119221399787075174415814740452965331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-134694217909187911310503472504820000000000000)
      constant := (2241216480557741483969715762599859754488477793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree083.table
  base := (7052236279146598936490841354473106673439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-273821785465116843731603337460200000000000000)
      constant := (4629774278763642237990359893243953651372844517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446684091695132922301/100000000000000000000)
  centralHi := (223342045847566461151/50000000000000000000)
  directionLo := (89879904303793181303/20000000000000000000)
  directionHi := (112349880379741476629/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree084.table
  base := (7798140597348184317060902020050305055279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-90935640764323769592858415874040000000000000)
      constant := (1533884523988146517395512765063590843448780679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree084.table
  base := (779813877675130862610667833500642337423/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-46215614298479647393397274133500000000000000)
      constant := (792110261303425873835348272452675853598186115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89879904303793181303/20000000000000000000)
  centralHi := (112349880379741476629/25000000000000000000)
  directionLo := (2825616512577423101/625000000000000000)
  directionHi := (452098642012387696161/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree085.table
  base := (1712149646584317995557038301441361158461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (12282)
      previous := (8832)
      next := (0)
      square := (240362330244995120454021277440000000000000)
      linear := (-16248553456915693819773150013800000000000000)
      constant := (277790264165203576052332948949807923858667995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree085.table
  base := (4280373350601853907777667630199061193479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6072)
      previous := (4485)
      next := (0)
      square := (120181165122497560227010638720000000000000)
      linear := (-8257811356371733087916586827700000000000000)
      constant := (143445711754636306291546711864761369087806861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2825616512577423101/625000000000000000)
  centralHi := (452098642012387696161/100000000000000000000)
  directionLo := (454781743562134065543/100000000000000000000)
  directionHi := (56847717945266758193/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree086.table
  base := (4670030633298408184033116261683847435929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-139821947621081140546855926423540000000000000)
      constant := (2422387858500249358980875511318879061542553987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree086.table
  base := (9340059978098027796305702892138527798731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-284237486442399965617944259482600000000000000)
      constant := (5003252173694291537459187353913356932413497993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454781743562134065543/100000000000000000000)
  centralHi := (56847717945266758193/12500000000000000000)
  directionLo := (114362277009670089333/25000000000000000000)
  directionHi := (457449108038680357333/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree087.table
  base := (10136079623832969164747114522239243080697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-94354127238919255750426718486520000000000000)
      constant := (1656225749986303576333072531223704271252892897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree087.table
  base := (5068039270039278005197509520383580603773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-47951564461360167707787427803900000000000000)
      constant := (855159248234158331427017275481017693150413573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114362277009670089333/25000000000000000000)
  centralHi := (457449108038680357333/100000000000000000000)
  directionLo := (460101009141855543341/100000000000000000000)
  directionHi := (230050504570927771671/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree088.table
  base := (1368600404650433579180565925082725255343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-143240434095676626704424229036020000000000000)
      constant := (2547069544578783612167333438255922020669765716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree088.table
  base := (10948802325778927868889043734639764286923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-291181287093922046875504874164200000000000000)
      constant := (5260264146310768024333883225821394080730860169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460101009141855543341/100000000000000000000)
  centralHi := (230050504570927771671/50000000000000000000)
  directionLo := (462737712728629265129/100000000000000000000)
  directionHi := (46273771272862926513/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree089.table
  base := (11778232045335983228166803761143383115121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-289899354665948739566416760684520000000000000)
      constant := (5221161234117579900914725890457321818447289163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree089.table
  base := (5889115639468580465957246304696055729907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-147326593709841543752142590752500000000000000)
      constant := (2695589071986366697898097417412043322860464321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462737712728629265129/100000000000000000000)
  centralHi := (46273771272862926513/10000000000000000000)
  directionLo := (93071895424836601307/20000000000000000000)
  directionHi := (58169934640522875817/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree090.table
  base := (6312182996012740257306262866288114317053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-48886306856757370953997510549500000000000000)
      constant := (891623947400063481775756778643215385338654853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree090.table
  base := (12624365347656739631208217946178325364119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-99375029248481376044355162948600000000000000)
      constant := (1841232493995299197323293712748009824272073519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93071895424836601307/20000000000000000000)
  centralHi := (58169934640522875817/12500000000000000000)
  directionLo := (233983276708647808071/50000000000000000000)
  directionHi := (467966553417295616143/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree091.table
  base := (13487205025491593344262994378597210545323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-296736327615139711881553365909480000000000000)
      constant := (5479886439601927988694219812917314033885155369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree091.table
  base := (13487204483789098143088161278541191087513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-301596988071205168761845796186600000000000000)
      constant := (5657822159974557353732751033867456914055863939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233983276708647808071/50000000000000000000)
  centralHi := (467966553417295616143/100000000000000000000)
  directionLo := (470559185740999190261/100000000000000000000)
  directionHi := (235279592870499595131/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree092.table
  base := (14366749097756312183085009369215414678743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-300154814089735198039121668521960000000000000)
      constant := (5611589499347848786639702251456467880738231629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree092.table
  base := (14366748642417032099816617167291049778927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-305068888396966209390626103527400000000000000)
      constant := (5793552177588223735403347206152372061424967381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470559185740999190261/100000000000000000000)
  centralHi := (235279592870499595131/50000000000000000000)
  directionLo := (236568805769696609849/50000000000000000000)
  directionHi := (473137611539393219699/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree093.table
  base := (15262998164122022248699566996331678510873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-101191100188110228065563323711480000000000000)
      constant := (1914950954429789265448028207180818695806780673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree093.table
  base := (1526299778142204212647298837334208150639/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-51423464787121208336567735144700000000000000)
      constant := (988481255749707681059860705807031376999060195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236568805769696609849/50000000000000000000)
  centralHi := (473137611539393219699/100000000000000000000)
  directionLo := (475702061821442334133/100000000000000000000)
  directionHi := (237851030910721167067/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree094.table
  base := (404398804568331034893941920235590457147/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-153495893519463085177129136873460000000000000)
      constant := (2939838265549943345313604375344926246742360820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree094.table
  base := (3235190372224298905814429144240578096851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-312012689048488290648186718209000000000000000)
      constant := (6069828230394980815886036156980546154448641765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475702061821442334133/100000000000000000000)
  centralHi := (237851030910721167067/50000000000000000000)
  directionLo := (956505522805050883/200000000000000000)
  directionHi := (478252761402525441501/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree095.table
  base := (17105611114208193717852803780748014228823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-310410273513521656511826576359400000000000000)
      constant := (6016060502472109472091384446077176755027505869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree095.table
  base := (534550338873871159972405681939532006831/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-157742294687124665638483512774900000000000000)
      constant := (3105187132492706737188560021806286691988836688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (956505522805050883/200000000000000000)
  centralHi := (478252761402525441501/100000000000000000000)
  directionLo := (480789929134451102481/100000000000000000000)
  directionHi := (240394964567225551241/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree096.table
  base := (18051974921328668032017552595344373239221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-104609586662705714223131626323960000000000000)
      constant := (2051334925705207479625305707353930714795213821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree096.table
  base := (141031052299003237296273313563895200011/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-53159414950001728650957888815100000000000000)
      constant := (1058754272998526363738151440565100250574631104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480789929134451102481/100000000000000000000)
  centralHi := (240394964567225551241/50000000000000000000)
  directionLo := (96662755624921038643/20000000000000000000)
  directionHi := (471986111449809759/97656250000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree097.table
  base := (19015043568778537567962933745450300446387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-317247246462712628826963181584360000000000000)
      constant := (6293509354754853853792241793514628694383157761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree097.table
  base := (9507521689014477492586436213749818898333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-161214195012885706267263820115700000000000000)
      constant := (3248141174573385652691301109316389836863692399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96662755624921038643/20000000000000000000)
  centralHi := (471986111449809759/97656250000000000)
  directionLo := (485824515944851924417/100000000000000000000)
  directionHi := (242912257972425962209/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree098.table
  base := (9997408511461461034104142749541817043391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-160332866468654057492265742098420000000000000)
      constant := (3217287117563675373095618428470514798389579973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree098.table
  base := (9997408431345706840220964764239705783299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-162950145175766226581653973786100000000000000)
      constant := (3320822199099163475928735350640362424227082097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485824515944851924417/100000000000000000000)
  centralHi := (242912257972425962209/50000000000000000000)
  directionLo := (122080586207691942467/25000000000000000000)
  directionHi := (488322344830767769869/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree099.table
  base := (4198259050324262009184926394910759367557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-108028073137301200380699928936440000000000000)
      constant := (2192399805994106901647058604512054425575078785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree099.table
  base := (20991295117039185606363568877715112661271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-109790730225764497930696084971000000000000000)
      constant := (2262870594967403580727564872131937008031965871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122080586207691942467/25000000000000000000)
  centralHi := (488322344830767769869/100000000000000000000)
  directionLo := (245403730935874755723/50000000000000000000)
  directionHi := (490807461871749511447/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree100.table
  base := (11002239112034536023664114777424669272979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-163751352943249543649834044710900000000000000)
      constant := (3360692451539697603207092055928244694337055137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree100.table
  base := (11002239055520947519807830411088596227417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-166422045501527267210434281126900000000000000)
      constant := (3468592254512047827294595693147724316362534851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245403730935874755723/50000000000000000000)
  centralHi := (490807461871749511447/100000000000000000000)
  directionLo := (493280059192502160069/100000000000000000000)
  directionHi := (49328005919250216007/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree101.table
  base := (11517182955331361406045858122075870571829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-165460596180547286728618196017140000000000000)
      constant := (3433565345093789127561963673124318018071981687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree101.table
  base := (23034365815747623529790498641125497126091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-336315991328815575049648869594600000000000000)
      constant := (7087362570338069869408429675437702254074888073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493280059192502160069/100000000000000000000)
  centralHi := (49328005919250216007/10000000000000000000)
  directionLo := (495740324126379716411/100000000000000000000)
  directionHi := (123935081031594929103/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree102.table
  base := (6020239570721265587074646242733009636007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (2047)
      previous := (1472)
      next := (0)
      square := (40060388374165853409003546240000000000000)
      linear := (-3277839988585196662890242104380000000000000)
      constant := (68768988030238726858171382470916300948618142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree102.table
  base := (4816191640637482597939611223483062956519/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (4048)
      previous := (2990)
      next := (0)
      square := (80120776748331706818007092480000000000000)
      linear := (-6662507679501502268204493665400000000000000)
      constant := (141944038600507678562471876651964543161737035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495740324126379716411/100000000000000000000)
  centralHi := (123935081031594929103/25000000000000000000)
  directionLo := (249094219690510684623/50000000000000000000)
  directionHi := (498188439381021369247/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree103.table
  base := (6286063828301742264409761524618550346229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-168879082655142772886186498629620000000000000)
      constant := (3581651584777450561905616910337837096703249774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree103.table
  base := (6286063811573344830229495783222646715167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-171629895990168828153604742138100000000000000)
      constant := (3696267351838175083401062747880472624636896202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249094219690510684623/50000000000000000000)
  centralHi := (498188439381021369247/100000000000000000000)
  directionLo := (125156145799174397713/25000000000000000000)
  directionHi := (500624583196697590853/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree104.table
  base := (2622425697500315374351113535456645522197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-170588325892440515964970649935860000000000000)
      constant := (3656864930695737038178050322479601025048515955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree104.table
  base := (26224256918828220643077253717612113483499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-346731692306098696935989791617000000000000000)
      constant := (7547528775284715883184058313326527321511742697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125156145799174397713/25000000000000000000)
  centralHi := (500624583196697590853/100000000000000000000)
  directionLo := (251524464748877247353/50000000000000000000)
  directionHi := (503048929497754494707/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree105.table
  base := (27320963242479629579187505889884639663699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-114865046086492172695836534161400000000000000)
      constant := (2488572284797599505986375999139589947765281099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree105.table
  base := (5464192639064855329032351189811066192589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-116734530877286579188256699652600000000000000)
      constant := (2568042727750754867475007015538492915834619945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251524464748877247353/50000000000000000000)
  centralHi := (503048929497754494707/100000000000000000000)
  directionLo := (252730824018760301933/50000000000000000000)
  directionHi := (505461648037520603867/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree106.table
  base := (28434374090611024867564655287421062734273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-348013624734072004245077905096680000000000000)
      constant := (7619264148363601473267817248694466552515532219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree106.table
  base := (28434374051030604911852277397271630632231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-353675492957620778193550406298600000000000000)
      constant := (7862332927385864720858277881036910533823298493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252730824018760301933/50000000000000000000)
  centralHi := (505461648037520603867/100000000000000000000)
  directionLo := (253931452268508843771/50000000000000000000)
  directionHi := (507862904537017687543/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree107.table
  base := (14782244747543087573310792688354520298019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-175716055604333745201323103854580000000000000)
      constant := (3887185871557091462992509275031070321885442257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree107.table
  base := (5912897892373359403554448577631063506111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-357147393283381818822330713639400000000000000)
      constant := (8022143007497616811540615400507275942690920665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253931452268508843771/50000000000000000000)
  centralHi := (507862904537017687543/100000000000000000000)
  directionLo := (510252860817796420147/100000000000000000000)
  directionHi := (127563215204449105037/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree108.table
  base := (1535565471613034462951129182765559741873/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-59141766280543829426702418386940000000000000)
      constant := (1321839939743340948651673556144212208886116730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree108.table
  base := (30711309404382470625787775198187206777717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-120206431203047619817037006993400000000000000)
      constant := (2727852807801512513698459320350484924828841917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (510252860817796420147/100000000000000000000)
  centralHi := (127563215204449105037/25000000000000000000)
  directionLo := (64078959366149771979/12500000000000000000)
  directionHi := (512631674929198175833/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree109.table
  base := (3187483387911539904787332373385210749437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-179134542078929231358891406467060000000000000)
      constant := (4044633917110785600957319590143783997389284555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree109.table
  base := (15937416927860775578958907033360455326543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-182045596967451950039945664160500000000000000)
      constant := (4173289587464140479795289674727811632913015029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64078959366149771979/12500000000000000000)
  centralHi := (512631674929198175833/100000000000000000000)
  directionLo := (257499750635163088657/50000000000000000000)
  directionHi := (102999900254065235463/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree110.table
  base := (4131882851652472694457889507265805219447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-180843785316226974437675557773300000000000000)
      constant := (4124528165111867042680678084868780312509379764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree110.table
  base := (6611012558718120791902380550392586181069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-367563094260664940708671635661800000000000000)
      constant := (8511205261894891396415982051763566749854407035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257499750635163088657/50000000000000000000)
  centralHi := (102999900254065235463/20000000000000000000)
  directionLo := (517356490706992365911/100000000000000000000)
  directionHi := (64669561338374045739/12500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree111.table
  base := (34251996212699591978642887918148176399623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-121702019035683145010973139386360000000000000)
      constant := (2803468375431949870015512763619743406815419423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree111.table
  base := (1370079847849224013511795643720669238667/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-123678331528808660445817314334200000000000000)
      constant := (2892478894711527716893953857089936517244321675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517356490706992365911/100000000000000000000)
  centralHi := (64669561338374045739/12500000000000000000)
  directionLo := (519702790683890654261/100000000000000000000)
  directionHi := (259851395341945327131/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree112.table
  base := (8866408514052017537751393117080946399687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-184262271790822460595243860385780000000000000)
      constant := (4286657111135674503198196500528205249513515322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree112.table
  base := (35465634042391602648555773107728835220563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-374506894912187021966232250343400000000000000)
      constant := (8845273441481542958950439428295608101226053089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519702790683890654261/100000000000000000000)
  centralHi := (259851395341945327131/50000000000000000000)
  directionLo := (522038545332232576671/100000000000000000000)
  directionHi := (16313704541632268021/3125000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree113.table
  base := (18347988161450093577333025398924604757581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-185971515028120203674028011692020000000000000)
      constant := (4368891808993789256881551058734048690923404543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree113.table
  base := (73391952622619876471683196136354352793/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-188989397618974031297506278842100000000000000)
      constant := (4507357766886875941743657374155493253710944750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (522038545332232576671/100000000000000000000)
  centralHi := (16313704541632268021/3125000000000000000)
  directionLo := (131090973893266921053/25000000000000000000)
  directionHi := (524363895573067684213/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree114.table
  base := (37943022992409485228907539531242755088061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-125120505510278631168541441998840000000000000)
      constant := (2967937771095206220746597526471802405984046661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree114.table
  base := (37943022982687502409434231134066054191107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-127150231854569701074597621675000000000000000)
      constant := (3061920986950941271131571808385705806951069307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131090973893266921053/25000000000000000000)
  centralHi := (524363895573067684213/100000000000000000000)
  directionLo := (105335795843299653813/20000000000000000000)
  directionHi := (263339489608249134533/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree115.table
  base := (2450423377801696023061513560136988157861/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-189390001502715689831596314304500000000000000)
      constant := (4535701654005060433452716370061991348766315064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree115.table
  base := (3920677403667288918960331226747360933173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-192461297944735071926286586182900000000000000)
      constant := (4679207861281929113906402729729048286807744595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105335795843299653813/20000000000000000000)
  centralHi := (263339489608249134533/50000000000000000000)
  directionLo := (105796786211397215581/20000000000000000000)
  directionHi := (264491965528493038953/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree116.table
  base := (40487229460682905251659754098296353693843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-382198489480026865820760931221480000000000000)
      constant := (9240553602009158881532809524466126447873056929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree116.table
  base := (2024361472692204863185395763950894860679/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-194197248107615592240676739853300000000000000)
      constant := (4766336909377652625249523852079088325978782370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105796786211397215581/20000000000000000000)
  centralHi := (264491965528493038953/50000000000000000000)
  directionLo := (265639441482468762717/50000000000000000000)
  directionHi := (106255776592987505087/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree117.table
  base := (10446097305231938101327676091312708131061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-64269495992437058663054872305660000000000000)
      constant := (1568544032522348841854140863137088707697779322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree117.table
  base := (20892194607596299574783596634500402223337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-65311066090165370851688964507900000000000000)
      constant := (1618089541546473556918330835149835546182899537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265639441482468762717/50000000000000000000)
  centralHi := (106255776592987505087/20000000000000000000)
  directionLo := (106712792794948697979/20000000000000000000)
  directionHi := (66695495496842936237/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree118.table
  base := (5387281663364731939431478479470683929517/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-194517731214608919067948768223220000000000000)
      constant := (4791767543619722815080805688020278986808084604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree118.table
  base := (861965066042171906566465178569584627817/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-197669148433376632869457047194100000000000000)
      constant := (4943003006994627117599984642504461721271401275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106712792794948697979/20000000000000000000)
  centralHi := (66695495496842936237/12500000000000000000)
  directionLo := (2679196501847200051/500000000000000000)
  directionHi := (535839300369440010201/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree119.table
  base := (138840067813749568150303604870524582627/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2295000000000000000000000000000000000000000
      center := (6141)
      previous := (4416)
      next := (0)
      square := (120181165122497560227010638720000000000000)
      linear := (-11542763203053333067454877619380000000000000)
      constant := (286981361123023109027873399552571325348126880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree119.table
  base := (44428821696367303242230869114067707045843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (12144)
      previous := (8970)
      next := (0)
      square := (240362330244995120454021277440000000000000)
      linear := (-23459423364265547433393788337000000000000000)
      constant := (592063536043784467839465552602357077534041937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2679196501847200051/500000000000000000)
  centralHi := (535839300369440010201/100000000000000000000)
  directionLo := (107621003152429412281/20000000000000000000)
  directionHi := (269052507881073530703/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree120.table
  base := (11444023595874303434141082679282688659269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-65978739229734801741839023611900000000000000)
      constant := (1655459627970770417157722570273628546405517338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree120.table
  base := (45776094380116154503140274006230932629707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-134094032506091782332158236356600000000000000)
      constant := (3415253181801594301530029280250206655769867907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107621003152429412281/20000000000000000000)
  centralHi := (269052507881073530703/50000000000000000000)
  directionLo := (270180615587217008689/50000000000000000000)
  directionHi := (540361231174434017379/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree121.table
  base := (47140071338697414672649412275911928714509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-399290921853004296608602444283880000000000000)
      constant := (10109709556028306006967655487885260779759313727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree121.table
  base := (1178501783396569830408862143637192991681/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-202876998922018193812627508205300000000000000)
      constant := (5214022155917051118055584514136520338281736860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270180615587217008689/50000000000000000000)
  centralHi := (540361231174434017379/100000000000000000000)
  directionLo := (21704322604470095043/4000000000000000000)
  directionHi := (135652016277938094019/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree122.table
  base := (48520752548840121770563270719011563707121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-402709408327599782766170746896360000000000000)
      constant := (10288221642659934063785963221511327231606665163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree122.table
  base := (24260376273231892324413932091975157785729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-204612949084898714127017661875700000000000000)
      constant := (5305967205949261863306101413366682156202043387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21704322604470095043/4000000000000000000)
  centralHi := (135652016277938094019/25000000000000000000)
  directionLo := (54484563363606878633/10000000000000000000)
  directionHi := (544845633636068786331/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree123.table
  base := (24959068998552985148981690412916206471889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34799)
      previous := (25024)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-67687982467032544820623174918140000000000000)
      constant := (1744715671264710861732464983037275053033383289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree123.table
  base := (24959068997556978552839802178026932216933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (34408)
      previous := (25415)
      next := (0)
      square := (681026602360819507953060286080000000000000)
      linear := (-68782966415926411480469271848700000000000000)
      constant := (1799571640911152770226339052497548050696242733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54484563363606878633/10000000000000000000)
  centralHi := (544845633636068786331/100000000000000000000)
  directionLo := (273537025217912170483/50000000000000000000)
  directionHi := (547074050435824340967/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree124.table
  base := (51332227667006048067891311370073427266247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-409546381276790755081307352121320000000000000)
      constant := (10649926710684636344999298879163402952958525341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree124.table
  base := (25666113832668155638806064979755430460913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-208084849410659754755797969216500000000000000)
      constant := (5492265306205355447369107252571031623886504139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273537025217912170483/50000000000000000000)
  centralHi := (547074050435824340967/100000000000000000000)
  directionLo := (274646713446669728731/50000000000000000000)
  directionHi := (549293426893339457463/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree125.table
  base := (26381510771185975310403453520222908457141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (104397)
      previous := (75072)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-206482433875693120619437827366900000000000000)
      constant := (5416559845911442763800849166218299354691071223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree125.table
  base := (26381510770486220430082175649356681295481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-209820799573540275070188122886900000000000000)
      constant := (5586618356301911251179516757154430184148638243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274646713446669728731/50000000000000000000)
  centralHi := (549293426893339457463/100000000000000000000)
  directionLo := (551503872149777424831/100000000000000000000)
  directionHi := (8617248002340272263/1562500000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree126.table
  base := (54210519607346357882371271107146579884161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-138794451408660575798814652448760000000000000)
      constant := (3672624323626426016553973948953528254278702761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree126.table
  base := (54210519606173416236163264517265461779339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-141037833157613863589718851038200000000000000)
      constant := (3787849381974194082139230131131407466088060739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551503872149777424831/100000000000000000000)
  centralHi := (8617248002340272263/1562500000000000000)
  directionLo := (27685274658388691333/5000000000000000000)
  directionHi := (553705493167773826661/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree127.table
  base := (55674721846374081481109381217760096854447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-419801840700577213554012259958760000000000000)
      constant := (11204186547732436776317349823019462035755249941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree127.table
  base := (1391868046134777242869035890272833247659/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (103224)
      previous := (76245)
      next := (0)
      square := (2043079807082458523859180858240000000000000)
      linear := (-213292699899301315698968430227700000000000000)
      constant := (5777732456122833965241251307431478356629663540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27685274658388691333/5000000000000000000)
  centralHi := (553705493167773826661/100000000000000000000)
  directionLo := (138974598697958382561/25000000000000000000)
  directionHi := (111179678958366706049/20000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree128.table
  base := (11431125648838707803594414364656251432613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (208794)
      previous := (150144)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-423220327175172699711580562571240000000000000)
      constant := (11392060422263275580108201622134343649643396195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree128.table
  base := (57155628243369786449618103203419636841649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (206448)
      previous := (152490)
      next := (0)
      square := (4086159614164917047718361716480000000000000)
      linear := (-430057300124363672026717167796200000000000000)
      constant := (11748987011454039523727473217696283426275387147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell022.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138974598697958382561/25000000000000000000)
  centralHi := (111179678958366706049/20000000000000000000)
  directionLo := (558082679806591736993/100000000000000000000)
  directionHi := (279041339903295868497/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 64
  qDenominator := 153
  table := BinomialMassData.Q64_153.Degree129.table
  base := (58653238785828617559915825524195009323231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (69598)
      previous := (50048)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-142212937883256061956382955061240000000000000)
      constant := (3860498198118311950605979559312271219249723831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q64_153.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 65
  qDenominator := 153
  table := BinomialMassData.Q65_153.Degree129.table
  base := (58653238785138349894171936376625411005267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (68816)
      previous := (50830)
      next := (0)
      square := (1362053204721639015906120572160000000000000)
      linear := (-144509733483374904218499158379000000000000000)
      constant := (3981371481143625697206594712246602694024699467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q65_153.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell022.Kernel129
