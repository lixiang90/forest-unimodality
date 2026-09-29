import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell031.Parameters
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch050_099
import ForestUnimodality.BinomialMassData.Q1677_3572.Batch100_149
import ForestUnimodality.BinomialMassData.Q841_1786.Batch000_049
import ForestUnimodality.BinomialMassData.Q841_1786.Batch050_099
import ForestUnimodality.BinomialMassData.Q841_1786.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree000.table
  base := (2745792915921098272857392449/50000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (179172743398393119473865908000000000000)
      linear := (10869380223262463738831407000000000000)
      constant := (109831716636843930914295697960000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree000.table
  base := (2745792915921098272857392449/50000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (179172743398393119473865908000000000000)
      linear := (10869380223262463738831407000000000000)
      constant := (109831716636843930914295697960000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree001.table
  base := (317423248866079906866536421069992505900063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-627466399992800353750668424222255000000000000)
      constant := (253265971904569912803768872893465211337499339287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree001.table
  base := (316733896557973595330183154039925316650343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-629466415740984916946795452420305000000000000)
      constant := (252717128308039901695677742718916361337499375007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49906795889839124337/100000000000000000000)
  directionHi := (24953397944919562169/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree002.table
  base := (190605516419333382018697012834778961196107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-1298271681933902849731673681848225000000000000)
      constant := (152587350441125737665400966230310495326874331043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree002.table
  base := (189853265587290518417359198396066916397631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-1302271713430271976123927738244325000000000000)
      constant := (151991108945688965977678197210799451414374443319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906795889839124337/100000000000000000000)
  centralHi := (24953397944919562169/50000000000000000000)
  directionLo := (17644716900499081521/25000000000000000000)
  directionHi := (14115773520399265217/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree003.table
  base := (29995353381463658455241147134465249379649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-1969076963875005345712678939474195000000000000)
      constant := (97035215610223434950944734948752984610206861604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree003.table
  base := (29838900164389093641273184494485524286177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-1975077011119559035301060024068345000000000000)
      constant := (96544443162535613189723654096138929925950249892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17644716900499081521/25000000000000000000)
  centralHi := (14115773520399265217/20000000000000000000)
  directionLo := (86441106124170981383/100000000000000000000)
  directionHi := (10805138265521372673/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree004.table
  base := (79614341373940753692185541236061163140663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-2639882245816107841693684197100165000000000000)
      constant := (65926452626069331915267816345562763485358568687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree004.table
  base := (39570085333393477651523709775673812757209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-2647882308808846094478192309892365000000000000)
      constant := (65563129042033638271352858824672662618847119682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441106124170981383/100000000000000000000)
  centralHi := (10805138265521372673/12500000000000000000)
  directionLo := (49906795889839124337/50000000000000000000)
  directionHi := (3992543671187129947/4000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree005.table
  base := (2784296169185969896432464839463845474187/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-662137505551442067534937890945227000000000000)
      constant := (9648322180684161588837983356657838938179795852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree005.table
  base := (55337303822462261618527457812598473989783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-3320687606498133153655324595716385000000000000)
      constant := (47986810682909760529890570101762327984678463567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906795889839124337/50000000000000000000)
  centralHi := (3992543671187129947/4000000000000000000)
  directionLo := (111594988148887387979/100000000000000000000)
  directionHi := (5579749407444369399/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree006.table
  base := (40796554013442697142526977915151536698289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-3981492809698312833655694712352105000000000000)
      constant := (38079882402616566342256285901994210288513864761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree006.table
  base := (40539035079626135664724655937335188952439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-3993492904187420212832456881540405000000000000)
      constant := (37908013768028736846557438178019304094933528111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111594988148887387979/100000000000000000000)
  centralHi := (5579749407444369399/5000000000000000000)
  directionLo := (122246184627334606587/100000000000000000000)
  directionHi := (30561546156833651647/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree007.table
  base := (7745191638996875209292170112653655112229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-4652298091639415329636699969978075000000000000)
      constant := (32279009663527957869063954276741463462367615284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree007.table
  base := (7696341857485885313807676466127217279509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-4666298201876707272009589167364425000000000000)
      constant := (32168842643090800949538344198468205669308690164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/100000000000000000000)
  centralHi := (30561546156833651647/25000000000000000000)
  directionLo := (132040970656574784211/100000000000000000000)
  directionHi := (33010242664143696053/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree008.table
  base := (3012172496336374953171083352686470437099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-5323103373580517825617705227604045000000000000)
      constant := (29131510006459465841595093684743155308753283608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree008.table
  base := (1197160071025612718330225443159459570229/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-1067820699913198866237344290637689000000000000)
      constant := (5813651856495705438712841484245475499278183284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132040970656574784211/100000000000000000000)
  centralHi := (33010242664143696053/25000000000000000000)
  directionLo := (17644716900499081521/12500000000000000000)
  directionHi := (141157735203992652169/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree009.table
  base := (94892230040466364022755813640045958667/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-1198781731104324064319742097046003000000000000)
      constant := (5541200853565505191100271097283797887721619320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree009.table
  base := (18851566854800336453378269021934511076103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-6011908797255281390363853739012465000000000000)
      constant := (27680449163937717717490279464513591423127261247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17644716900499081521/12500000000000000000)
  centralHi := (141157735203992652169/100000000000000000000)
  directionLo := (37430096917379343253/25000000000000000000)
  directionHi := (149720387669517373013/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree010.table
  base := (1872135092894301677692196791112921456831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-6664713937462722817579715742855985000000000000)
      constant := (27486635508492989450877423201647202322627392952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree010.table
  base := (371716632938522805776767308500192276391/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-1336942818988913689908197204967297000000000000)
      constant := (5498722156602443618516447381746603644925812472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37430096917379343253/25000000000000000000)
  centralHi := (149720387669517373013/100000000000000000000)
  directionLo := (3945478643325533921/2500000000000000000)
  directionHi := (157819145733021356841/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree011.table
  base := (2931684368020225702618692098835793969273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-7335519219403825313560721000481955000000000000)
      constant := (28181101426062418661157381590229640260011138308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree011.table
  base := (5815674347097336772668283580372698989281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-7357519392633855508718118310660505000000000000)
      constant := (28218152038910771570465645063491139372606288338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3945478643325533921/2500000000000000000)
  centralHi := (157819145733021356841/100000000000000000000)
  directionLo := (82761058227723708309/50000000000000000000)
  directionHi := (165522116455447416619/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree012.table
  base := (1802574290269661226037003836443153794957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-1601264900268985561908345251621585000000000000)
      constant := (5923662705871399309335778886890363550634664693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree012.table
  base := (446361095810318925056504409365868891277/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-1606064938064628513579050119296905000000000000)
      constant := (5936939739321813811435624308127193125919809492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761058227723708309/50000000000000000000)
  centralHi := (165522116455447416619/100000000000000000000)
  directionLo := (86441106124170981383/50000000000000000000)
  directionHi := (172882212248341962767/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree013.table
  base := (6704360388345674742970559899634345362249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-8677129783286030305522731515733895000000000000)
      constant := (31693708477256414727258515305485291574780102801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree013.table
  base := (3313234287128320245976881983952023022537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-8703129988012429627072382882308545000000000000)
      constant := (31789728790311775022754848279405421114598216226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441106124170981383/50000000000000000000)
  centralHi := (172882212248341962767/100000000000000000000)
  directionLo := (89970755787465216623/50000000000000000000)
  directionHi := (179941511574930433247/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree014.table
  base := (4716716190332879870499124481431252590289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-9347935065227132801503736773359865000000000000)
      constant := (34339911324693150248743956961130733446873372761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree014.table
  base := (580670982144737896077534979401971328641/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-9375935285701716686249515168132565000000000000)
      constant := (34466479242858183844092750385684056072427494472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89970755787465216623/50000000000000000000)
  centralHi := (179941511574930433247/100000000000000000000)
  directionLo := (18673413149143593669/10000000000000000000)
  directionHi := (186734131491435936691/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree015.table
  base := (2992229542136553359789243429183625527737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-10018740347168235297484742030985835000000000000)
      constant := (37510901835991515850908299531340327993468342913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree015.table
  base := (146332391014452953310698289167367015797/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-2009748116678200749085329490791317000000000000)
      constant := (7533855719856427598880458345786553137521207412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18673413149143593669/10000000000000000000)
  centralHi := (186734131491435936691/100000000000000000000)
  directionLo := (193288189343919691331/100000000000000000000)
  directionHi := (48322047335979922833/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree016.table
  base := (1489150165562932417690180009313906127877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-10689545629109337793465747288611805000000000000)
      constant := (41173386293556173588116281158659385127769385773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree016.table
  base := (1428800290680264118807760881633927857153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-10721545881080290804603779739780605000000000000)
      constant := (41365026208557008293154003497053814135758802697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193288189343919691331/100000000000000000000)
  centralHi := (48322047335979922833/25000000000000000000)
  directionLo := (199627183559356497349/100000000000000000000)
  directionHi := (3992543671187129947/2000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree017.table
  base := (175703209027078766883841768533357977223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-11360350911050440289446752546237775000000000000)
      constant := (45302025873765566016058866334305255285578504127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree017.table
  base := (120180671294209338166819322055562836909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-11394351178769577863780912025604625000000000000)
      constant := (45528487118419989724988996135287484028730245141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199627183559356497349/100000000000000000000)
  centralHi := (3992543671187129947/2000000000000000000)
  directionLo := (20577099088994803289/10000000000000000000)
  directionHi := (205770990889948032891/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree018.table
  base := (-973293481779699423910435679491002131547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-12031156192991542785427757803863745000000000000)
      constant := (49876739092848381142573120524061087341199976397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree018.table
  base := (-204864950344737865969217144247624002733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-2413431295291772984591608862285729000000000000)
      constant := (10027926884574291618103918449717245486644571883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20577099088994803289/10000000000000000000)
  centralHi := (205770990889948032891/100000000000000000000)
  directionLo := (52934150701497244563/25000000000000000000)
  directionHi := (211736602805988978253/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree019.table
  base := (-989201341663161597346662126006933363809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-35185488850228934297531199616315000000000000)
      constant := (152025285831779097931389329385551368398691838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree019.table
  base := (-405048594987524613522600805626484557099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (395792590167050400917769790772000000000000)
      linear := (-7058150567395098051044419167453000000000000)
      constant := (30571799938519831410275018627163595613368309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52934150701497244563/25000000000000000000)
  centralHi := (211736602805988978253/100000000000000000000)
  directionLo := (217538679879719788129/100000000000000000000)
  directionHi := (21753867987971978813/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree020.table
  base := (-44637004689270523864147903229911293671/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-13372766756873747777389768319115685000000000000)
      constant := (60301521761537149691586310477909795001494702144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree020.table
  base := (-2899698301261700645162052706165161631581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-13412767071837439041312308883076685000000000000)
      constant := (60642224758655949415519293296330748022057363131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217538679879719788129/100000000000000000000)
  centralHi := (21753867987971978813/10000000000000000000)
  directionLo := (111594988148887387979/50000000000000000000)
  directionHi := (223189976297774775959/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree021.table
  base := (-3622884472353831426993634968511192628711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-14043572038814850273370773576741655000000000000)
      constant := (66126361484024222127164373055371450449427041761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree021.table
  base := (-3662172457684432319424538462433591101477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-14085572369526726100489441168900705000000000000)
      constant := (66508463593049158734558632669219602709718267827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111594988148887387979/50000000000000000000)
  centralHi := (223189976297774775959/100000000000000000000)
  directionLo := (228701669857898784871/100000000000000000000)
  directionHi := (28587708732237348109/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree022.table
  base := (-1072279372834508980319591044071433441461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-14714377320755952769351778834367625000000000000)
      constant := (72345785866110425633628514567715590394161468044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree022.table
  base := (-4325021842979696284626626266589082751131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-14758377667216013159666573454724725000000000000)
      constant := (72770961794362093260556965711813337549193335181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228701669857898784871/100000000000000000000)
  centralHi := (28587708732237348109/12500000000000000000)
  directionLo := (58520905490998146869/25000000000000000000)
  directionHi := (234083621963992587477/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree023.table
  base := (-973216169174149764117481436360019592029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-3077036520539411053066556818398719000000000000)
      constant := (15790266238352368772614986642670647736356065979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree023.table
  base := (-979770066883781840000572906814480430289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-3086236592981060043768741148109749000000000000)
      constant := (15884252662253707810004872204953425895346467239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58520905490998146869/25000000000000000000)
  centralHi := (234083621963992587477/100000000000000000000)
  directionLo := (239344584956024138229/100000000000000000000)
  directionHi := (23934458495602413823/10000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree024.table
  base := (-5362918833007317702854575527051941309657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-16055987884638157761313789349619565000000000000)
      constant := (85935705350435986944827888911929906454555335007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree024.table
  base := (-53927919782723851334194061864618132379/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-3220797652518917455604167605274553000000000000)
      constant := (17290416841540856083971004565384262699049976580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344584956024138229/100000000000000000000)
  centralHi := (23934458495602413823/10000000000000000000)
  directionLo := (122246184627334606587/50000000000000000000)
  directionHi := (9779694770186768527/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree025.table
  base := (-5787530029280810922078830878260999875899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-16726793166579260257294794607245535000000000000)
      constant := (93292609630175136053059263681680331409964218349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree025.table
  base := (-2907367112531486880596206768682858655879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-16776793560283874337197970312196785000000000000)
      constant := (93857134644137321418520303797451183595455894658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/50000000000000000000)
  centralHi := (9779694770186768527/4000000000000000000)
  directionLo := (249533979449195621687/100000000000000000000)
  directionHi := (31191747431149452711/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree026.table
  base := (-6146748843167899943172746986457861787009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-17397598448520362753275799864871505000000000000)
      constant := (101016593938773978004745990497418922075811459959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree026.table
  base := (-1542874893648039293054898083473360651823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-17449598857973161396375102598020805000000000000)
      constant := (101630974024923469955710817386030153086257601892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533979449195621687/100000000000000000000)
  centralHi := (31191747431149452711/12500000000000000000)
  directionLo := (127237863051590942473/50000000000000000000)
  directionHi := (254475726103181884947/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree027.table
  base := (-6446496203761210345313479312227700700639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-18068403730461465249256805122497475000000000000)
      constant := (109102936637248527624398825914257492303976130089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree027.table
  base := (-323449824610874281151190330745706078631/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-3624480831132489691110446976768965000000000000)
      constant := (21953778130054362587382532437545214233207150724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127237863051590942473/50000000000000000000)
  centralHi := (254475726103181884947/100000000000000000000)
  directionLo := (5186466367450258883/2000000000000000000)
  directionHi := (259323318372512944151/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree028.table
  base := (-3345953221936193726613643171847401831083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-18739209012402567745237810380123445000000000000)
      constant := (117547543357032471159460139827099817514409385466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree028.table
  base := (-839043319206338789721163601383208985509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-18795209453351735514729367169668845000000000000)
      constant := (118266800324752590076116259265979161021718667672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5186466367450258883/2000000000000000000)
  centralHi := (259323318372512944151/100000000000000000000)
  directionLo := (264081941313149568423/100000000000000000000)
  directionHi := (33010242664143696053/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree029.table
  base := (-3443717574255539266344814054150323455907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-19410014294343670241218815637749415000000000000)
      constant := (126346860996315450407484557412522719920820837514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree029.table
  base := (-6905992540010767397537223116260706481677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-19468014751041022573906499455492865000000000000)
      constant := (127121160157005286866552607213478003376893158027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081941313149568423/100000000000000000000)
  centralHi := (33010242664143696053/12500000000000000000)
  directionLo := (268756320862806566507/100000000000000000000)
  directionHi := (67189080215701641627/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree030.table
  base := (-1407390276624985645261906765049025223771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-4016163915256954547439964179075077000000000000)
      constant := (27099560834545061319173630185740892384329039821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree030.table
  base := (-7053790876523828267961924406888520256101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-20140820048730309633083631741316885000000000000)
      constant := (136328894844589718146969979419420831410292513651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756320862806566507/100000000000000000000)
  centralHi := (67189080215701641627/25000000000000000000)
  directionLo := (54670155763341995231/20000000000000000000)
  directionHi := (68337694704177494039/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree031.table
  base := (-357190843671368189966142533161746740513/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-4150324971645175046636165230600271000000000000)
      constant := (28999538416290718573075171857361411894098594652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree031.table
  base := (-7159090980553830105357853738009730896379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-20813625346419596692260764027140905000000000000)
      constant := (145887333397978429580053601178890610606413462829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54670155763341995231/20000000000000000000)
  centralHi := (68337694704177494039/25000000000000000000)
  directionLo := (5557385592369561781/2000000000000000000)
  directionHi := (277869279618478089051/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree032.table
  base := (-56335579344110867718449255481724948231/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-21422430140166977729161831410627325000000000000)
      constant := (154844194148589002095659349266746461985041571968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree032.table
  base := (-903100442429079078170111121424489613007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-21486430644108883751437896312964925000000000000)
      constant := (155794154692469316967429357326895457460777446856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5557385592369561781/2000000000000000000)
  centralHi := (277869279618478089051/100000000000000000000)
  directionLo := (282315470407985304337/100000000000000000000)
  directionHi := (141157735203992652169/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree033.table
  base := (-181022633381400505028698968587009831557/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-4418647084421616045028567333650659000000000000)
      constant := (33007056635123970136424314365753372274677615256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree033.table
  base := (-7253459357882397977848931828553135715139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-22159235941798170810615028598788945000000000000)
      constant := (166047340540367496824839265013522087977098119589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315470407985304337/100000000000000000000)
  centralHi := (141157735203992652169/50000000000000000000)
  directionLo := (35836589434645931391/12500000000000000000)
  directionHi := (286692715477167451129/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree034.table
  base := (-1808970699808343470015076485998479829403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-22764040704049182721123841925879265000000000000)
      constant := (175569194895807158789179737764267280534089628212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree034.table
  base := (-7247260134123167297121793575455104072773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-22832041239487457869792160884612965000000000000)
      constant := (176645135199629095569777074044531027712271243923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35836589434645931391/12500000000000000000)
  centralHi := (286692715477167451129/100000000000000000000)
  directionLo := (72751031514878773869/25000000000000000000)
  directionHi := (291004126059515095477/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree035.table
  base := (-1439562606506957610422705611630081816831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-4686969197198057043420969436701047000000000000)
      constant := (37288878607193560276420743457549072885249935881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree035.table
  base := (-7208122307046396747244068969270316551357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-23504846537176744928969293170436985000000000000)
      constant := (187586010407976560375665637395413017836436911707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72751031514878773869/25000000000000000000)
  centralHi := (291004126059515095477/100000000000000000000)
  directionLo := (295252586203156256119/100000000000000000000)
  directionHi := (7381314655078906403/2500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree036.table
  base := (-7128374488651844250544822747005559511721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-24105651267931387713085852441131205000000000000)
      constant := (197659539115043370258795040361589908572937600271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree036.table
  base := (-7137714943504271098057570206828012126103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-24177651834866031988146425456261005000000000000)
      constant := (198868635169717683349979371771618778558051288753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295252586203156256119/100000000000000000000)
  centralHi := (7381314655078906403/2500000000000000000)
  directionLo := (37430096917379343253/12500000000000000000)
  directionHi := (11977631013561389841/4000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree037.table
  base := (-175725758624660020152513995761203220707/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-4955291309974498041813371539751435000000000000)
      constant := (41842693264735586179051669023860088522803388456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree037.table
  base := (-1759373123143160519219996597865126116929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-24850457132555319047323557742085025000000000000)
      constant := (210491849635891375608620513315385059672724343516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37430096917379343253/12500000000000000000)
  centralHi := (11977631013561389841/4000000000000000000)
  directionLo := (303571188045954622397/100000000000000000000)
  directionHi := (151785594022977311199/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree038.table
  base := (-6901056844626280837543718161621220642451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-70491030005023802507057792122945000000000000)
      constant := (612479659066751639427310838884811223600825741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree038.table
  base := (-1381744622993224052924429152533857398403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (395792590167050400917769790772000000000000)
      linear := (-14140311595703382884487916912969000000000000)
      constant := (123243569259281956597480500253711709006927773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303571188045954622397/100000000000000000000)
  centralHi := (151785594022977311199/50000000000000000000)
  directionLo := (153823075713319428759/50000000000000000000)
  directionHi := (307646151426638857519/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree039.table
  base := (-6745567829787064544052325388995402165141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-26118067113754695201028868214009115000000000000)
      constant := (233333722680940630858543324545693930538810474691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree039.table
  base := (-844064149449476109196299144470059679341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-26196067727933893165677822313733065000000000000)
      constant := (234756131515514377153940207296742475530153591128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153823075713319428759/50000000000000000000)
  centralHi := (307646151426638857519/100000000000000000000)
  directionLo := (311667840438522737971/100000000000000000000)
  directionHi := (77916960109630684493/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree040.table
  base := (-6563535987182707820524612891700458351233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-26788872395695797697009873471635085000000000000)
      constant := (245898387929160440556679980529076011188267595383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree040.table
  base := (-3284914281029720714508249140870866696371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-26868873025623180224854954599557085000000000000)
      constant := (247395546445170727093073829867490236447691284842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667840438522737971/100000000000000000000)
  centralHi := (77916960109630684493/25000000000000000000)
  directionLo := (315638291466042713681/100000000000000000000)
  directionHi := (157819145733021356841/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree041.table
  base := (-6355811253305406680975315521990482013111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-27459677677636900192990878729261055000000000000)
      constant := (258798474886751005708489144494367919609126646161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree041.table
  base := (-6361512859058406804167888922926702094901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-27541678323312467284032086885381105000000000000)
      constant := (260372214538349503620302780592614681841123292451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638291466042713681/100000000000000000000)
  centralHi := (157819145733021356841/50000000000000000000)
  directionLo := (319559414374842970123/100000000000000000000)
  directionHi := (79889853593710742531/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree042.table
  base := (-6123136765644230639077812577677081707883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-28130482959578002688971883986887025000000000000)
      constant := (272033390939464805319361493793909086369130409533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree042.table
  base := (-1532075866588656717034222093613515607671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-28214483621001754343209219171205125000000000000)
      constant := (273685547772296941903025306372730767368713474884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319559414374842970123/100000000000000000000)
  centralHi := (79889853593710742531/25000000000000000000)
  directionLo := (40429125406301816883/12500000000000000000)
  directionHi := (64686600650082907013/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree043.table
  base := (-586616269266866089838951495725152440109/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-5760257648303821036990577848902599000000000000)
      constant := (57120523522221204014600274932821709823575036118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree043.table
  base := (-2935422647160448178397782089325595520147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-28887288918691041402386351457029145000000000000)
      constant := (287335031863881167151914962818277068856108589994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40429125406301816883/12500000000000000000)
  centralHi := (64686600650082907013/20000000000000000000)
  directionLo := (319590572258308417/97656250000000000)
  directionHi := (327260745992507819009/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree044.table
  base := (-2792729114826174918694286052518795740791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-29472093523460207680933894502138965000000000000)
      constant := (299505700997472871153843765308739752710603915682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree044.table
  base := (-2794851372548312892216851608713092479047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-29560094216380328461563483742853165000000000000)
      constant := (301320216731180508591761873670062856231352897794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319590572258308417/97656250000000000)
  centralHi := (327260745992507819009/100000000000000000000)
  directionLo := (331044232910894833237/100000000000000000000)
  directionHi := (165522116455447416619/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree045.table
  base := (-2640761004018033414664132322128472815589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-30142898805401310176914899759764935000000000000)
      constant := (313742243465421548465957210348095205463362735078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree045.table
  base := (-52853700877491974639780097385357562247/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-6046579902813923104148123205735437000000000000)
      constant := (63128141643964290252900990310483757446873841940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331044232910894833237/100000000000000000000)
  centralHi := (165522116455447416619/50000000000000000000)
  directionLo := (334784964446662163937/100000000000000000000)
  directionHi := (167392482223331081969/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree046.table
  base := (-2477395566059240718146762053248967260303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-30813704087342412672895905017390905000000000000)
      constant := (328311896446566182265726643217241311114477265906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree046.table
  base := (-2479140230870983329649142576656894261929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-30905704811758902579917748314501205000000000000)
      constant := (330296160923172081978326487199678067655437961758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334784964446662163937/100000000000000000000)
  centralHi := (167392482223331081969/50000000000000000000)
  directionLo := (21155272382835549343/6250000000000000000)
  directionHi := (338484358125368789489/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree047.table
  base := (-575706128455964447551195494711354080433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (39710)
      previous := (19855)
      next := (19855)
      square := (323406801834099580650327963940000000000000)
      linear := (-14252833575954511167440882876875000000000000)
      constant := (155370916332470510853089739503388609415709496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree047.table
  base := (-4608813693643933684887499882175086414977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (39710)
      previous := (19855)
      next := (19855)
      square := (323406801834099580650327963940000000000000)
      linear := (-14295387102511629533315926030025000000000000)
      constant := (156308860094574367587792836506587293804193303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21155272382835549343/6250000000000000000)
  centralHi := (338484358125368789489/100000000000000000000)
  directionLo := (34214375483345151331/10000000000000000000)
  directionHi := (342143754833451513311/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree048.table
  base := (-846886452341419697657999227613094531467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-6431062930244923532971583106528569000000000000)
      constant := (71689869653184208656753837231440649378976172317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree048.table
  base := (-1059325771679514308706843125371524967907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-32251315407137476698272012886149245000000000000)
      constant := (360610775504695796186191845085533731143470123028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34214375483345151331/10000000000000000000)
  centralHi := (342143754833451513311/100000000000000000000)
  directionLo := (345764424496683925533/100000000000000000000)
  directionHi := (172882212248341962767/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree049.table
  base := (-3841436471581635422444770888985866329411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-32826119933165720160838920790268815000000000000)
      constant := (374016642953389946532025200689869247381477527461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree049.table
  base := (-384404132122562048038965823902821239863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-6584824140965352751489829034394653000000000000)
      constant := (75253887638586691305790280998497245710184981026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345764424496683925533/100000000000000000000)
  centralHi := (172882212248341962767/50000000000000000000)
  directionLo := (174673785614436935181/50000000000000000000)
  directionHi := (349347571228873870363/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree050.table
  base := (-1713460760786920250645638692512962077649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-33496925215106822656819926047894785000000000000)
      constant := (389916031012305892638025449581108649308281765198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree050.table
  base := (-3429285584494618509683263365431974453437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-33596926002516050816626277457797285000000000000)
      constant := (392262054919850236674695696367300762404081117787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174673785614436935181/50000000000000000000)
  centralHi := (349347571228873870363/100000000000000000000)
  directionLo := (352894338009981630421/100000000000000000000)
  directionHi := (176447169004990815211/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree051.table
  base := (-598223198118697032623772725770406975971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-6833546099409585030560186261104151000000000000)
      constant := (81229466032529172655615506111108628727418902021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree051.table
  base := (-2993262033601460837578437264809306374429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-34269731300205337875803409743621305000000000000)
      constant := (408588445336711710932200953708866665941017968379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352894338009981630421/100000000000000000000)
  centralHi := (176447169004990815211/50000000000000000000)
  directionLo := (356405810945182582939/100000000000000000000)
  directionHi := (17820290547259129147/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree052.table
  base := (-10136884317673889832825871819210954339/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-6967707155797805529756387312629345000000000000)
      constant := (84542075991410144088527910903478559183665939450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree052.table
  base := (-634042419886756656445981795681493446423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-34942536597894624934980542029445325000000000000)
      constant := (425248450742394239214841698234954764930573700292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356405810945182582939/100000000000000000000)
  centralHi := (17820290547259129147/5000000000000000000)
  directionLo := (359883023149860866493/100000000000000000000)
  directionHi := (179941511574930433247/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree053.table
  base := (-411282802901280688140100829749399326829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-7101868212186026028952588364154539000000000000)
      constant := (87921007813291815325736703587906037756219540779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree053.table
  base := (-2058183769760462532473398090885130577127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-35615341895583911994157674315269345000000000000)
      constant := (442241931386010695949203998987545351006400650977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359883023149860866493/100000000000000000000)
  centralHi := (179941511574930433247/50000000000000000000)
  directionLo := (363326958299922131807/100000000000000000000)
  directionHi := (11353967446872566619/3125000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree054.table
  base := (-311570202972850666588178119655427095693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-7236029268574246528148789415679733000000000000)
      constant := (91366236582836007690425935048737641817966712843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree054.table
  base := (-779729367685309689076585268439360313803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-36288147193273199053334806601093365000000000000)
      constant := (459568764116611810177325911152281776114236222906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363326958299922131807/100000000000000000000)
  centralHi := (11353967446872566619/3125000000000000000)
  directionLo := (366738553882003819761/100000000000000000000)
  directionHi := (183369276941001909881/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree055.table
  base := (-129833734941191653228900215520706001781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-36850951624812335136724952336024635000000000000)
      constant := (474388701612508941731048061911596253156685946648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree055.table
  base := (-1040130760716458348565651933246283065103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-36960952490962486112511938886917385000000000000)
      constant := (477228840334132661640598337680441797316016677753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366738553882003819761/100000000000000000000)
  centralHi := (183369276941001909881/50000000000000000000)
  directionLo := (289155237635950753/78125000000000000)
  directionHi := (370118704174016963841/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree056.table
  base := (-99798449096926307963615889322683787001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-7504351381350687526541191518730121000000000000)
      constant := (98455499632431163560388384758126409136739839551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree056.table
  base := (-250160012413440571249728098069260878741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-37633757788651773171689071172741405000000000000)
      constant := (495222064201926831708223997193204951963017736582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289155237635950753/78125000000000000)
  centralHi := (370118704174016963841/100000000000000000000)
  directionLo := (18673413149143593669/5000000000000000000)
  directionHi := (373468262982871873381/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree057.table
  base := (61074440851828762050376974342576714209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-105796571159818670716584384629575000000000000)
      constant := (1414120462271694133522303371673070251961687681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree057.table
  base := (59867342082494044622702450896185216133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-106112363120058338589657073292425000000000000)
      constant := (1422571609658060958077233356387027173142437797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18673413149143593669/5000000000000000000)
  centralHi := (373468262982871873381/100000000000000000000)
  directionLo := (37678804616313613741/10000000000000000000)
  directionHi := (376788046163136137411/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree058.table
  base := (160358800295487238664767875378561174733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-38863367470635642624667968108902545000000000000)
      constant := (529048592025937553889432533841875590420918624468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree058.table
  base := (320168774909592144617642713266675481519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-38979368384030347290043335744389445000000000000)
      constant := (532207626195136978798655655891838739192123690062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37678804616313613741/10000000000000000000)
  centralHi := (376788046163136137411/100000000000000000000)
  directionLo := (190039416968838120193/50000000000000000000)
  directionHi := (380078833937676240387/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree059.table
  base := (1242006019544635398414417393140987480541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-39534172752576745120648973366528515000000000000)
      constant := (547930746601279574703784707640693487325369939909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree059.table
  base := (387814892137166264265207859647992747/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-7930434736343926869844093606042693000000000000)
      constant := (110239964676882265174198918415521509087585537920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190039416968838120193/50000000000000000000)
  centralHi := (380078833937676240387/100000000000000000000)
  directionLo := (76668274607796864271/20000000000000000000)
  directionHi := (95835343259746080339/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree060.table
  base := (1862712525111059950530453978109808418731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-40204978034517847616629978624154485000000000000)
      constant := (567143891299164566470971517019213663613708617219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree060.table
  base := (116362765893869813477232566210061090629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-40324978979408921408397600316037485000000000000)
      constant := (570524884119361835225897131145938702106576086736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76668274607796864271/20000000000000000000)
  centralHi := (95835343259746080339/25000000000000000000)
  directionLo := (193288189343919691331/50000000000000000000)
  directionHi := (386576378687839382663/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree061.table
  base := (9779253278148222737755951199064584633/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-40875783316458950112610983881780455000000000000)
      constant := (586687973584708807752012087146786853111456311552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree061.table
  base := (625665585824684002819649947913008487477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-40997784277098208467574732601861505000000000000)
      constant := (590182756561888508200561368852479630321320184692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193288189343919691331/50000000000000000000)
  centralHi := (386576378687839382663/100000000000000000000)
  directionLo := (389784536424155572449/100000000000000000000)
  directionHi := (7795690728483111449/2000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree062.table
  base := (1582138282711983309095082284911957827161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-41546588598400052608591989139406425000000000000)
      constant := (606562946889757269335424475251574234214623424578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree062.table
  base := (79088107855084112954270815389153479123/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-8334117914957499105350372977537105000000000000)
      constant := (122034678954569515834399676222644327422185257816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389784536424155572449/100000000000000000000)
  centralHi := (7795690728483111449/2000000000000000000)
  directionLo := (15718660152131742071/4000000000000000000)
  directionHi := (12280203243852923493/3125000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree063.table
  base := (3845023904498953975246361864664623568481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-42217393880341155104572994397032395000000000000)
      constant := (626768769907036942609029544288983034400061604969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree063.table
  base := (1922169539946933587343487200793134804907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-42343394872476782585928997173509545000000000000)
      constant := (630496758012864747908015318335076501614076564486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15718660152131742071/4000000000000000000)
  centralHi := (12280203243852923493/3125000000000000000)
  directionLo := (198061455984862176317/50000000000000000000)
  directionHi := (79224582393944870527/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree064.table
  base := (1136421219499212810890965880524363797839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-42888199162282257600553999654658365000000000000)
      constant := (647305405971091568170520540376023893544891650844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree064.table
  base := (4545061304989764794302440563793401468941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-43016200170166069645106129459333565000000000000)
      constant := (651152810129286186661797337064587684208005531509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198061455984862176317/50000000000000000000)
  centralHi := (79224582393944870527/20000000000000000000)
  directionLo := (399254367118712994699/100000000000000000000)
  directionHi := (3992543671187129947/1000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree065.table
  base := (5266218646992770330719437219176942535123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-43559004444223360096535004912284335000000000000)
      constant := (668172822514961332935482649319996271147691301227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree065.table
  base := (2632825365669524287006656732899253980971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-43689005467855356704283261745157585000000000000)
      constant := (672141519018288834165397766186534391875742685958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399254367118712994699/100000000000000000000)
  centralHi := (3992543671187129947/1000000000000000000)
  directionLo := (402361451855609691227/100000000000000000000)
  directionHi := (100590362963902422807/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree066.table
  base := (1201317782740405391939845652643455615803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-8845961945232892518503202033982061000000000000)
      constant := (137874198118602827642379089942014512537366486547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree066.table
  base := (3003035792896058320859795258710067812909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-44361810765544643763460394030981605000000000000)
      constant := (693462856152610313555512330735379014734672938282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402361451855609691227/100000000000000000000)
  centralHi := (100590362963902422807/25000000000000000000)
  directionLo := (202722363230690571701/50000000000000000000)
  directionHi := (405444726461381143403/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree067.table
  base := (6766763395602863624506843079199626950081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-44900615008105565088497015427536275000000000000)
      constant := (710899884461585290998359623486247573311715143369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree067.table
  base := (6766292059862543838436414514609864872293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-45034616063233930822637526316805625000000000000)
      constant := (715116796166604933575533715318610344632545180557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202722363230690571701/50000000000000000000)
  centralHi := (405444726461381143403/100000000000000000000)
  directionLo := (204252365036083634857/50000000000000000000)
  directionHi := (81700946014433453943/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree068.table
  base := (3773356681473720542074978416012384179551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-45571420290046667584478020685162245000000000000)
      constant := (732759481210166106639985082201096264503197530798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree068.table
  base := (3773141926114236366127016845083908940961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-45707421360923217881814658602629645000000000000)
      constant := (737103316491411880338242920299226606202120816978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204252365036083634857/50000000000000000000)
  centralHi := (81700946014433453943/20000000000000000000)
  directionLo := (20577099088994803289/5000000000000000000)
  directionHi := (411541981779896065781/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree069.table
  base := (1043301653966991951721784465365519086571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-46242225571987770080459025942788215000000000000)
      constant := (754949760436821509707210494119084455140535659032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree069.table
  base := (8346021766201893621871874115002643781169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-46380226658612504940991790888453665000000000000)
      constant := (759422397033957497195347504298047830780649437881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20577099088994803289/5000000000000000000)
  centralHi := (411541981779896065781/100000000000000000000)
  directionLo := (207278490830159683921/50000000000000000000)
  directionHi := (414556981660319367843/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree070.table
  base := (1833168041050128192592443411156784178457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-9382606170785774515288006240082837000000000000)
      constant := (155494140792466352413669321667355768886326356193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree070.table
  base := (114568541941382811149725625900363771857/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-9410606391260358400033784634855537000000000000)
      constant := (156414803978864997877979723872374022032057484688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207278490830159683921/50000000000000000000)
  centralHi := (414556981660319367843/100000000000000000000)
  directionLo := (417550211734234942667/100000000000000000000)
  directionHi := (104387552933558735667/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree071.table
  base := (10004973958133924727525016205080786510303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-47583836135869975072421036458040155000000000000)
      constant := (800322295578260745120305498692320513121854617047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree071.table
  base := (1250581076377564316088345588540159676209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-47725837253991079059346055460101705000000000000)
      constant := (805058169116728805932590999656124526849065526728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417550211734234942667/100000000000000000000)
  centralHi := (104387552933558735667/25000000000000000000)
  directionLo := (16820885474685070589/4000000000000000000)
  directionHi := (210261068433563382363/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree072.table
  base := (10863796357763928119848139278154730403431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-48254641417811077568402041715666125000000000000)
      constant := (823504520824767290194762742747541621605485647519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree072.table
  base := (5431749843695733582205050888900779172147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-48398642551680366118523187745925725000000000000)
      constant := (828374830469941863712589182018292734900098906006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16820885474685070589/4000000000000000000)
  centralHi := (210261068433563382363/50000000000000000000)
  directionLo := (84694641122395591301/20000000000000000000)
  directionHi := (211736602805988978253/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree073.table
  base := (2348458243670148015104983495522146602241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-9785089339950436012876609394658419000000000000)
      constant := (169403473358901883700663661375325661785810483209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree073.table
  base := (2348404131625214761790372575748073193183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-9814289569873930635540064006349949000000000000)
      constant := (170404798250710844045623609033822776719830590167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84694641122395591301/20000000000000000000)
  centralHi := (211736602805988978253/50000000000000000000)
  directionLo := (42640385099958304897/10000000000000000000)
  directionHi := (426403850999583048971/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree074.table
  base := (6320222041878496396308721841471781864181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-49596251981693282560364052230918065000000000000)
      constant := (870860821959454842229684608984240799451618548538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree074.table
  base := (12640197302047450141769019301211993061743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-49744253147058940236877452317573765000000000000)
      constant := (876005640126902590254628922426886427655093893607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42640385099958304897/10000000000000000000)
  centralHi := (426403850999583048971/100000000000000000000)
  directionLo := (429314491280302213449/100000000000000000000)
  directionHi := (8586289825606044269/2000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree075.table
  base := (6779121017776070109875380145835104567261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-50267057263634385056345057488544035000000000000)
      constant := (895034876017814040855738740505236616604115434378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree075.table
  base := (3389504228386272232305953475843992601379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-50417058444748227296054584603397785000000000000)
      constant := (900319766957910580409164617996606826723908328684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429314491280302213449/100000000000000000000)
  centralHi := (8586289825606044269/2000000000000000000)
  directionLo := (108051382655213726729/25000000000000000000)
  directionHi := (432205530620854906917/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree076.table
  base := (7247836761624612232893898907528247422391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-141102112314613538926110977136205000000000000)
      constant := (2547200885758068532681859657930454797112123438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree076.table
  base := (72477340674821108240676824773093368069/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (395792590167050400917769790772000000000000)
      linear := (-28304633652319952551374912404001000000000000)
      constant := (512446738332092938054118039292564530002576840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108051382655213726729/25000000000000000000)
  centralHi := (432205530620854906917/100000000000000000000)
  directionLo := (217538679879719788129/50000000000000000000)
  directionHi := (435077359759439576259/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree077.table
  base := (7726364107027732025800371354417634926541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-51608667827516590048307068003795975000000000000)
      constant := (944374744942125669759173401224151199609070387818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree077.table
  base := (15452540808294106353944276457260718304697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-51762669040126801414408849175045825000000000000)
      constant := (949945419220958600437237305427349450051362317953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217538679879719788129/50000000000000000000)
  centralHi := (435077359759439576259/100000000000000000000)
  directionLo := (437930356622185846853/100000000000000000000)
  directionHi := (218965178311092923427/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree078.table
  base := (821469842990054156426108831247766595283/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-10455894621891538508857614652284389000000000000)
      constant := (193908108838651817931612190108954517394567332268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree078.table
  base := (16429225843841369011170579830090355308939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-52435474337816088473585981460869845000000000000)
      constant := (975256929303936230726607886044299518750758096611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437930356622185846853/100000000000000000000)
  centralHi := (218965178311092923427/50000000000000000000)
  directionLo := (440764886903692611423/100000000000000000000)
  directionHi := (13773902715740394107/3125000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree079.table
  base := (17425671179000989851140204064732890997403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-52950278391398795040269078519047915000000000000)
      constant := (995036910908000994987782113821228454192988024947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree079.table
  base := (8712757551931277984798443173946211209603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-53108279635505375532763113746693865000000000000)
      constant := (1000900886448925264685882596352395076865773405494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440764886903692611423/100000000000000000000)
  centralHi := (13773902715740394107/3125000000000000000)
  directionLo := (443581304614176680291/100000000000000000000)
  directionHi := (110895326153544170073/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree080.table
  base := (9220771876128434755254499484204072203023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-53621083673339897536250083776673885000000000000)
      constant := (1020863839169759619082002751007989406348456976654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree080.table
  base := (9220700649690527437535477948694602389963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-53781084933194662591940246032517885000000000000)
      constant := (1026877284843338591769855086625542923962547208774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443581304614176680291/100000000000000000000)
  centralHi := (110895326153544170073/25000000000000000000)
  directionLo := (446379952595549551917/100000000000000000000)
  directionHi := (223189976297774775959/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree081.table
  base := (3895401585885577181555926855096127777533/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-10858377791056200006446217806859971000000000000)
      constant := (209404264735077360450957396813917283500065913317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree081.table
  base := (9738438949316198366538950540804772689467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-54453890230883949651117378318341905000000000000)
      constant := (1053186119278427167943318454423915807852885539366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446379952595549551917/100000000000000000000)
  centralHi := (223189976297774775959/50000000000000000000)
  directionLo := (449161163008552119037/100000000000000000000)
  directionHi := (224580581504276059519/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree082.table
  base := (821282309887629061416319694581959788303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-10992538847444420505642418858385165000000000000)
      constant := (214701871933887266454061252790590115756112195235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree082.table
  base := (20531939045772891905836585914024928990807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-55126695528573236710294510604165925000000000000)
      constant := (1079827385084454298748313770636192550598790051343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449161163008552119037/100000000000000000000)
  centralHi := (224580581504276059519/50000000000000000000)
  directionLo := (45192525779290671527/10000000000000000000)
  directionHi := (451925257792906715271/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree083.table
  base := (43213375711555717118394955799985500839/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-11126699903832641004838619909910359000000000000)
      constant := (220065588577148287967492669980857337765855971100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree083.table
  base := (21606579488653238333703462724316966474831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-55799500826262523769471642889989945000000000000)
      constant := (1106801078073098775406680347816225423098387506119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45192525779290671527/10000000000000000000)
  centralHi := (451925257792906715271/100000000000000000000)
  directionLo := (11366813727557275953/2500000000000000000)
  directionHi := (454672549102291038121/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree084.table
  base := (22700893453829767211542729171249033077057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-56304304801104307520174104807177765000000000000)
      constant := (1127477069495462781264346113832868095178266027593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree084.table
  base := (5675198628651085379458781407591363523069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-56472306123951810828648775175813965000000000000)
      constant := (1134107194486247341179410010786723551000431403924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11366813727557275953/2500000000000000000)
  centralHi := (454672549102291038121/100000000000000000000)
  directionLo := (228701669857898784871/50000000000000000000)
  directionHi := (457403339715797569743/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree085.table
  base := (11907335115212692655972222223205949772087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-56975110083045410016155110064803735000000000000)
      constant := (1154956736060860662448932568071888135379602012126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree085.table
  base := (23814579893309849333721840529998070985421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-57145111421641097887825907461637985000000000000)
      constant := (1161745730950438451381164596597643719209252991029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228701669857898784871/50000000000000000000)
  centralHi := (457403339715797569743/100000000000000000000)
  directionLo := (230058961713706874303/50000000000000000000)
  directionHi := (460117923427413748607/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree086.table
  base := (12474007156733642261384790004867018778429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-57645915364986512512136115322429705000000000000)
      constant := (1182766939494134861260805579543267831015678855242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree086.table
  base := (6236982956487802741205531825712676970633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-57817916719330384947003039747462005000000000000)
      constant := (1189716684436308051481843918468481689150217260868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230058961713706874303/50000000000000000000)
  centralHi := (460117923427413748607/100000000000000000000)
  directionLo := (462816585414941072029/100000000000000000000)
  directionHi := (46281658541494107203/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree087.table
  base := (13050461111848280291355862306041496428059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-58316720646927615008117120580055675000000000000)
      constant := (1210907677020753843755690611902797755570118442982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree087.table
  base := (26100846899908482069806048390793133306069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-58490722017019672006180172033286025000000000000)
      constant := (1218020052222465779486398759023444065861791417981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462816585414941072029/100000000000000000000)
  centralHi := (46281658541494107203/10000000000000000000)
  directionLo := (93099920517932883647/20000000000000000000)
  directionHi := (116374900647416104559/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree088.table
  base := (13636695416849253303966539678046311830969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-58987525928868717504098125837681645000000000000)
      constant := (1239378946146763879343778096257572176646588796162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree088.table
  base := (5454664409677081601087730278332099668873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-11832705462941791813071460863822009000000000000)
      constant := (249331166372659605785167209740875378548843104977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93099920517932883647/20000000000000000000)
  centralHi := (116374900647416104559/25000000000000000000)
  directionLo := (468167243927985174953/100000000000000000000)
  directionHi := (234083621963992587477/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree089.table
  base := (14232708665667846794105064556684194126203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-59658331210809820000079131095307615000000000000)
      constant := (1268180744629628787398294300691967995343492912294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree089.table
  base := (5693070902880415425812862133359760853723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-11967266522479649224906887320986813000000000000)
      constant := (255124804232050785248126340300272235433040552627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468167243927985174953/100000000000000000000)
  centralHi := (234083621963992587477/50000000000000000000)
  directionLo := (470819770786142364373/100000000000000000000)
  directionHi := (235409885393071182187/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree090.table
  base := (1187079967484452914170814440489446464117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-12065827298550184499212027270586717000000000000)
      constant := (259462614090440775063445305817796310466818187665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree090.table
  base := (23741553454931196594503642077646422599/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-12101827582017506636742313778151617000000000000)
      constant := (260984923627244511345233079486055870513787487750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470819770786142364373/100000000000000000000)
  centralHi := (235409885393071182187/50000000000000000000)
  directionLo := (473457437199064070521/100000000000000000000)
  directionHi := (236728718599532035261/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree091.table
  base := (482939595703497828151524404186850695487/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-60999941774692024992041141610559555000000000000)
      constant := (1326775921799493996288756476660657113616986410432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree091.table
  base := (3863510216359245842219327033060483118853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-61181943207776820242888701176582105000000000000)
      constant := (1334557621012655650844360631026869676121169647976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473457437199064070521/100000000000000000000)
  centralHi := (236728718599532035261/50000000000000000000)
  directionLo := (59510061270539549623/12500000000000000000)
  directionHi := (95216098032863279397/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree092.table
  base := (32158820096525038828101332492268252051439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-61670747056633127488022146868185525000000000000)
      constant := (1356569297037886381585707121964710360330167979111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree092.table
  base := (32158772244103673611197161355839319145699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-61854748505466107302065833462406125000000000000)
      constant := (1364523028189130229529219474750681619213418521851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59510061270539549623/12500000000000000000)
  centralHi := (95216098032863279397/20000000000000000000)
  directionLo := (478689169912048276459/100000000000000000000)
  directionHi := (23934458495602413823/5000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree093.table
  base := (16714527628619092007575445130133663543431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-62341552338574229984003152125811495000000000000)
      constant := (1386693194696584698244497900727698802218091015038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree093.table
  base := (33429011551886265573825946870888871110209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-62527553803155394361242965748230145000000000000)
      constant := (1394820838225081109085401285097318366877965056841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478689169912048276459/100000000000000000000)
  centralHi := (23934458495602413823/5000000000000000000)
  directionLo := (120320927540441787499/25000000000000000000)
  directionHi := (481283710161767149997/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree094.table
  base := (4339854743266667317420428385515894563823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (39710)
      previous := (19855)
      next := (19855)
      square := (323406801834099580650327963940000000000000)
      linear := (-28525286383212011081930356443385000000000000)
      constant := (641533550679494009628456528348932403500320824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree094.table
  base := (17359399013865138991240141229596114834269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (39710)
      previous := (19855)
      next := (19855)
      square := (323406801834099580650327963940000000000000)
      linear := (-28610393436326247813680442749685000000000000)
      constant := (645292462572867495484238213086243394910342218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120320927540441787499/25000000000000000000)
  centralHi := (481283710161767149997/100000000000000000000)
  directionLo := (483864338366722322299/100000000000000000000)
  directionHi := (4838643383667223223/1000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree095.table
  base := (1125880208340323803552351457508524011701/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-176407653469408407135637569642835000000000000)
      constant := (4010893496143767558972954502992937545339120288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree095.table
  base := (900703255169739392493009011701747690491/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4418000000000000000000000000000000000000000
      center := (48598)
      previous := (24299)
      next := (24299)
      square := (395792590167050400917769790772000000000000)
      linear := (-35386794680628237384818410149517000000000000)
      constant := (806877374967390420624845440669495785186356952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483864338366722322299/100000000000000000000)
  centralHi := (4838643383667223223/1000000000000000000)
  directionLo := (486431275946619220743/100000000000000000000)
  directionHi := (60803909493327402593/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree096.table
  base := (18678520035605913425699489627039459569527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-64353968184397537471946167898689405000000000000)
      constant := (1479048009592079728190554057841014899988519473246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree096.table
  base := (18678503384727129425815189240681095839663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-64545969696223255538774362605702205000000000000)
      constant := (1487708673150785749150338425479138918392486839374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486431275946619220743/100000000000000000000)
  centralHi := (60803909493327402593/12500000000000000000)
  directionLo := (122246184627334606587/25000000000000000000)
  directionHi := (488984738509338426349/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree097.table
  base := (1935272847193724836765262597029441759121/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-13004954693267727993585434631263075000000000000)
      constant := (302098796986892526035514114329400844705477129316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree097.table
  base := (19352713263327064745832101838050559600413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-65218774993912542597951494891526225000000000000)
      constant := (1519336082879179577009884160846065758905579492874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246184627334606587/25000000000000000000)
  centralHi := (488984738509338426349/100000000000000000000)
  directionLo := (491524936062287832221/100000000000000000000)
  directionHi := (245762468031143916111/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree098.table
  base := (8014683237866391535943618082130183992853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-13139115749655948492781635682788269000000000000)
      constant := (308454095452281280540611499395501754594916631997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree098.table
  base := (20036694203344913651997463014649407306419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-65891580291601829657128627177350245000000000000)
      constant := (1551295890146695609621987372938298755414193050262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491524936062287832221/100000000000000000000)
  centralHi := (245762468031143916111/50000000000000000000)
  directionLo := (49405207321397428259/10000000000000000000)
  directionHi := (494052073213974282591/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree099.table
  base := (41460916819701994307234364094579162882121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-66366384030220844959889183671567315000000000000)
      constant := (1574377485785125360996520084762863008861184509329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree099.table
  base := (10365222860856872382629106121858165970303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-66564385589291116716305759463174265000000000000)
      constant := (1583588094182891364264059093627827352879408628188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49405207321397428259/10000000000000000000)
  centralHi := (494052073213974282591/100000000000000000000)
  directionLo := (99313269873268449971/20000000000000000000)
  directionHi := (3879424604424548827/781250000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree100.table
  base := (42867957943990838004754221614728687633641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-67037189312161947455870188929193285000000000000)
      constant := (1606815009795097415271210471621815402224759381809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree100.table
  base := (8573586953142222487287477227835153663007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-13447438177396080755096578349799657000000000000)
      constant := (323242538858612871382758745044965365453411269143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99313269873268449971/20000000000000000000)
  centralHi := (3879424604424548827/781250000000000000)
  directionLo := (249533979449195621687/50000000000000000000)
  directionHi := (3992543671187129947/800000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree101.table
  base := (2768408672401426193046172552944795720047/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-67707994594103049951851194186819255000000000000)
      constant := (1639583048650352461513660243594498022934492161648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree101.table
  base := (692101837310359121101648521501036656463/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-67909996184669690834660024034822305000000000000)
      constant := (1649169689850676681598193387874134939062224824768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533979449195621687/50000000000000000000)
  centralHi := (3992543671187129947/800000000000000000)
  directionLo := (125389272835387615833/25000000000000000000)
  directionHi := (501557091341550463333/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree102.table
  base := (45740658537758456244871331040783072222271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-68378799876044152447832199444445225000000000000)
      constant := (1672681601772549000589248901856208392660577786679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree102.table
  base := (571757990014460942052350554251534179049/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-13716560296471795578767431264129265000000000000)
      constant := (336491816058111063287667351660728413872775136016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125389272835387615833/25000000000000000000)
  centralHi := (501557091341550463333/100000000000000000000)
  directionLo := (252016965773629245393/50000000000000000000)
  directionHi := (504033931547258490787/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree103.table
  base := (47206316627496854452913888012845282850157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-69049605157985254943813204702071195000000000000)
      constant := (1706110668639755948264982638311351102963574849493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree103.table
  base := (2950393685385084908868105040015759025773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-69255606780048264953014288606470345000000000000)
      constant := (1716080865102786308020452082267893664809498449232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252016965773629245393/50000000000000000000)
  centralHi := (504033931547258490787/100000000000000000000)
  directionLo := (253249329923583668197/50000000000000000000)
  directionHi := (101299731969433467279/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree104.table
  base := (48691512436869653608896989343045902834699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-69720410439926357439794209959697165000000000000)
      constant := (1739870248780865666544311125071334262169627882851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree104.table
  base := (24345748152930913607773383271358122441889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-69928412077737552012191420892294365000000000000)
      constant := (1750035043827229935750168071945267826766323882322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253249329923583668197/50000000000000000000)
  centralHi := (101299731969433467279/20000000000000000000)
  directionLo := (127237863051590942473/25000000000000000000)
  directionHi := (508951452206363769893/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree105.table
  base := (50196245432543848919255050844278383824711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-70391215721867459935775215217323135000000000000)
      constant := (1773960341770572284087610280591733940402631962239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree105.table
  base := (50196230699479761318532291363249887201217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-70601217375426839071368553178118385000000000000)
      constant := (1784321616048591889578873084292607996798723295433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127237863051590942473/25000000000000000000)
  centralHi := (508951452206363769893/100000000000000000000)
  directionLo := (31962030023123521969/6250000000000000000)
  directionHi := (102278496073995270301/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree106.table
  base := (25860257566479871901519259230609039425653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-71062021003808562431756220474949105000000000000)
      constant := (1808380947224856502416098463940685553261895118394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree106.table
  base := (51720501676916582886119158408264734259019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-71274022673116126130545685463942405000000000000)
      constant := (1818940581391992528607173460778708849070120442531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31962030023123521969/6250000000000000000)
  centralHi := (102278496073995270301/20000000000000000000)
  directionLo := (513821912003513831583/100000000000000000000)
  directionHi := (16056934750109807237/3125000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree107.table
  base := (26632160551619115312161630857686776943467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-71732826285749664927737225732575075000000000000)
      constant := (1843132064796924412024615613192246585173581631366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree107.table
  base := (26632154406878642750974511072708285179097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-71946827970805413189722817749766425000000000000)
      constant := (1853891939518982530383350655117148021115571447106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513821912003513831583/100000000000000000000)
  centralHi := (16056934750109807237/3125000000000000000)
  directionLo := (516239910827259436369/100000000000000000000)
  directionHi := (51623991082725943637/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree108.table
  base := (10965532590119728358761938772127047351423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-14480726313538153484743646198040209000000000000)
      constant := (375642738834710692464948472439063740783344919927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree108.table
  base := (10965530345355193805126822335480785031801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-14523926653698940049779990007118089000000000000)
      constant := (377835138024791756813270515958728670542824675649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516239910827259436369/100000000000000000000)
  centralHi := (51623991082725943637/10000000000000000000)
  directionLo := (5186466367450258883/1000000000000000000)
  directionHi := (518646636745025888301/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree109.table
  base := (56410540320234676994201973416538051569491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-73074436849631869919699236247827015000000000000)
      constant := (1913625835071803723934751459457146515186039028459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree109.table
  base := (56410530069891588618115984623352084283233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-73292438566183987308077082321414465000000000000)
      constant := (1924791832930939306530316918990008683759579872617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5186466367450258883/1000000000000000000)
  centralHi := (518646636745025888301/100000000000000000000)
  directionLo := (260521122983778851431/50000000000000000000)
  directionHi := (521042245967557702863/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree110.table
  base := (14503238222900370584189424658273333220387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-73745242131572972415680241505452985000000000000)
      constant := (1949368487236057023665919165444603307713057571052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree110.table
  base := (58012943530527719704478637587139150074631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-73965243863873274367254214607238485000000000000)
      constant := (1960740367690660340574401480714010003087864416319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260521122983778851431/50000000000000000000)
  centralHi := (521042245967557702863/100000000000000000000)
  directionLo := (523426891130850254277/100000000000000000000)
  directionHi := (261713445565425127139/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree111.table
  base := (59634900375071914029649748490807901822187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-74416047413514074911661246763078955000000000000)
      constant := (1985441650435350485328596734327815265500201200963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree111.table
  base := (59634891826335027648822215646541662889313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-74638049161562561426431346893062505000000000000)
      constant := (1997021294177962691642542561557775135029419762537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523426891130850254277/100000000000000000000)
  centralHi := (261713445565425127139/50000000000000000000)
  directionLo := (525800721409639212657/100000000000000000000)
  directionHi := (262900360704819606329/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree112.table
  base := (15319095627231108232706427031542808058423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-75086852695455177407642252020704925000000000000)
      constant := (2021845324460974529255493609926290782973525451708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree112.table
  base := (3829773418889967627868064747414700655281/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-75310854459251848485608479178886525000000000000)
      constant := (2033634612189437829262097827595896849965650850704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525800721409639212657/100000000000000000000)
  centralHi := (262900360704819606329/50000000000000000000)
  directionLo := (264081941313149568423/50000000000000000000)
  directionHi := (528163882626299136847/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree113.table
  base := (15734349764157252268962969773347650744753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-75757657977396279903623257278330895000000000000)
      constant := (2058579509124308519581502103848130900455010140388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree113.table
  base := (15734347981945807959706508221724316724969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-75983659756941135544785611464710545000000000000)
      constant := (2070580321541307370565630858489595896092039216324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081941313149568423/50000000000000000000)
  centralHi := (528163882626299136847/100000000000000000000)
  directionLo := (106103303471075235797/20000000000000000000)
  directionHi := (265258258677688089493/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree114.table
  base := (32308974902200460735247563727382903051903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-211713194624203275345164162149465000000000000)
      constant := (5805108599043961341646792237307065165683307454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree114.table
  base := (32308971647364256428987346475683287664129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (242990)
      previous := (121495)
      next := (121495)
      square := (1978962950835252004588848953860000000000000)
      linear := (-212344778544682611091309539475165000000000000)
      constant := (5838942997416931630896985158788893764900121922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106103303471075235797/20000000000000000000)
  centralHi := (265258258677688089493/50000000000000000000)
  directionLo := (532858765023966944449/100000000000000000000)
  directionHi := (10657175300479338889/2000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree115.table
  base := (66318034558995466229909958966238781228421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-77099268541278484895585267793582835000000000000)
      constant := (2133039409698556307646197136846019799851823098029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree115.table
  base := (66318028614898041373382580640407537993949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-77329270352319709663139876036358585000000000000)
      constant := (2145468913617990887093473339349162813265736636101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532858765023966944449/100000000000000000000)
  centralHi := (10657175300479338889/2000000000000000000)
  directionLo := (267595381004071743093/50000000000000000000)
  directionHi := (535190762008143486187/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree116.table
  base := (34018826572859688994788802122835415490999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-77770073823219587391566273051208805000000000000)
      constant := (2170765125316058339744947393257621603495763323102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree116.table
  base := (17009411929557024451074783584282867886209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-78002075650008996722317008322182605000000000000)
      constant := (2183411796057125932468665994957886124851957923364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267595381004071743093/50000000000000000000)
  centralHi := (535190762008143486187/100000000000000000000)
  directionLo := (107502528345122626603/20000000000000000000)
  directionHi := (67189080215701641627/12500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree117.table
  base := (69776805406637262903582783474450737002537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-78440879105160689887547278308834775000000000000)
      constant := (2208821350981430718743711472926584238271936128113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree117.table
  base := (558214403608103686925714058080022132437/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-15734976189539656756298828121601325000000000000)
      constant := (444337413852468996229275918496124358737243830325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107502528345122626603/20000000000000000000)
  centralHi := (67189080215701641627/12500000000000000000)
  directionLo := (539824534724791299739/100000000000000000000)
  directionHi := (26991226736239564987/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree118.table
  base := (35767745599476784810220120984397361195031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-79111684387101792383528283566460745000000000000)
      constant := (2247208086580801275012798810990579015075232551838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree118.table
  base := (2235483958572548339963057161088891825591/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-79347686245387570840671272893830645000000000000)
      constant := (2260294733122857579378030680330796717317622955488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539824534724791299739/100000000000000000000)
  centralHi := (26991226736239564987/5000000000000000000)
  directionLo := (542126568770455550247/100000000000000000000)
  directionHi := (67765821096306943781/12500000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree119.table
  base := (14662742078710523338181917975540342201697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-15956497933808578975901857764817343000000000000)
      constant := (457185066402241367499238821560662995348401070953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree119.table
  base := (73313706262569070665218859023553149820961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-80020491543076857899848405179654665000000000000)
      constant := (2299234787538516265807896541127964148271575528489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542126568770455550247/100000000000000000000)
  centralHi := (67765821096306943781/12500000000000000000)
  directionLo := (10888377378522798691/2000000000000000000)
  directionHi := (544418868926139934551/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree120.table
  base := (37555731436840488425533084395521356638197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-80453294950983997375490294081712685000000000000)
      constant := (2324973087179542502375707908440293170659547118906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree120.table
  base := (18777864775557074747181518696421130074749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-80693296840766144959025537465478685000000000000)
      constant := (2338507232418788861819009681142846035027914061204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10888377378522798691/2000000000000000000)
  centralHi := (544418868926139934551/100000000000000000000)
  directionLo := (54670155763341995231/10000000000000000000)
  directionHi := (546701557633419952311/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree121.table
  base := (76928748533758113505534889818520838856401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-81124100232925099871471299339338655000000000000)
      constant := (2364351352001613176323894943641035231925198121049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree121.table
  base := (9616093136333317197052038401432206294097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-81366102138455432018202669751302705000000000000)
      constant := (2378112067681831027996121791996322749316170868424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54670155763341995231/10000000000000000000)
  centralHi := (546701557633419952311/100000000000000000000)
  directionLo := (17155461087132198991/3125000000000000000)
  directionHi := (548974754788230367713/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree122.table
  base := (78765567278302592865097683077924427100381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-81794905514866202367452304596964625000000000000)
      constant := (2404060126401277285446977052796041353966771728069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree122.table
  base := (39382782067547949216653591829381768445141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-82038907436144719077379802037126725000000000000)
      constant := (2418049293253649155845522175607317108729618490618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17155461087132198991/3125000000000000000)
  centralHi := (548974754788230367713/100000000000000000000)
  directionLo := (110247715562870095119/20000000000000000000)
  directionHi := (137809644453587618899/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree123.table
  base := (80621919020962474621065091946889848742267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-82465710796807304863433309854590595000000000000)
      constant := (2444099410309673561297730137411264282989672076883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree123.table
  base := (3224876646065026131079478879342829700303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-16542342546766801227311386864590149000000000000)
      constant := (491663781813468933597825975717860677508384635235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110247715562870095119/20000000000000000000)
  centralHi := (137809644453587618899/25000000000000000000)
  directionLo := (69186642716773032709/12500000000000000000)
  directionHi := (553493141734184261673/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree124.table
  base := (16499560736727926156999482450326660636081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-16627303215749681471882863022443313000000000000)
      constant := (496893840732904545961980188766604860197582157369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree124.table
  base := (41248900532203303633728174337641779089013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-83384518031523293195734066608774765000000000000)
      constant := (2498920915062431699850982280408080548185508655674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69186642716773032709/12500000000000000000)
  centralHi := (553493141734184261673/100000000000000000000)
  directionLo := (555738559236956178101/100000000000000000000)
  directionHi := (277869279618478089051/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree125.table
  base := (84393221195698770611922760836118508044703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-83807321360689509855395320369842535000000000000)
      constant := (2525169506409496749014202388810423430621740362647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree125.table
  base := (84393218804858438828872841428834953038867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-84057323329212580254911198894598785000000000000)
      constant := (2539855311184220942570745377366445191965891450283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555738559236956178101/100000000000000000000)
  centralHi := (277869279618478089051/50000000000000000000)
  directionLo := (69746867593054617487/12500000000000000000)
  directionHi := (557974940744436939897/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree126.table
  base := (86308171493252871998918486256665658856743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-84478126642630612351376325627468505000000000000)
      constant := (2566200318493648977021680906872350655489650848607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree126.table
  base := (67428257274196764628608905463560149131/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 1594898000000000000000000000000000000000000000
      center := (17543878)
      previous := (8771939)
      next := (8771939)
      square := (142881125050305194731314894468692000000000000)
      linear := (-16946025725380373462817666236084561000000000000)
      constant := (516224419476652630091193627712288786805277905664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69746867593054617487/12500000000000000000)
  centralHi := (557974940744436939897/100000000000000000000)
  directionLo := (56020239447430781007/10000000000000000000)
  directionHi := (560202394474307810071/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree127.table
  base := (88242654518517547648859761471177022313527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-85148931924571714847357330885094475000000000000)
      constant := (2607561639870899311966631601818912180266899792623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree127.table
  base := (44121326263339127871356048819041119194669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-85402933924591154373265463466246825000000000000)
      constant := (2622721273614846465564265195997900015421339198762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56020239447430781007/10000000000000000000)
  centralHi := (560202394474307810071/100000000000000000000)
  directionLo := (562421026501266256603/100000000000000000000)
  directionHi := (140605256625316564151/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree128.table
  base := (45098335109613808806131633004857277885687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-85819737206512817343338336142720445000000000000)
      constant := (2649253470499568938363518949224676382785326424926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree128.table
  base := (90196668401280227239144757194164738421851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-86075739222280441432442595752070845000000000000)
      constant := (2664652839838542294854576465306347396489766658099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell031.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562421026501266256603/100000000000000000000)
  centralHi := (140605256625316564151/25000000000000000000)
  directionLo := (282315470407985304337/50000000000000000000)
  directionHi := (22585237632638824347/4000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1677
  qDenominator := 3572
  table := BinomialMassData.Q1677_3572.Degree129.table
  base := (92170218548109827472557557004097051178329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-86490542488453919839319341400346415000000000000)
      constant := (2691275810341959846751102468545855026865107282721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1677_3572.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 841
  qDenominator := 1786
  table := BinomialMassData.Q841_1786.Degree129.table
  base := (5760638555558565572097869040103372940791/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7974490000000000000000000000000000000000000000
      center := (87719390)
      previous := (43859695)
      next := (43859695)
      square := (714405625251525973656574472343460000000000000)
      linear := (-86748544519969728491619728037894865000000000000)
      constant := (2706916796017794998765698724678499551872173474544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q841_1786.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell031.Kernel129
