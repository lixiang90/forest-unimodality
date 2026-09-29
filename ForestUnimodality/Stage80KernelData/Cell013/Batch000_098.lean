import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell013.Parameters
import ForestUnimodality.BinomialMassData.Q89_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q89_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q91_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q91_255.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree000.table
  base := (202238878554974635143093309/25000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3818)
      previous := (2047)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (206224364306711175492958786350000000000000)
      constant := (20628365612607412784595517518000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree000.table
  base := (202238878554974635143093309/25000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3772)
      previous := (2093)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (206224364306711175492958786350000000000000)
      constant := (20628365612607412784595517518000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree001.table
  base := (54988808305870626113908701637206766628219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (2373312652608509753793253313130000000000000)
      constant := (237350518732854632092797268286279333333329365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree001.table
  base := (6801779176105834589389168563268492887351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (2347863179785912445263207334370000000000000)
      constant := (234841222139226813714905465558639333333332680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (47666017369207587121/100000000000000000000)
  directionHi := (23833008684603793561/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree002.table
  base := (7460680655620485664367657659587727797001/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (1240811112002929524206207258310000000000000)
      constant := (160053587907968870947030944125535999999996675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree002.table
  base := (182639403409672793060239001319907727797/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (1189912166357734907146115300790000000000000)
      constant := (156672632957280287798764846556691999999999000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47666017369207587121/100000000000000000000)
  centralHi := (23833008684603793561/50000000000000000000)
  directionLo := (67409928227844885977/100000000000000000000)
  directionHi := (33704964113922442989/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree003.table
  base := (157282384360334845261534667943165094917/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (108309571397349294619161203490000000000000)
      constant := (107198961703796377521977198680331309834431200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree003.table
  base := (2437689082449074272830592491112431741437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (31961152929557369029023267210000000000000)
      constant := (103780071391819887909151782373255915991293950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67409928227844885977/100000000000000000000)
  centralHi := (33704964113922442989/50000000000000000000)
  directionLo := (41279981938964066589/50000000000000000000)
  directionHi := (82559963877928133179/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree004.table
  base := (8386434812158883058701319072863911831513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-1024191969208230934967884851330000000000000)
      constant := (70978120190542838038087848973658115579217710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree004.table
  base := (8028495119361914715361798570475883503521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-1125989860498620169088068766370000000000000)
      constant := (67908511396419896636299789804113909975527070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41279981938964066589/50000000000000000000)
  centralHi := (82559963877928133179/100000000000000000000)
  directionLo := (95332034738415174243/100000000000000000000)
  directionHi := (23833008684603793561/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree005.table
  base := (2181204101830996584809153684204877524917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-2156693509813811164554930906150000000000000)
      constant := (46100424977553274359312349310040720352575975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree005.table
  base := (5146350799159099202735167420670891060453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-2283940873926797707205160799950000000000000)
      constant := (43528758761502099919753728893216625494127510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95332034738415174243/100000000000000000000)
  centralHi := (23833008684603793561/25000000000000000000)
  directionLo := (53292227527116927889/50000000000000000000)
  directionHi := (106584455054233855779/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree006.table
  base := (3376810442511636539230603366754794917889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-3289195050419391394141976960970000000000000)
      constant := (29050133551767322036985675963632071938097630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree006.table
  base := (6245334682088865776694471318725743612647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-3441891887354975245322252833530000000000000)
      constant := (27005091378229592657696624523944098560824745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/50000000000000000000)
  centralHi := (106584455054233855779/100000000000000000000)
  directionLo := (58378710312599396077/50000000000000000000)
  directionHi := (23351484125039758431/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree007.table
  base := (753976187410700035405516552975899210187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-4421696591024971623729023015790000000000000)
      constant := (17461247065727274761409188604584615380803225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree007.table
  base := (839149697893378251910041910434769898637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-4599842900783152783439344867110000000000000)
      constant := (15917319068768223993291914928830910042365580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58378710312599396077/50000000000000000000)
  centralHi := (23351484125039758431/20000000000000000000)
  directionLo := (63056213973904260433/50000000000000000000)
  directionHi := (126112427947808520867/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree008.table
  base := (1587109347817006518888226221612172944171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-5554198131630551853316069070610000000000000)
      constant := (9739823658379901399369221510480769712981285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree008.table
  base := (1254396979861623060902131664729357668801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-5757793914211330321556436900690000000000000)
      constant := (8652401568260902569387658656473765494252335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63056213973904260433/50000000000000000000)
  centralHi := (126112427947808520867/100000000000000000000)
  directionLo := (67409928227844885977/50000000000000000000)
  directionHi := (26963971291137954391/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree009.table
  base := (-21434787703863263319419791999417334123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-6686699672236132082903115125430000000000000)
      constant := (4810021701777418686859405740113051713153590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree009.table
  base := (-3097910989883751872740462064724866871/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-6915744927639507859673528934270000000000000)
      constant := (4133003177050917564508490116149770211421500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67409928227844885977/50000000000000000000)
  centralHi := (26963971291137954391/20000000000000000000)
  directionLo := (35749513026905690341/25000000000000000000)
  directionHi := (28599610421524552273/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree010.table
  base := (-1287986686968392807698420796099558430877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-7819201212841712312490161180250000000000000)
      constant := (1943860942322573792172006658608414202148205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree010.table
  base := (-751207808017026867813267327463316990497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-8073695941067685397790620967850000000000000)
      constant := (1637562403603694364124448066793041692391010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35749513026905690341/25000000000000000000)
  centralHi := (28599610421524552273/20000000000000000000)
  directionLo := (7536659093792154841/5000000000000000000)
  directionHi := (150733181875843096821/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree011.table
  base := (-1131120590692818225858501900544941710937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-8951702753447292542077207235070000000000000)
      constant := (647154871768374422913205780923355366176210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree011.table
  base := (-1217680056890508752356220083912681507013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-9231646954495862935907713001430000000000000)
      constant := (681064091157435637620475886425051334197290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7536659093792154841/5000000000000000000)
  centralHi := (150733181875843096821/100000000000000000000)
  directionLo := (39522573716056240371/25000000000000000000)
  directionHi := (31618058972844992297/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree012.table
  base := (-3043335062840004711952201674478234849403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-10084204294052872771664253289890000000000000)
      constant := (583065301992148236211250424728851927837995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree012.table
  base := (-3184171286601010235332922102594715169473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-10389597967924040474024805035010000000000000)
      constant := (936013319610632268623547760603909740334545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39522573716056240371/25000000000000000000)
  centralHi := (31618058972844992297/20000000000000000000)
  directionLo := (165119927755856266357/100000000000000000000)
  directionHi := (82559963877928133179/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree013.table
  base := (-736899441674754361231737012228239706981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-11216705834658453001251299344710000000000000)
      constant := (1520845051015636498099643344484904351186825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree013.table
  base := (-3800148990878258936445022509198529039871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-11547548981352218012141897068590000000000000)
      constant := (2180025211537660173304886402736376612159215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165119927755856266357/100000000000000000000)
  centralHi := (82559963877928133179/50000000000000000000)
  directionLo := (171862269721835083191/100000000000000000000)
  directionHi := (21482783715229385399/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree014.table
  base := (-21112086561724510965440022531124172661/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-12349207375264033230838345399530000000000000)
      constant := (3301444293797063279890412926983342302913000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree014.table
  base := (-107959277334551766020621365667331120193/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-12705499994780395550258989102170000000000000)
      constant := (4261037214493573364580040921512783758533800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171862269721835083191/100000000000000000000)
  centralHi := (21482783715229385399/12500000000000000000)
  directionLo := (11146869124224410053/6250000000000000000)
  directionHi := (178349905987590560849/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree015.table
  base := (-4682574802368430607749734111718343126449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-13481708915869613460425391454350000000000000)
      constant := (5814409711625253005317055440100982546843585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree015.table
  base := (-4763026032176288433539405322819600676183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-13863451008208573088376081135750000000000000)
      constant := (7074192449471612068683623245277031068746695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11146869124224410053/6250000000000000000)
  centralHi := (178349905987590560849/100000000000000000000)
  directionLo := (18460969145097445499/10000000000000000000)
  directionHi := (184609691450974454991/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree016.table
  base := (-1270705663659795913405773626952662371221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-14614210456475193690012437509170000000000000)
      constant := (8982348652695632348297149451968834483027860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree016.table
  base := (-2575480775315662662366731003835360621639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-15021402021636750626493173169330000000000000)
      constant := (10546455948961035886637979951275423410389870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18460969145097445499/10000000000000000000)
  centralHi := (184609691450974454991/100000000000000000000)
  directionLo := (95332034738415174243/50000000000000000000)
  directionHi := (190664069476830348487/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree017.table
  base := (-1087160314083978308282310247559357287177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3818)
      previous := (2047)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-926277176298869054094087268470000000000000)
      constant := (750027275119662696790068931317819458849325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree017.table
  base := (-5494050812691786462912686560414708448983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3772)
      previous := (2093)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-951726649121466362624133247230000000000000)
      constant := (860373973368351852921827458430249345509335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95332034738415174243/50000000000000000000)
  centralHi := (190664069476830348487/100000000000000000000)
  directionLo := (196532024365768922749/100000000000000000000)
  directionHi := (786128097463075691/400000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree018.table
  base := (-2875284836705443028976982469419374445407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-16879213537686354149186529618810000000000000)
      constant := (17079487818400215200772661719306023558321310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree018.table
  base := (-1160154770640429052473193036359365967143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-17337304048493105702727357236490000000000000)
      constant := (19277136293323656656840562091162742662175475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196532024365768922749/100000000000000000000)
  centralHi := (786128097463075691/400000000000000000)
  directionLo := (202229784683534657931/100000000000000000000)
  directionHi := (50557446170883664483/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree019.table
  base := (-6033705582715248916510777187768984151719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-18011715078291934378773575673630000000000000)
      constant := (21940902762981621187337604877109453702298135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree019.table
  base := (-303863892949417304678262733063629747681/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-18495255061921283240844449270070000000000000)
      constant := (24472144132255592512150533162531300876057300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202229784683534657931/100000000000000000000)
  centralHi := (50557446170883664483/25000000000000000000)
  directionLo := (12985709547089396699/6250000000000000000)
  directionHi := (41554270550686069437/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree020.table
  base := (-3145028774832436933730096414594242681663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-19144216618897514608360621728450000000000000)
      constant := (27313691341254724397236483304467915949981790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree020.table
  base := (-6328090821749795480383519384860681293013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-19653206075349460778961541303650000000000000)
      constant := (30191752220040861784611679394028946594788645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12985709547089396699/6250000000000000000)
  centralHi := (41554270550686069437/20000000000000000000)
  directionLo := (53292227527116927889/25000000000000000000)
  directionHi := (213168910108467711557/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree021.table
  base := (-6523254364622746928103779817262452900223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-20276718159503094837947667783270000000000000)
      constant := (33182122746995980445466999920075266677533295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree021.table
  base := (-131132084897090926617696015203256414821/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-20811157088777638317078633337230000000000000)
      constant := (36421258389578955117766381283702172087548250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/25000000000000000000)
  centralHi := (213168910108467711557/100000000000000000000)
  directionLo := (10921656633573679957/5000000000000000000)
  directionHi := (218433132671473599141/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree022.table
  base := (-210501737765149801970589167355266871639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-21409219700108675067534713838090000000000000)
      constant := (39534234197021552009413093317289379566237920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree022.table
  base := (-6765401632451598848842336316305740235221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-21969108102205815855195725370810000000000000)
      constant := (43149463150383956628257654142786616080316965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10921656633573679957/5000000000000000000)
  centralHi := (218433132671473599141/100000000000000000000)
  directionLo := (223573439076548595427/100000000000000000000)
  directionHi := (55893359769137148857/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree023.table
  base := (-3465296650351345164092779329395742701107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-22541721240714255297121759892910000000000000)
      constant := (46360783387008422519921033987850910781402310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree023.table
  base := (-6956483701695604856390883966355014080173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-23127059115633993393312817404390000000000000)
      constant := (50367693393590450667131322418143013962450045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223573439076548595427/100000000000000000000)
  centralHi := (55893359769137148857/25000000000000000000)
  directionLo := (4571963773800347419/2000000000000000000)
  directionHi := (228598188690017370951/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree024.table
  base := (-7108539906615668473574188888650848706201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-23674222781319835526708805947730000000000000)
      constant := (53654520179711023207349401078306570858618665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree024.table
  base := (-891428022574155751667936465850985670051/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-24285010129062170931429909437970000000000000)
      constant := (58069127008289472239097822958255816962631320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4571963773800347419/2000000000000000000)
  centralHi := (228598188690017370951/100000000000000000000)
  directionLo := (233514841250397584309/100000000000000000000)
  directionHi := (23351484125039758431/10000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree025.table
  base := (-7271226219909084852989576239184000646483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-24806724321925415756295852002550000000000000)
      constant := (61409675584503332544127647026637357197496195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree025.table
  base := (-7291478737728390321293667727432989559333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-25442961142490348469547001471550000000000000)
      constant := (66248320671169953557249298020577990260291445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233514841250397584309/100000000000000000000)
  centralHi := (23351484125039758431/10000000000000000000)
  directionLo := (29791260855754741951/12500000000000000000)
  directionHi := (238330086846037935609/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree026.table
  base := (-92746562050623422750496161411436117587/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-25939225862530995985882898057370000000000000)
      constant := (69621599345156190107365212334901954420828400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree026.table
  base := (-7437662086751150531122598857822629902819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-26600912155918526007664093505130000000000000)
      constant := (74900875598558655846515802438726899371279635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29791260855754741951/12500000000000000000)
  centralHi := (238330086846037935609/100000000000000000000)
  directionLo := (48609990540168420817/20000000000000000000)
  directionHi := (121524976350421052043/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree027.table
  base := (-1510982162182544687221206372594680838459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-27071727403136576215469944112190000000000000)
      constant := (78286499759092823150973325051282292826401175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree027.table
  base := (-946350416112717655218058727182184125539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-27758863169346703545781185538710000000000000)
      constant := (84023197636579248820604345540453854526307480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48609990540168420817/20000000000000000000)
  centralHi := (121524976350421052043/50000000000000000000)
  directionLo := (15479993227111524971/6250000000000000000)
  directionHi := (247679891633784399537/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree028.table
  base := (-7677504060351831726546150834728941941519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-28204228943742156445056990167010000000000000)
      constant := (87401254326445283235026972349602036683515135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree028.table
  base := (-7691586288310486682371610859638461674641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-28916814182774881083898277572290000000000000)
      constant := (93612322407626776945879475677699268640431265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15479993227111524971/6250000000000000000)
  centralHi := (247679891633784399537/100000000000000000000)
  directionLo := (252224855895617041733/100000000000000000000)
  directionHi := (126112427947808520867/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree029.table
  base := (-7788102902555999976937412384058841599427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-29336730484347736674644036221830000000000000)
      constant := (96963269892745116786548287550132921666483955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree029.table
  base := (-7800579393306354968843555902146195503177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-30074765196203058622015369605870000000000000)
      constant := (103665785774895163440176813316884242493727705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252224855895617041733/100000000000000000000)
  centralHi := (126112427947808520867/50000000000000000000)
  directionLo := (128344679616459347567/50000000000000000000)
  directionHi := (51337871846583739027/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree030.table
  base := (-492950476370321085875502678970870894351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-30469232024953316904231082276650000000000000)
      constant := (106970377725118717481070409414480394767814640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree030.table
  base := (-246820568414614430410469805059750160553/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-31232716209631236160132461639450000000000000)
      constant := (114181526249169409865485909036611457728087840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128344679616459347567/50000000000000000000)
  centralHi := (51337871846583739027/20000000000000000000)
  directionLo := (65269382348870123551/25000000000000000000)
  directionHi := (52215505879096098841/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree031.table
  base := (-3987619523427939600138984874500651621983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-31601733565558897133818128331470000000000000)
      constant := (117420753532466671368869452334847350437407390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree031.table
  base := (-7985022587666418611503956401013340273559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-32390667223059413698249553673030000000000000)
      constant := (125157810214218346298828714481275169914121735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65269382348870123551/25000000000000000000)
  centralHi := (52215505879096098841/20000000000000000000)
  directionLo := (33174144103288854889/12500000000000000000)
  directionHi := (265393152826310839113/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree032.table
  base := (-8052552836853089242873545969325580233539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-32734235106164477363405174386290000000000000)
      constant := (128312855530835393932752676364605609687608435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree032.table
  base := (-8061210298376029077743539349044344633541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-33548618236487591236366645706610000000000000)
      constant := (136593173697740768161111640330084766013599765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33174144103288854889/12500000000000000000)
  centralHi := (265393152826310839113/100000000000000000000)
  directionLo := (269639712911379543909/100000000000000000000)
  directionHi := (26963971291137954391/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree033.table
  base := (-8119450714734035926096306301045153255127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-33866736646770057592992220441110000000000000)
      constant := (139645375751812026553372928247461260639024455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree033.table
  base := (-4063553724865860974357569581843951503429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-34706569249915768774483737740190000000000000)
      constant := (148486376333403458704640705905484940465270570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269639712911379543909/100000000000000000000)
  centralHi := (26963971291137954391/10000000000000000000)
  directionLo := (68455105722095694761/25000000000000000000)
  directionHi := (54764084577676555809/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree034.table
  base := (-1022023677787906547082693856479433395667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3818)
      previous := (2047)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-2058778716904449283681133323290000000000000)
      constant := (8906894189392583419201140118625955872839320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree034.table
  base := (-4091478550742741987599974205418348839089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3772)
      previous := (2093)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-2109677662549643900741225280810000000000000)
      constant := (9460962615128326786163496554960642092064610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68455105722095694761/25000000000000000000)
  centralHi := (54764084577676555809/20000000000000000000)
  directionLo := (69484563574677496083/25000000000000000000)
  directionHi := (277938254298709984333/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree035.table
  base := (-513936747027630906531407501115330954479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-36131739727981218052166312550750000000000000)
      constant := (163627382600280390782331440554840644997336560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree035.table
  base := (-8228966152086291582873577648651008669313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-37022471276772123850717921807350000000000000)
      constant := (173642241164298745336224075146997877418528145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69484563574677496083/25000000000000000000)
  centralHi := (277938254298709984333/100000000000000000000)
  directionLo := (56399192339768830583/20000000000000000000)
  directionHi := (70498990424711038229/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree036.table
  base := (-8260033455335944229976280391577672111127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-37264241268586798281753358605570000000000000)
      constant := (176275108597577813896361220183558791398264455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree036.table
  base := (-826531100204648467490267997472914975537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-38180422290200301388835013840930000000000000)
      constant := (186903241758534035138747165865397135810471050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56399192339768830583/20000000000000000000)
  centralHi := (70498990424711038229/25000000000000000000)
  directionLo := (285996104215245522729/100000000000000000000)
  directionHi := (28599610421524552273/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree037.table
  base := (-8287486108900154187079457200549097388449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-38396742809192378511340404660390000000000000)
      constant := (189359684840303133800133350541511662821073585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree037.table
  base := (-4146071119262824570298727544572543228427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-39338373303628478926952105874510000000000000)
      constant := (200618713444550619942188997889708050209537910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285996104215245522729/100000000000000000000)
  centralHi := (28599610421524552273/10000000000000000000)
  directionLo := (28994106442196003161/10000000000000000000)
  directionHi := (289941064421960031611/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree038.table
  base := (-1661096633626947717495663300281157182953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-39529244349797958740927450715210000000000000)
      constant := (202880516328031288886074568273137918059493725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree038.table
  base := (-8309588538693389942370537750093566282909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-40496324317056656465069197908090000000000000)
      constant := (214788098406818262234490799543156390163589485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28994106442196003161/10000000000000000000)
  centralHi := (289941064421960031611/100000000000000000000)
  directionLo := (58766612987301140401/20000000000000000000)
  directionHi := (146916532468252851003/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree039.table
  base := (-8314142354884005447683625622857648967167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-40661745890403538970514496770030000000000000)
      constant := (216837092736567203902610697008480091727331055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree039.table
  base := (-8317759941594695745655090561251198835859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-41654275330484834003186289941670000000000000)
      constant := (229410919626076936150999810938804053046551235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58766612987301140401/20000000000000000000)
  centralHi := (146916532468252851003/50000000000000000000)
  directionLo := (14883709153116233211/5000000000000000000)
  directionHi := (297674183062324664221/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree040.table
  base := (-4156782355691431314436791867509967696623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-41794247431009119200101542824850000000000000)
      constant := (231228976047822553271534243345088580070278590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree040.table
  base := (-4158375301948571700487294712890283070601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-42812226343913011541303381975250000000000000)
      constant := (244486768933172696044696764036441245777889330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14883709153116233211/5000000000000000000)
  centralHi := (297674183062324664221/100000000000000000000)
  directionLo := (301466363751686193641/100000000000000000000)
  directionHi := (150733181875843096821/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree041.table
  base := (-8303837013356802395295383349766240108811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-42926748971614699429688588879670000000000000)
      constant := (246055790089027328027333627743991349128304315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree041.table
  base := (-4153320564930215694039680191850655974911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-43970177357341189079420474008830000000000000)
      constant := (260015296908639749005863995452582812697521630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301466363751686193641/100000000000000000000)
  centralHi := (150733181875843096821/50000000000000000000)
  directionLo := (305211431118668251591/100000000000000000000)
  directionHi := (38151428889833531449/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree042.table
  base := (-2071258454532924305371718615758514952733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-44059250512220279659275634934490000000000000)
      constant := (261317211654173870992887270472799350719609780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree042.table
  base := (-8287500547313077098695593240030233296339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-45128128370769366617537566042410000000000000)
      constant := (275996204316841472141368472382480938660370435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305211431118668251591/100000000000000000000)
  centralHi := (38151428889833531449/12500000000000000000)
  directionLo := (154455549347819787361/50000000000000000000)
  directionHi := (308911098695639574723/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree043.table
  base := (-8257219208038335171170900028426844024589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-45191752052825859888862680989310000000000000)
      constant := (277012962946358215911956647327641631153406685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree043.table
  base := (-4129693993717928759137181905517577662183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-46286079384197544155654658075990000000000000)
      constant := (292429234824109197219279781162614601668873390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154455549347819787361/50000000000000000000)
  centralHi := (308911098695639574723/100000000000000000000)
  directionLo := (78141744649222532871/25000000000000000000)
  directionHi := (62513395719378026297/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree044.table
  base := (-164408965557656220285646646151575725561/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-46324253593431440118449727044130000000000000)
      constant := (293142805129595941956874087054333961484653250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree044.table
  base := (-328894164617281513013325343031866170959/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-47444030397625721693771750109570000000000000)
      constant := (309314168796786769690724726281169503722318375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78141744649222532871/25000000000000000000)
  centralHi := (62513395719378026297/20000000000000000000)
  directionLo := (316180589728449922969/100000000000000000000)
  directionHi := (31618058972844992297/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree045.table
  base := (-1021846050796988410510605812878212090757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-47456755134037020348036773098950000000000000)
      constant := (309706532817175806845941557649883604692547240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree045.table
  base := (-4088221175406763107269786833685292710453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-48601981411053899231888842143150000000000000)
      constant := (326650818011290067531818953376348512200372490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316180589728449922969/100000000000000000000)
  centralHi := (31618058972844992297/10000000000000000000)
  directionLo := (159876682581350783667/50000000000000000000)
  directionHi := (63950673032540313467/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree046.table
  base := (-4060110172231538879054953799703237970947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-48589256674642600577623819153770000000000000)
      constant := (326703969353749268453560158405880926791889510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree046.table
  base := (-8121689909427030901658520057335634665479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-49759932424482076770005934176730000000000000)
      constant := (344439021136923610627221898511358023725148535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159876682581350783667/50000000000000000000)
  centralHi := (63950673032540313467/20000000000000000000)
  directionLo := (161643329389673216189/50000000000000000000)
  directionHi := (323286658779346432379/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree047.table
  base := (-4028419573987277004655343010685548987661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-49721758215248180807210865208590000000000000)
      constant := (344134962772292272910977895531468290276979130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree047.table
  base := (-8058128694047817677941903610877248440123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-50917883437910254308123026210310000000000000)
      constant := (362678639875156621771856441385619128012066795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161643329389673216189/50000000000000000000)
  centralHi := (323286658779346432379/100000000000000000000)
  directionLo := (32678175126000406923/10000000000000000000)
  directionHi := (326781751260004069231/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree048.table
  base := (-3992327488785249362900767175094994090799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-50854259755853761036797911263410000000000000)
      constant := (361999382326343014965219050586838401232772670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree048.table
  base := (-7985786056069767593938407623191361377449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-52075834451338431846240118243890000000000000)
      constant := (381369555657696626611594039914457448428758585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32678175126000406923/10000000000000000000)
  centralHi := (326781751260004069231/100000000000000000000)
  directionLo := (66047971102342506543/20000000000000000000)
  directionHi := (82559963877928133179/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree049.table
  base := (-3951846892668403437118288260962200584959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-51986761296459341266384957318230000000000000)
      constant := (380297115513609139935837996309165720928405470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree049.table
  base := (-3952342723647337262177936845121700695781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-53233785464766609384357210277470000000000000)
      constant := (400511666820982848699576200779362854967578730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66047971102342506543/20000000000000000000)
  centralHi := (82559963877928133179/25000000000000000000)
  directionLo := (333662121584453109851/100000000000000000000)
  directionHi := (83415530396113277463/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree050.table
  base := (-1953494476102473170386387033292096496763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-53119262837064921495972003373050000000000000)
      constant := (399028065519944292149094328887215046746129580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree050.table
  base := (-3907423488953278482376755627934211607363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-54391736478194786922474302311050000000000000)
      constant := (420104886187367567857553751041310385364162790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333662121584453109851/100000000000000000000)
  centralHi := (83415530396113277463/25000000000000000000)
  directionLo := (168524820569612214943/50000000000000000000)
  directionHi := (337049641139224429887/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree051.table
  base := (-1543105311107707433475684359510350694761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3818)
      previous := (2047)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-3191280257510029513268179378110000000000000)
      constant := (24599538177847206228517965708288302864179725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree051.table
  base := (-1929071973571382962964784604245366727461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3772)
      previous := (2093)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-3267628675977821438858317314390000000000000)
      constant := (25891125823164292774400682308833725937989780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168524820569612214943/50000000000000000000)
  centralHi := (337049641139224429887/100000000000000000000)
  directionLo := (340403451515876331937/100000000000000000000)
  directionHi := (170201725757938165969/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree052.table
  base := (-3804178141213242914341078698734883873409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-55384265918276081955146095482690000000000000)
      constant := (437789294307028044413706189680040556817543970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree052.table
  base := (-3804511494138758577401646051811084814161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-56707638505051141998708486378210000000000000)
      constant := (460644361117607022225168867814229894661224130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340403451515876331937/100000000000000000000)
  centralHi := (170201725757938165969/50000000000000000000)
  directionLo := (171862269721835083191/50000000000000000000)
  directionHi := (343724539443670166383/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree053.table
  base := (-936560165745506270429029442965249848091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-56516767458881662184733141537510000000000000)
      constant := (457819439636561407392072938356817135268204120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree053.table
  base := (-187326623695475060157478098747178212187/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-57865589518479319536825578411790000000000000)
      constant := (481590497556605020914314044399671298006774200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171862269721835083191/50000000000000000000)
  centralHi := (343724539443670166383/100000000000000000000)
  directionLo := (8675346110804627697/2500000000000000000)
  directionHi := (347013844432185107881/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree054.table
  base := (-1473582789198204265849321417483722312313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-57649268999487242414320187592330000000000000)
      constant := (478282531865597100151631846131668318880615725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree054.table
  base := (-7368424657364194846263585350299355966243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-59023540531907497074942670445370000000000000)
      constant := (502987501126677984847207144711240291886336595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8675346110804627697/2500000000000000000)
  centralHi := (347013844432185107881/100000000000000000000)
  directionLo := (21892016367224773529/6250000000000000000)
  directionHi := (70054452375119275293/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree055.table
  base := (-3617332348995043577167268984970378149743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-58781770540092822643907233647150000000000000)
      constant := (499178525236117670957095745148706821441728190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree055.table
  base := (-3617555727665186355987097561795082553823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-60181491545335674613059762478950000000000000)
      constant := (524835331345787012865250124669736634258354590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21892016367224773529/6250000000000000000)
  centralHi := (70054452375119275293/20000000000000000000)
  directionLo := (14140025835975715991/4000000000000000000)
  directionHi := (5523447592178014059/1562500000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree056.table
  base := (-3546371335526254933470337746754191575659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-59914272080698402873494279701970000000000000)
      constant := (520507380346912498049024089352809159039036470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree056.table
  base := (-7093133354730299261469748507596586157963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-61339442558763852151176854512530000000000000)
      constant := (547133953477521776244844806919136799005230395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14140025835975715991/4000000000000000000)
  centralHi := (5523447592178014059/1562500000000000000)
  directionLo := (356699811975181121697/100000000000000000000)
  directionHi := (178349905987590560849/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree057.table
  base := (-3471077846278058711588083460014054199619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-61046773621303983103081325756790000000000000)
      constant := (542269063266298697237675055363610150089303270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree057.table
  base := (-3471248616134386442178860794828677910871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-62497393572192029689293946546110000000000000)
      constant := (569883337711366973967042782620827362512748430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356699811975181121697/100000000000000000000)
  centralHi := (178349905987590560849/50000000000000000000)
  directionLo := (71974107865251421937/20000000000000000000)
  directionHi := (179935269663128554843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree058.table
  base := (-3391455252112626741429038275950337330227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-62179275161909563332668371811610000000000000)
      constant := (564463544768901238757741669430202575346931910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree058.table
  base := (-1695802247604925314416092384735558504871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-63655344585620207227411038579690000000000000)
      constant := (593083458460098216251935235616457415525536860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71974107865251421937/20000000000000000000)
  centralHi := (179935269663128554843/50000000000000000000)
  directionLo := (5672087080375829133/1562500000000000000)
  directionHi := (363013573144053064513/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree059.table
  base := (-413438307098943289535754023332179247361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-63311776702515143562255417866430000000000000)
      constant := (587090799679107160776375095521128047403041040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree059.table
  base := (-330763684817524422123910916149579255849/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-64813295599048384765528130613270000000000000)
      constant := (616734293757544806494703405836739478517891700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5672087080375829133/1562500000000000000)
  centralHi := (363013573144053064513/100000000000000000000)
  directionLo := (91532406658330019743/25000000000000000000)
  directionHi := (366129626633320078973/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree060.table
  base := (-3219233962120969152870674024688005161747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-64444278243120723791842463921250000000000000)
      constant := (610150806306257127909685685058154995247653510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree060.table
  base := (-6438695701005304715198925388325409848723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-65971246612476562303645222646850000000000000)
      constant := (640835824742363766547154778251009348305785795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91532406658330019743/25000000000000000000)
  centralHi := (366129626633320078973/100000000000000000000)
  directionLo := (369219382901948909981/100000000000000000000)
  directionHi := (184609691450974454991/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree061.table
  base := (-3126639923996396992388689848762583128667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-65576779783726304021429509976070000000000000)
      constant := (633643545958737140061419793112176404274457110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree061.table
  base := (-3126739370591968030925740993012024688611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-67129197625904739841762314680430000000000000)
      constant := (665388035215528024159871015785833745949742630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369219382901948909981/100000000000000000000)
  centralHi := (184609691450974454991/50000000000000000000)
  directionLo := (186141748354807258211/50000000000000000000)
  directionHi := (372283496709614516423/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree062.table
  base := (-3029726200619932821374556344163877954617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-66709281324331884251016556030890000000000000)
      constant := (657569002525934964338323506821791178133470610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree062.table
  base := (-6059626027046544247138371084425458673613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-68287148639332917379879406714010000000000000)
      constant := (690390911260993278082866854773467636649887645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186141748354807258211/50000000000000000000)
  centralHi := (372283496709614516423/100000000000000000000)
  directionLo := (75064519217584858081/20000000000000000000)
  directionHi := (187661298043962145203/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree063.table
  base := (-183030899624023988209564839754745810111/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-67841782864937464480603602085710000000000000)
      constant := (681927162118572962563277122955653661221402080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree063.table
  base := (-1464285079281696473060047325937508420607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-69445099652761094917996498747590000000000000)
      constant := (715844440920516126863324408865255603986674620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75064519217584858081/20000000000000000000)
  centralHi := (187661298043962145203/50000000000000000000)
  directionLo := (1891686419217127813/500000000000000000)
  directionHi := (378337283843425562601/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree064.table
  base := (-1129178354226125058949437498901767141397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-68974284405543044710190648140530000000000000)
      constant := (706718012759258006256901817914472197210220025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree064.table
  base := (-2823011991318915338691254600749784805267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-70603050666189272456113590781170000000000000)
      constant := (741748613914887479937465821024427365738335110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1891686419217127813/500000000000000000)
  centralHi := (378337283843425562601/100000000000000000000)
  directionLo := (381328138953660696973/100000000000000000000)
  directionHi := (190664069476830348487/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree065.table
  base := (-678270466757601675890353724756431741699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-70106785946148624939777694195350000000000000)
      constant := (731941544116231245885532197681346947197878680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree065.table
  base := (-271313953130032237846123305415069679393/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-71761001679617449994230682814750000000000000)
      constant := (768103421404951449026152909592713458796626900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381328138953660696973/100000000000000000000)
  centralHi := (190664069476830348487/50000000000000000000)
  directionLo := (384295717865427118807/100000000000000000000)
  directionHi := (48036964733178389851/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree066.table
  base := (-2598903366662306096455645725062529934569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-71239287486754205169364740250170000000000000)
      constant := (757597747274282191638773876548335865467286770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree066.table
  base := (-1039581462221059096064323120501112810429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-72918952693045627532347774848330000000000000)
      constant := (794908855786727592169469831137966379833951425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384295717865427118807/100000000000000000000)
  centralHi := (48036964733178389851/12500000000000000000)
  directionLo := (96810138925871795603/25000000000000000000)
  directionHi := (387240555703487182413/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree067.table
  base := (-4960822544187367790430860916258944645307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-72371789027359785398951786304990000000000000)
      constant := (783686614537635568007017074017369474962594155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree067.table
  base := (-4960910237828721907367445184265373693667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-74076903706473805070464866881910000000000000)
      constant := (822164910515766378543237827347021605037953555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96810138925871795603/25000000000000000000)
  centralHi := (387240555703487182413/100000000000000000000)
  directionLo := (390163167397163668741/100000000000000000000)
  directionHi := (195081583698581834371/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree068.table
  base := (-47152126997393277352518541540903685417/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3818)
      previous := (2047)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-4323781798115609742855225432930000000000000)
      constant := (47659302309432067760209674730122956021866500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree068.table
  base := (-4715289142771904103832940012158621020237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3772)
      previous := (2093)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-4425579689405998976975409347970000000000000)
      constant := (49992445879797856444843000444555551639839565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390163167397163668741/100000000000000000000)
  centralHi := (195081583698581834371/50000000000000000000)
  directionLo := (393064048731537845499/100000000000000000000)
  directionHi := (786128097463075691/200000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree069.table
  base := (-557622315570168241075147149686868400251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-74636792108570945858125878414630000000000000)
      constant := (837162315700352941726597428075647403879295320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree069.table
  base := (-4461045146041806982630643043862253526433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-76392805733330160146699050949070000000000000)
      constant := (878028859253455442329273498047705130962912945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393064048731537845499/100000000000000000000)
  centralHi := (786128097463075691/200000000000000000)
  directionLo := (79188735465865435817/20000000000000000000)
  directionHi := (197971838664663589543/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree070.table
  base := (-4198121163693820947168191989876039596293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-75769293649176526087712924469450000000000000)
      constant := (864549138893908809586167562983387368350069845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree070.table
  base := (-4198179213385581491710082203231172719803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-77550756746758337684816142982650000000000000)
      constant := (906636744219928127484704095267892866259653995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79188735465865435817/20000000000000000000)
  centralHi := (197971838664663589543/50000000000000000000)
  directionLo := (398802513568949257869/100000000000000000000)
  directionHi := (39880251356894925787/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree071.table
  base := (-196332080378236001013113877021332947173/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-76901795189782106317299970524270000000000000)
      constant := (892368604547507517563218717130458433480100900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree071.table
  base := (-981673044520865338455924828969402065611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-78708707760186515222933235016230000000000000)
      constant := (935695231243711801840490963903978568182305260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398802513568949257869/100000000000000000000)
  centralHi := (39880251356894925787/10000000000000000000)
  directionLo := (80328200288753776193/20000000000000000000)
  directionHi := (200820500721884440483/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree072.table
  base := (-1823270356720460485987105454824652048461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-78034296730387686546887016579090000000000000)
      constant := (920620708944897150290317371959582266739843130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree072.table
  base := (-145863390388807454656982516452109478719/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-79866658773614692761050327049810000000000000)
      constant := (965204317205406618374675051880574635243828375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80328200288753776193/20000000000000000000)
  centralHi := (200820500721884440483/50000000000000000000)
  directionLo := (404459569367069315863/100000000000000000000)
  directionHi := (50557446170883664483/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree073.table
  base := (-1678909611944145220101085744717996925679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-79166798270993266776474062633910000000000000)
      constant := (949305448867054675892174919806906966654363070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree073.table
  base := (-3357857580280548615262246566706648016227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-81024609787042870299167419083390000000000000)
      constant := (995163999408708503395531957740518680849655955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404459569367069315863/100000000000000000000)
  centralHi := (50557446170883664483/12500000000000000000)
  directionLo := (101814657731720029553/25000000000000000000)
  directionHi := (407258630926880118213/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree074.table
  base := (-3060477782658116510245956731672494533851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-80299299811598847006061108688730000000000000)
      constant := (978422821523318260519016738718507736195755915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree074.table
  base := (-1530255588975513513361044108166864078973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-82182560800471047837284511116970000000000000)
      constant := (1025574275520579070757181241538861288435304090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101814657731720029553/25000000000000000000)
  centralHi := (407258630926880118213/100000000000000000000)
  directionLo := (205019292797213571453/50000000000000000000)
  directionHi := (410038585594427142907/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree075.table
  base := (-1377258474179593457874665136733647406363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-81431801352204427235648154743550000000000000)
      constant := (1007972824492118809345497113327519276986832790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree075.table
  base := (-1377273009477466505434540519432214491927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-83340511813899225375401603150550000000000000)
      constant := (1056435143519940265496991157846022700354992910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205019292797213571453/50000000000000000000)
  centralHi := (410038585594427142907/100000000000000000000)
  directionLo := (412799819389640665893/100000000000000000000)
  directionHi := (206399909694820332947/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree076.table
  base := (-609984301556156390723102515548136934213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-82564302892810007465235200798370000000000000)
      constant := (1037955455669970730238325232332083305560746580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree076.table
  base := (-243996250770173695229799068807325301601/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-84498462827327402913518695184130000000000000)
      constant := (1087746601653677033497743397552890448175596650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412799819389640665893/100000000000000000000)
  centralHi := (206399909694820332947/50000000000000000000)
  directionLo := (12985709547089396699/3125000000000000000)
  directionHi := (415542705506860694369/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree077.table
  base := (-423347795647886255856254729368659340171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-83696804433415587694822246853190000000000000)
      constant := (1068370713227569053279828749557306308801793575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree077.table
  base := (-2116760995491169155573627810895200451593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-85656413840755580451635787217710000000000000)
      constant := (1119508648398905043889149506505001306042344345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12985709547089396699/3125000000000000000)
  centralHi := (415542705506860694369/100000000000000000000)
  directionLo := (52283450612951363043/12500000000000000000)
  directionHi := (83653520980722180869/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree078.table
  base := (-1784922631857523776738632427176840786827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-84829305974021167924409292908010000000000000)
      constant := (1099218595572001036519256211085240395189104955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree078.table
  base := (-1784941787978335817386483765680823520399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-86814364854183757989752879251290000000000000)
      constant := (1151721282430609411308556204663905630039070335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52283450612951363043/12500000000000000000)
  centralHi := (83653520980722180869/20000000000000000000)
  directionLo := (105243716713767748811/25000000000000000000)
  directionHi := (84194973371014199049/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree079.table
  base := (-288897697501030059088315857227310388357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-85961807514626748153996338962830000000000000)
      constant := (1130499101314218898170439919268326047332362025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree079.table
  base := (-1444505151576643260749489996709564075779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-87972315867611935527869971284870000000000000)
      constant := (1184384502593888019345702434218652039731498035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105243716713767748811/25000000000000000000)
  centralHi := (84194973371014199049/20000000000000000000)
  directionLo := (211832414738329383589/50000000000000000000)
  directionHi := (423664829476658767179/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree080.table
  base := (-1095436825040017537783583203534231928181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-87094309055232328383583385017650000000000000)
      constant := (1162212229241039479678504186079079104591335365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree080.table
  base := (-547725659475040704508354895355197719639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-89130266881040113065987063318450000000000000)
      constant := (1217498307880142471682848330821270435770729870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211832414738329383589/50000000000000000000)
  centralHi := (423664829476658767179/100000000000000000000)
  directionLo := (53292227527116927889/12500000000000000000)
  directionHi := (426337820216935423113/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree081.table
  base := (-92220986163982986182673102999099802193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-88226810595837908613170431072470000000000000)
      constant := (1194357978291039165141453640823059218859946760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree081.table
  base := (-184445123431194942819517125109498003731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-90288217894468290604104155352030000000000000)
      constant := (1251062697406653496898089068067569304615304460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53292227527116927889/12500000000000000000)
  centralHi := (426337820216935423113/100000000000000000000)
  directionLo := (214497078161434142047/50000000000000000000)
  directionHi := (85798831264573656819/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree082.table
  base := (-371481894949840276225871812994833166677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-89359312136443488842757477127290000000000000)
      constant := (1226936347533800585296158185470399398222455205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree082.table
  base := (-371492854531201307372522572873346427321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-91446168907896468142221247385610000000000000)
      constant := (1285077670399058038060522769759886043237563465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214497078161434142047/50000000000000000000)
  centralHi := (85798831264573656819/20000000000000000000)
  directionLo := (431634145279322346567/100000000000000000000)
  directionHi := (53954268159915293321/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree083.table
  base := (3420969515437032400988247406607651317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-90491813677049069072344523182110000000000000)
      constant := (1259947336152043518614240090552899644168459195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree083.table
  base := (682288305511957826458782614603183809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-92604119921324645680338339419190000000000000)
      constant := (1319543226176314181841033742166143524009060075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431634145279322346567/100000000000000000000)
  centralHi := (53954268159915293321/12500000000000000000)
  directionLo := (434258085224504195347/100000000000000000000)
  directionHi := (108564521306126048837/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree084.table
  base := (386940538102358680185477598276337721199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-91624315217654649301931569236930000000000000)
      constant := (1293390943426237688536426189585575924021397665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree084.table
  base := (386932255899539323804508790928068517013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-93762070934752823218455431452770000000000000)
      constant := (1354459364137799163456759819444681177021251355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434258085224504195347/100000000000000000000)
  centralHi := (108564521306126048837/25000000000000000000)
  directionLo := (10921656633573679957/2500000000000000000)
  directionHi := (436866265342947198281/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree085.table
  base := (155815332864294719981241074826985577013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3818)
      previous := (2047)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-5456283338721189972442271487750000000000000)
      constant := (78074539336550077922724220774504406610691575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree085.table
  base := (389534733014784551200192160834359972917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550000000000000000000000000000000000000000
      center := (3772)
      previous := (2093)
      next := (0)
      square := (95435523084739906987672420350000000000000)
      linear := (-5583530702834176515092501381550000000000000)
      constant := (81754475514837431105038494029225523586187670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10921656633573679957/2500000000000000000)
  centralHi := (436866265342947198281/100000000000000000000)
  directionLo := (87891793247500860787/20000000000000000000)
  directionHi := (6866546347461004749/1562500000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree086.table
  base := (1179829218542621100716466282820134997423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-93889318298865809761105661346570000000000000)
      constant := (1361576011475437680469076313854373285213828705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree086.table
  base := (147477870395838503098239607312154528689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-96077972961609178294689615519930000000000000)
      constant := (1425643384548190348158636573513733519054934520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87891793247500860787/20000000000000000000)
  centralHi := (6866546347461004749/1562500000000000000)
  directionLo := (221018230140851473551/50000000000000000000)
  directionHi := (442036460281702947103/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree087.table
  base := (794599042863468001727688526779125940327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-95021819839471389990692707401390000000000000)
      constant := (1396317471189803275333057442670167021902635090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree087.table
  base := (1589192650481883145530358509110242388331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-97235923975037355832806707553510000000000000)
      constant := (1461911266105907190357264052382244900753414885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221018230140851473551/50000000000000000000)
  centralHi := (442036460281702947103/100000000000000000000)
  directionLo := (444599011953714474831/100000000000000000000)
  directionHi := (27787438247107154677/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree088.table
  base := (401436632694574107408192939553859188913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-96154321380076970220279753456210000000000000)
      constant := (1431491547420537399690614786708461897919689275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree088.table
  base := (501794610362886076666140105823690468353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-98393874988465533370923799587090000000000000)
      constant := (1498629728050307265446740574836694792721241020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444599011953714474831/100000000000000000000)
  centralHi := (27787438247107154677/6250000000000000000)
  directionLo := (89429375630619438171/20000000000000000000)
  directionHi := (55893359769137148857/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree089.table
  base := (2433784360332475777636551936169884392397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-97286822920682550449866799511030000000000000)
      constant := (1467098239771213194956916349963564448841040995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree089.table
  base := (1216890129234721954363327191692706544809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-99551826001893710909040891620670000000000000)
      constant := (1535798770044967490083398942153503765743494030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89429375630619438171/20000000000000000000)
  centralHi := (55893359769137148857/12500000000000000000)
  directionLo := (8993606170027734659/2000000000000000000)
  directionHi := (449680308501386732951/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree090.table
  base := (2869001594360293105554043146435972942643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-98419324461288130679453845565850000000000000)
      constant := (1503137547886597098015614237912699942706357405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree090.table
  base := (2868998031654060626515655717146407929659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-100709777015321888447157983654250000000000000)
      constant := (1573418391786951469322492885778529678375071765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8993606170027734659/2000000000000000000)
  centralHi := (449680308501386732951/100000000000000000000)
  directionLo := (226099772813764645231/50000000000000000000)
  directionHi := (452199545627529290463/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree091.table
  base := (3312834791862460929580384870751329726931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-99551826001893710909040891620670000000000000)
      constant := (1539609471447226218868799863816235014366245885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree091.table
  base := (828207924455955255048401091204419214753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-101867728028750065985275075687830000000000000)
      constant := (1611488593002367082302324848852712629183817020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226099772813764645231/50000000000000000000)
  centralHi := (452199545627529290463/100000000000000000000)
  directionLo := (113676206359770365541/25000000000000000000)
  directionHi := (90940965087816292433/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree092.table
  base := (18826419431590814521754632890539969409/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-100684327542499291138627937675490000000000000)
      constant := (1576514010164732818659317467622250153477603000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree092.table
  base := (1882640599808123148917069981516712702227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-103025679042178243523392167721410000000000000)
      constant := (1650009373442547983459894059200861899128308090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113676206359770365541/25000000000000000000)
  centralHi := (90940965087816292433/20000000000000000000)
  directionLo := (4571963773800347419/1000000000000000000)
  directionHi := (457196377380034741901/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree093.table
  base := (4226348817449433526868123154182374175337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-101816829083104871368214983730310000000000000)
      constant := (1613851163777811916931672691260152592050085895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree093.table
  base := (2113173242365278732519566041912740836751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-104183630055606421061509259754990000000000000)
      constant := (1688980732880770295854484621417735463054631170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4571963773800347419/1000000000000000000)
  centralHi := (457196377380034741901/100000000000000000000)
  directionLo := (229837212338031079109/50000000000000000000)
  directionHi := (459674424676062158219/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree094.table
  base := (2348014765209341756877888687666956012031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-102949330623710451597802029785130000000000000)
      constant := (1651620932048742564142429719765460508624308770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree094.table
  base := (1174006876319047941864052524531576513073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-105341581069034598599626351788570000000000000)
      constant := (1728402671109428429945979008826325536736685820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229837212338031079109/50000000000000000000)
  centralHi := (459674424676062158219/100000000000000000000)
  directionLo := (231069592283964498157/50000000000000000000)
  directionHi := (92427836913585799263/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree095.table
  base := (2587162987568093293870078090224372042013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-104081832164316031827389075839950000000000000)
      constant := (1689823314760385796879606920318245305604252710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree095.table
  base := (1034864843442437228059264082123462967447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-106499532082462776137743443822150000000000000)
      constant := (1768275187937604810848516674090926059819413725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231069592283964498157/50000000000000000000)
  centralHi := (92427836913585799263/20000000000000000000)
  directionLo := (464590868533758357553/100000000000000000000)
  directionHi := (232295434266879178777/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree096.table
  base := (707654763207780812790694303347754197673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-105214333704921612056976121894770000000000000)
      constant := (1728458311713593031914645411124708115575299640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree096.table
  base := (1415309144966132213866109371307391098919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-107657483095890953675860535855730000000000000)
      constant := (1808598283188977597720805681512678161655255460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464590868533758357553/100000000000000000000)
  centralHi := (232295434266879178777/50000000000000000000)
  directionLo := (467029682500795168619/100000000000000000000)
  directionHi := (23351484125039758431/5000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree097.table
  base := (3078382939845447227554956341987010229447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-106346835245527192286563167949590000000000000)
      constant := (1767525922724967894489132264554239378689305490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree097.table
  base := (384797784719401233169357369434751847511/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-108815434109319131213977627889310000000000000)
      constant := (1849371956700018451772788624904866388143362960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell013.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467029682500795168619/100000000000000000000)
  centralHi := (23351484125039758431/5000000000000000000)
  directionLo := (93891165409453756621/20000000000000000000)
  directionHi := (234727913523634391553/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 89
  qDenominator := 255
  table := BinomialMassData.Q89_255.Degree098.table
  base := (3330454629051900394166855902867412772489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64906)
      previous := (34799)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-107479336786132772516150214004410000000000000)
      constant := (1807026147624932425536679965107672468737479630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q89_255.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 91
  qDenominator := 255
  table := BinomialMassData.Q91_255.Degree098.table
  base := (6660908109019955878088646464244800079913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (64124)
      previous := (35581)
      next := (0)
      square := (1622403892440578418790431145950000000000000)
      linear := (-109973385122747308752094719922890000000000000)
      constant := (1890596208318439243985230365773393208346422855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q91_255.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell013.Kernel098
