import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell073.Parameters
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch000_049
import ForestUnimodality.BinomialMassData.Q4777_9702.Batch050_099
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch000_049
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree000.table
  base := (3351855639239379781901107/80000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (516019410454381724506767150000000000000)
      linear := (6946862915605132773183561000000000000)
      constant := (209490977452461236368819187500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree000.table
  base := (3351855639239379781901107/80000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (516019410454381724506767150000000000000)
      linear := (6946862915605132773183561000000000000)
      constant := (209490977452461236368819187500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree001.table
  base := (24420699938661835115593722464277454790831/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-3931453320138698275198845078581763000000000000)
      constant := (958742487582358821502312922336458947843746748385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree001.table
  base := (243749589660239460193425008951164570584047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-875974080549446103512319579911364000000000000)
      constant := (212656351842826408101407959737588204381943755461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24997091050574339969/50000000000000000000)
  directionHi := (49994182101148679939/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree002.table
  base := (146444243738422599719609408687504051286469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-15834796596854437114828875625892226000000000000)
      constant := (1156461420897869052002583390813417843062499029423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree002.table
  base := (29186586329617770446048542897770997319269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-1764057418465519319695027527774414000000000000)
      constant := (128054612363762813298571779396824496682870237235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/50000000000000000000)
  centralHi := (49994182101148679939/100000000000000000000)
  directionLo := (70702450367194700757/100000000000000000000)
  directionHi := (35351225183597350379/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree003.table
  base := (91009150181008627313562591165850175536987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-2645187394825719742140006788291214000000000000)
      constant := (81264891673286193040576942130052118541543000681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree003.table
  base := (1132180637257608078983181308534982923147/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-442023459396932089312955912606244000000000000)
      constant := (13482710250658915031260347561320781077623583480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70702450367194700757/100000000000000000000)
  centralHi := (35351225183597350379/50000000000000000000)
  directionLo := (86592463482040081719/100000000000000000000)
  directionHi := (2164811587051002043/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree004.table
  base := (3682927183215201391615982060040181165683/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-15889288255004259121845623281674813000000000000)
      constant := (246706263969648065106282710989014532046044422088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree004.table
  base := (29295675054793986229661931114279396688729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-1770112047148832876030221711750257000000000000)
      constant := (27274719491943564139573572309740996816218713427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86592463482040081719/100000000000000000000)
  centralHi := (2164811587051002043/2500000000000000000)
  directionLo := (24997091050574339969/25000000000000000000)
  directionHi := (99988364202297359877/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree005.table
  base := (39810294642759525019213553550055756352813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-39750466466585558808122432032078326000000000000)
      constant := (361070579354197937397845052023116086567140810471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree005.table
  base := (9890010200360474117294930584961498727703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-2214153716106869484121575685681782000000000000)
      constant := (19964665485967870790963495356581804306226019578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/25000000000000000000)
  centralHi := (99988364202297359877/100000000000000000000)
  directionLo := (111790389657671715219/100000000000000000000)
  directionHi := (5589519482883585761/5000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree006.table
  base := (1746964808179665110199278853744747820969/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-2651242023509033298475200972267057000000000000)
      constant := (16087973344519178128777482928804636160697636376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree006.table
  base := (6941146342390765694979988368103276943227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-886065128354968697404309886537769000000000000)
      constant := (5342356278357793909120918828978478241646502534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111790389657671715219/100000000000000000000)
  centralHi := (5589519482883585761/5000000000000000000)
  directionLo := (7653764765974877899/6250000000000000000)
  directionHi := (24492047251119609277/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree007.table
  base := (404291291067127939319989070749399510561/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (82605935283768789604216805673450000000000000)
      linear := (-568308636527955509561069418056487000000000000)
      constant := (2595456441014129685162894675322662046228414075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree007.table
  base := (20071587460621239254145875276981316357929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (18356874507504175467603734594100000000000000)
      linear := (-126621920572365008175685046267136000000000000)
      constant := (575365443931074220105614395109087424058483123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7653764765974877899/6250000000000000000)
  centralHi := (24492047251119609277/20000000000000000000)
  directionLo := (26454434567943201659/20000000000000000000)
  directionHi := (16534021604964501037/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree008.table
  base := (297381439233358646253618953617471299083/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-31833068168158340250707994219132213000000000000)
      constant := (120904613267510788644827442209050835014602264025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree008.table
  base := (737763311996419310284664642049253024159/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-3546278722980979308395637607476357000000000000)
      constant := (13420755748870074820141721831003237134950905170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26454434567943201659/20000000000000000000)
  centralHi := (16534021604964501037/12500000000000000000)
  directionLo := (28280980146877880303/20000000000000000000)
  directionHi := (35351225183597350379/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree009.table
  base := (17116270657882598523601960027599802081/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-1326630116535068908626799516796169000000000000)
      constant := (4526155916284932362425492390405909072119744320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree009.table
  base := (5429818705184229429607026439382463562961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-1330106797313005305495663860469294000000000000)
      constant := (4527791893925325114585627559457544321774992681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28280980146877880303/20000000000000000000)
  centralHi := (35351225183597350379/25000000000000000000)
  directionLo := (74991273151723019907/50000000000000000000)
  directionHi := (29996509260689207963/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree010.table
  base := (3966452920823453988587594436792906597139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-39804958124735380815139179687860913000000000000)
      constant := (128973346288722517416010497754014829472700324313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree010.table
  base := (1962635902845782837836061976013841356471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-4434362060897052524578345555339407000000000000)
      constant := (14351537279208871881207516572054798228339868346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991273151723019907/50000000000000000000)
  centralHi := (29996509260689207963/20000000000000000000)
  directionLo := (39523871299213079473/25000000000000000000)
  directionHi := (158095485196852317893/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree011.table
  base := (2749801848631977666336783533150313864591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (33451990321526204054600194033050000000000000)
      linear := (-361908290107635546259130350596903000000000000)
      constant := (1157107553652128373793278991684468396899840757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree011.table
  base := (1085102528585617772292399986582110063587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (7433775627005823123244487562900000000000000)
      linear := (-80634772394298993928424785607784000000000000)
      constant := (257742624002068642206459348617997443940085805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39523871299213079473/25000000000000000000)
  centralHi := (158095485196852317893/100000000000000000000)
  directionLo := (165811943730211924133/100000000000000000000)
  directionHi := (82905971865105962067/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree012.table
  base := (869525043729888761526987604439086274891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-5308538675701380153285596128509957000000000000)
      constant := (17180482244837005479695355795618320702005649266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree012.table
  base := (852443700862376527422685603381281534131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-1774148466271041913587017834400819000000000000)
      constant := (5744296232609046649801391583193069585154544502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165811943730211924133/100000000000000000000)
  centralHi := (82905971865105962067/50000000000000000000)
  directionLo := (173184926964080163439/100000000000000000000)
  directionHi := (2164811587051002043/1250000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree013.table
  base := (220420082428788303464096494996188376399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-51762793059600941661785957890953963000000000000)
      constant := (172404375644190159531641169459322909476379898932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree013.table
  base := (169933349973745469171837509173075905643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-5766487067771162348852407477133982000000000000)
      constant := (19224597324930920754023935529714030652749650045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173184926964080163439/100000000000000000000)
  centralHi := (2164811587051002043/1250000000000000000)
  directionLo := (22532073380071945891/12500000000000000000)
  directionHi := (180256587040575567129/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree014.table
  base := (145154345260657225399762352174652183107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (82605935283768789604216805673450000000000000)
      linear := (-1137729347712029835591868380108537000000000000)
      constant := (3940712005237128701397549824813417845428317881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree014.table
  base := (114873736343255686247510462864049244167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (9178437253752087733801867297050000000000000)
      linear := (-126745484423044876672321662266643000000000000)
      constant := (439601476017992760649901733463314843905998429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22532073380071945891/12500000000000000000)
  centralHi := (180256587040575567129/100000000000000000000)
  directionLo := (9353055037724226197/5000000000000000000)
  directionHi := (187061100754484523941/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree015.table
  base := (-983475126600997096301693933712982839719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-13274374003595107161381587413262814000000000000)
      constant := (48117668389642301853511570922577021537265989203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree015.table
  base := (-26025682334900194415842394513887599117/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-2218190135229078521678371808332344000000000000)
      constant := (8054063897818244053804342052382105341338600860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9353055037724226197/5000000000000000000)
  centralHi := (187061100754484523941/100000000000000000000)
  directionLo := (96813317342504881199/50000000000000000000)
  directionHi := (193626634685009762399/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree016.table
  base := (-260914240071252105528575608514551816629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-63720627994466502508432736094047013000000000000)
      constant := (242593227841678356020727284878577548301561639428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree016.table
  base := (-1071050400223032159833673617170883022733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-7098612074645272173126469398928557000000000000)
      constant := (27077069830341525188425379606224305680057758321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96813317342504881199/50000000000000000000)
  centralHi := (193626634685009762399/100000000000000000000)
  directionLo := (24997091050574339969/12500000000000000000)
  directionHi := (199976728404594719753/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree017.table
  base := (-3042745384445871828341679240371173143301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-135413145945510045581296657656822726000000000000)
      constant := (542403153935577527322632272408028304995346354833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree017.table
  base := (-3094896093676165006374070976177068094987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-15085307487206617562435646745720164000000000000)
      constant := (60551541937529500685416323314621567749928845319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/12500000000000000000)
  centralHi := (199976728404594719753/100000000000000000000)
  directionLo := (103065646734699937609/50000000000000000000)
  directionHi := (206131293469399875219/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree018.table
  base := (-3866495515088864362600860881160535425423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-5310556885262484672063994189835238000000000000)
      constant := (22391774460127005982747422649322094087670684617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree018.table
  base := (-7832165180841154759960996670242439241/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-2662231804187115129769725782263869000000000000)
      constant := (11250343628344784837624252023293691077316359750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103065646734699937609/50000000000000000000)
  centralHi := (206131293469399875219/100000000000000000000)
  directionLo := (1657088680481125799/781250000000000000)
  directionHi := (212107351101584102273/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree019.table
  base := (-2286082174211468277786416727325710289317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-75678462929332063355079514297140063000000000000)
      constant := (335802022776960902936190323249314494668008067761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree019.table
  base := (-115480920919588483507928386010885428347/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-8430737081519381997400531320723132000000000000)
      constant := (37496933171524213750574175137166535643272072780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1657088680481125799/781250000000000000)
  centralHi := (212107351101584102273/100000000000000000000)
  directionLo := (43583917508775406419/20000000000000000000)
  directionHi := (6809987110746157253/3125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree020.table
  base := (-2585599765336278256827993290714400283171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-79664407907620583637295107031504413000000000000)
      constant := (371695881611539217735640440216426276313987703543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree020.table
  base := (-5215800977726374114387390547628680565433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-17749557500954837210983770589309314000000000000)
      constant := (83016983106279730355928066208938134280349518221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43583917508775406419/20000000000000000000)
  centralHi := (6809987110746157253/3125000000000000000)
  directionLo := (223580779315343430439/100000000000000000000)
  directionHi := (5589519482883585761/2500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree021.table
  base := (-1418368536106305086804017350767324910863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (9178437253752087733801867297050000000000000)
      linear := (-189683339877344906846963038017843000000000000)
      constant := (929550587652592060633710637826131183620959638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree021.table
  base := (-1143130331263040195545664123868454823693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (498036)
      previous := (249018)
      next := (249018)
      square := (6118958169168058489201244864700000000000000)
      linear := (-126786672373271499504533867599812000000000000)
      constant := (622876217300013479428161605211202906751621015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223580779315343430439/100000000000000000000)
  centralHi := (5589519482883585761/2500000000000000000)
  directionLo := (229102123785920229513/100000000000000000000)
  directionHi := (114551061892960114757/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree022.table
  base := (-6087642915643090089879535503024297590793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (5445468)
      previous := (2722734)
      next := (2722734)
      square := (66903980643052408109200388066100000000000000)
      linear := (-1448533848995002052921095743805506000000000000)
      constant := (7445882004653977301146398330636625860081662189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree022.table
  base := (-6127451079578077981556143864223881454443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (7433775627005823123244487562900000000000000)
      linear := (-161369621295760195399580053595334000000000000)
      constant := (831601480945216409106539328554343381883647071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229102123785920229513/100000000000000000000)
  centralHi := (114551061892960114757/50000000000000000000)
  directionLo := (234493499626710187481/100000000000000000000)
  directionHi := (117246749813355093741/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree023.table
  base := (-6421372826958710852900431071407376209399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-183244485684972288967883770469194926000000000000)
      constant := (986595935658256083117425934429658954719268214267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree023.table
  base := (-6458874771969783349412726895204766835429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-20413807514703056859531894432898464000000000000)
      constant := (110193219156966962560937754685258088552612994473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234493499626710187481/100000000000000000000)
  centralHi := (117246749813355093741/50000000000000000000)
  directionLo := (119881837251462685733/50000000000000000000)
  directionHi := (239763674502925371467/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree024.table
  base := (-3340750629987366001626934687262617221033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-10623131980086073862906386440995757000000000000)
      constant := (59819034706420274305722645335390599546984815421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree024.table
  base := (-6716768209165316231079841504282491099229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-7100630284206376691904867460253838000000000000)
      constant := (40088385855857861123032664462748558403360891691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119881837251462685733/50000000000000000000)
  centralHi := (239763674502925371467/100000000000000000000)
  directionLo := (7653764765974877899/3125000000000000000)
  directionHi := (244920472511196092769/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree025.table
  base := (-1374830239427822423272436501200778302901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-199188265598126370096746141406652326000000000000)
      constant := (1171343760650496205516621916590494472699491308165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree025.table
  base := (-6907261296554311447560576259923598832549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-22189974190535203291897310328624564000000000000)
      constant := (130834251827459941632874059982039902180707095913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7653764765974877899/3125000000000000000)
  centralHi := (244920472511196092769/100000000000000000000)
  directionLo := (24997091050574339969/10000000000000000000)
  directionHi := (249970910505743399691/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree026.table
  base := (-7004820021921202081699745450067715061229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-207160155554703410661177326875381026000000000000)
      constant := (1270356221618791606334722243930670114522810621657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree026.table
  base := (-703585689111531523825954173077409582919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-11539028764225638254040009138243807000000000000)
      constant := (70947852925044622328105876932799975358411838015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/10000000000000000000)
  centralHi := (249970910505743399691/100000000000000000000)
  directionLo := (254921310099868251457/100000000000000000000)
  directionHi := (127460655049934125729/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree027.table
  base := (-7078451286951327971438535523789294603921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-7967853537454831526874389346078138000000000000)
      constant := (50879304817125956889457213794813336342374267159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree027.table
  base := (-3553751267400250172002099721778086332121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-3994356811061224954043787704058444000000000000)
      constant := (25574201256825838484766211698051874705705874959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254921310099868251457/100000000000000000000)
  centralHi := (127460655049934125729/50000000000000000000)
  directionLo := (129888695223060122579/50000000000000000000)
  directionHi := (259777390446120245159/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree028.table
  base := (-1774873712933934901550452062705084681469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (82605935283768789604216805673450000000000000)
      linear := (-2276570770080178487653466304212637000000000000)
      constant := (15116978377400166163742680654007349857872796146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree028.table
  base := (-7126650683306156170716654908033208239493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (18356874507504175467603734594100000000000000)
      linear := (-507229065393539243682559881065586000000000000)
      constant := (3377119924579862761357896345015671325044138009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129888695223060122579/50000000000000000000)
  centralHi := (259777390446120245159/100000000000000000000)
  directionLo := (264544345679432016591/100000000000000000000)
  directionHi := (16534021604964501037/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree029.table
  base := (-1414391717002608800610382015421667119509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-231075825424434532354470883281567126000000000000)
      constant := (1593492736396325111500528850129726753314371984485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree029.table
  base := (-3548655278850318342772759238497905033829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-12871153771099748078314071060038382000000000000)
      constant := (88996608925860990030680380866530325270000895273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264544345679432016591/100000000000000000000)
  centralHi := (16534021604964501037/6250000000000000000)
  directionLo := (67306727503144901127/25000000000000000000)
  directionHi := (269226910012579604509/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree030.table
  base := (-6999453590956879606654955544411971360281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-26560857264556841435433563194477314000000000000)
      constant := (189977718950293924309205157275083339005319410797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree030.table
  base := (-7023093540213934077985918757187441228557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-8876796960038523124270283355979938000000000000)
      constant := (63661694878583542163471949965436787386838391803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67306727503144901127/25000000000000000000)
  centralHi := (269226910012579604509/100000000000000000000)
  directionLo := (273829412808201542803/100000000000000000000)
  directionHi := (68457353202050385701/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree031.table
  base := (-860654277315307621275296570613571255817/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-123509802668794306741666627109512263000000000000)
      constant := (915179278061465411469563387881000566840389249044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree031.table
  base := (-6907253352980661439297153879945591847259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-27518474218031642588993558015802864000000000000)
      constant := (204451640832674404804044957738274132882827404183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273829412808201542803/100000000000000000000)
  centralHi := (68457353202050385701/25000000000000000000)
  directionLo := (17397239090725635409/6250000000000000000)
  directionHi := (55671165090322033309/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree032.table
  base := (-6732233710118770030947310095863469116991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-254991495294165654047764439687753226000000000000)
      constant := (1955146984557198328251766434606710557393891757603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree032.table
  base := (-1688180466368799109372665993292521629411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-14203278777973857902588132981832957000000000000)
      constant := (109195165566769308989391515233379603942211321214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17397239090725635409/6250000000000000000)
  centralHi := (55671165090322033309/20000000000000000000)
  directionLo := (28280980146877880303/10000000000000000000)
  directionHi := (282809801468778803031/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree033.table
  base := (-6543096107761687661577031500780692386679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (7433775627005823123244487562900000000000000)
      linear := (-241472346419414779258214531824134000000000000)
      constant := (1913814523244007759496224084609648672738751163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree033.table
  base := (-656214114407949366362209307705576769439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1238962604500970520540747927150000000000000)
      linear := (-40350745032870232811789220263814000000000000)
      constant := (320659576874712411191991512114547175882884805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28280980146877880303/10000000000000000000)
  centralHi := (282809801468778803031/100000000000000000000)
  directionLo := (14359735552123940163/5000000000000000000)
  directionHi := (287194711042478803261/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree034.table
  base := (-6320204889304734346059870483473736884147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-270935275207319735176626810625210626000000000000)
      constant := (2217330953729533157595871520910520449140379694151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree034.table
  base := (-1584473053713125644964000426313446118449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-15091362115889931118770840929696007000000000000)
      constant := (123837565325483583136880424434260460921332468426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14359735552123940163/5000000000000000000)
  centralHi := (287194711042478803261/100000000000000000000)
  directionLo := (291513670853933900531/100000000000000000000)
  directionHi := (72878417713483475133/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree035.table
  base := (-3032854357066650945614851596115757351707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 800415000000000000000000000000000000000000000
      center := (6723486)
      previous := (3361743)
      next := (3361743)
      square := (82605935283768789604216805673450000000000000)
      linear := (-2845991481264252813684265266264687000000000000)
      constant := (24027458613055563863379193168792546215866688319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree035.table
  base := (-6082120919070331453413425988293251670221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (18356874507504175467603734594100000000000000)
      linear := (-634098113667263988851518159331736000000000000)
      constant := (5367699886070537887228655015791956682541779073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291513670853933900531/100000000000000000000)
  centralHi := (72878417713483475133/25000000000000000000)
  directionLo := (295769570001206389031/100000000000000000000)
  directionHi := (36971196250150798629/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree036.table
  base := (-722693074327287338262073208750428309603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-5312575094823589190842392251160519000000000000)
      constant := (46226088755697102198631814328864901268263307348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree036.table
  base := (-2898380589439781629096891117513446872923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-5326481817935334778317849625853019000000000000)
      constant := (46470609762586823138372480255770584901031537117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295769570001206389031/100000000000000000000)
  centralHi := (36971196250150798629/12500000000000000000)
  directionLo := (74991273151723019907/25000000000000000000)
  directionHi := (299965092606892079629/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree037.table
  base := (-5469458764288857041569323751021194836191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-294850945077050856869920367031396726000000000000)
      constant := (2641870802341327778112753166707921341284863771203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree037.table
  base := (-548355594545348408854111666509390252721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-16423487122764040943044902851490582000000000000)
      constant := (147546352016703735296804213097823212390838635385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74991273151723019907/25000000000000000000)
  centralHi := (299965092606892079629/100000000000000000000)
  directionLo := (76025684404443277431/25000000000000000000)
  directionHi := (12164109504710924389/4000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree038.table
  base := (-2565512739587086838958434759380057619551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-151411417516813948717175776250062713000000000000)
      constant := (1395832312055364931635226285613374868568381446083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree038.table
  base := (-2572038033824834754100961687035788740343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-16867528791722077551136256825422107000000000000)
      constant := (155911530848686548316629572061725492858100433891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76025684404443277431/25000000000000000000)
  centralHi := (12164109504710924389/4000000000000000000)
  directionLo := (308184836211301887999/100000000000000000000)
  directionHi := (601923508225199/195312500000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree039.table
  base := (-4767663961161739316520324250981744289313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-34532747221133881999864748663206014000000000000)
      constant := (327286569516030714519522870706515844001973493781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree039.table
  base := (-2389868645770549545609912369562992673197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-5770523486893371386409203599784544000000000000)
      constant := (54835582942587202108782475611354533930590134363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308184836211301887999/100000000000000000000)
  centralHi := (601923508225199/195312500000000)
  directionLo := (62442713430647706433/20000000000000000000)
  directionHi := (156106783576619266083/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree040.table
  base := (-4380653669269871785502592539933084659999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-318766614946781978563213923437582826000000000000)
      constant := (3103604270779704041057422414247406748410295624067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree040.table
  base := (-4391815578149080976911878788421043218473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-35511224259276301534637929546570314000000000000)
      constant := (346662899827442204266087961783474450309378016701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62442713430647706433/20000000000000000000)
  centralHi := (156106783576619266083/50000000000000000000)
  directionLo := (63238194078740927157/20000000000000000000)
  directionHi := (158095485196852317893/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree041.table
  base := (-39711480651108784880862306927119823181/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-163369252451679509563822554453155763000000000000)
      constant := (1632865505843421913560064278654447057497004143650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree041.table
  base := (-3981460906958814711490699828031009930299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-36399307597192374750820637494433364000000000000)
      constant := (364770265933560012501342763707047726642118812663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63238194078740927157/20000000000000000000)
  centralHi := (158095485196852317893/50000000000000000000)
  directionLo := (160059479571248307053/50000000000000000000)
  directionHi := (320118959142496614107/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree042.table
  base := (-141607480868845457608467212672043430727/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (18356874507504175467603734594100000000000000)
      linear := (-758980487210739364381125384070386000000000000)
      constant := (7782202248371716449237023522821821087441471275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree042.table
  base := (-22185685722269533624108537374145865863/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (249018)
      previous := (124509)
      next := (124509)
      square := (3059479084584029244600622432350000000000000)
      linear := (-126827860323498122336746072932981000000000000)
      constant := (1303859498820472523636012316624772132903861840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160059479571248307053/50000000000000000000)
  centralHi := (320118959142496614107/100000000000000000000)
  directionLo := (161999665313264020641/50000000000000000000)
  directionHi := (323999330626528041283/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree043.table
  base := (-1544354004921784549976390867065642942343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-171341142408256550128253739921884463000000000000)
      constant := (1801128728365817695328307984290733112362184371019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree043.table
  base := (-1548748055278054064495768308651665795851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-19087737136512260591593026695079732000000000000)
      constant := (201177682926836731630217750531467238578970714887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161999665313264020641/50000000000000000000)
  centralHi := (323999330626528041283/100000000000000000000)
  directionLo := (65566755140208378817/20000000000000000000)
  directionHi := (163916887850520947043/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree044.table
  base := (-52351123646456971417453860094324250803/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (33451990321526204054600194033050000000000000)
      linear := (-1448984193277231986863382914514453000000000000)
      constant := (15605963544836488794115760296717713044829847975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree044.table
  base := (-105026478849935800421291506704532723809/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (7433775627005823123244487562900000000000000)
      linear := (-322839319098682598341890589570434000000000000)
      constant := (3486211171769140694486476823970327269760094325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65566755140208378817/20000000000000000000)
  centralHi := (163916887850520947043/50000000000000000000)
  directionLo := (331623887460423848267/100000000000000000000)
  directionHi := (82905971865105962067/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree045.table
  base := (-2127493465269696890452630821998132854283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-13282446841839525236495179658563938000000000000)
      constant := (146485273269957410873753417342674240445040848557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree045.table
  base := (-2134966055657594253994607337684704476903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-13317213649618889205183823095295188000000000000)
      constant := (147254196379660834528310477777848493220665663537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331623887460423848267/100000000000000000000)
  centralHi := (82905971865105962067/25000000000000000000)
  directionLo := (335371168973015145659/100000000000000000000)
  directionHi := (16768558448650757283/5000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree046.table
  base := (-809603376941768119454709167678640151757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-183298977343122110974900518124977513000000000000)
      constant := (2068814834997464280479846981305065235180727924281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree046.table
  base := (-813046103678776549633009759669229988841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-20419862143386370415867088616874307000000000000)
      constant := (231073940952833074447350311988307478903235771517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335371168973015145659/100000000000000000000)
  centralHi := (16768558448650757283/5000000000000000000)
  directionLo := (8476926006161132721/2500000000000000000)
  directionHi := (339077040246445308841/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree047.table
  base := (-1093315301146122690226219583356621570269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-374569844642821262514232221718683726000000000000)
      constant := (4324220195506786845859088179288985997509164755977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree047.table
  base := (-13745709400024291857856059709415378191/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-20863903812344407023958442590805832000000000000)
      constant := (241493446458740634402579497617210400564508698680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8476926006161132721/2500000000000000000)
  centralHi := (339077040246445308841/100000000000000000000)
  directionLo := (171371422257513742957/50000000000000000000)
  directionHi := (68548568903005497183/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree048.table
  base := (-550377378891759386612634983144987743911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-42504637177710922564295934131934714000000000000)
      constant := (501652175078083606838191364952603077046953697107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree048.table
  base := (-556215163549660738091482489761683540191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-14205296987534962421366531043158238000000000000)
      constant := (168093046014625942090647639076745969936220170489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171371422257513742957/50000000000000000000)
  centralHi := (68548568903005497183/20000000000000000000)
  directionLo := (173184926964080163439/50000000000000000000)
  directionHi := (346369853928160326879/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree049.table
  base := (2275929270184019834303095383494870801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16335000000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1685835413954465093963608279050000000000000)
      linear := (-81323120482293907464201289599363000000000000)
      constant := (980752574489141746000939040647297755485813734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree049.table
  base := (373192769217438507310924788862901069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (15246)
      previous := (7623)
      next := (7623)
      square := (187315045994940565995956475450000000000000)
      linear := (-9059553165456259991728925672082000000000000)
      constant := (109542728228655447014540414426706661165440235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173184926964080163439/50000000000000000000)
  centralHi := (346369853928160326879/100000000000000000000)
  directionLo := (174979637354020379783/50000000000000000000)
  directionHi := (349959274708040759567/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree050.table
  base := (584674253252408918223883043155476753741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-398485514512552384207525778124869826000000000000)
      constant := (4908329497372982626979429052187965501073286904647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree050.table
  base := (144933330054410100697654781137069635459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-22196028819218516848232504512600407000000000000)
      constant := (274110814198660027058792719511224060645379104834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174979637354020379783/50000000000000000000)
  centralHi := (349959274708040759567/100000000000000000000)
  directionLo := (88378062958993375947/25000000000000000000)
  directionHi := (353512251835973503789/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree051.table
  base := (235185035549584645402714550282318439437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-45161933829903269419106329288177614000000000000)
      constant := (567903696788978637680175439752005855530155150155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree051.table
  base := (2287856174010833353846289268850018163/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-7546690162725517818774619495510644000000000000)
      constant := (95145187658362868083549529890959769613443628288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88378062958993375947/25000000000000000000)
  centralHi := (353512251835973503789/100000000000000000000)
  directionLo := (178514936659445648009/50000000000000000000)
  directionHi := (357029873318891296019/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree052.table
  base := (1782487720318354482085631149814981541067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-414429294425706465336388149062327226000000000000)
      constant := (5317982291221793830081735525948724804811892799489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree052.table
  base := (889156273783583275341497866949239048591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-23084112157134590064415212460463457000000000000)
      constant := (296986177091168122505572410773292018632907117733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178514936659445648009/50000000000000000000)
  centralHi := (357029873318891296019/100000000000000000000)
  directionLo := (22532073380071945891/6250000000000000000)
  directionHi := (360513174081151134257/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree053.table
  base := (1202014712806776687279333040794601774269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-211200592191141752950409667265527963000000000000)
      constant := (2764436974966949910110514710799476453555684912023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree053.table
  base := (2400193562936786261640218153088333698209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-47056307652185253345013132868789964000000000000)
      constant := (617525025201981667895847247394509613133012130667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22532073380071945891/6250000000000000000)
  centralHi := (360513174081151134257/100000000000000000000)
  directionLo := (90990784880265896151/25000000000000000000)
  directionHi := (72792627904212716921/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree054.table
  base := (1520125288537920140789304241279888251587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-7969871747015936045652787407403419000000000000)
      constant := (106366775856303078911356640662161575414739306827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree054.table
  base := (1518363851904572147812845257595422277807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-7990731831683554426865973469442169000000000000)
      constant := (106921479923641822661686022492339305675570767447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90990784880265896151/25000000000000000000)
  centralHi := (72792627904212716921/20000000000000000000)
  directionLo := (22961294297924633697/6250000000000000000)
  directionHi := (367380708766794139153/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree055.table
  base := (1845440486494379154916132524851716380887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 324135000000000000000000000000000000000000000
      center := (2722734)
      previous := (1361367)
      next := (1361367)
      square := (33451990321526204054600194033050000000000000)
      linear := (-1811342827667097467064800435820303000000000000)
      constant := (24639570291986883265225878132930477217823761549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree055.table
  base := (29501173280810236589469128632397173297/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72030000000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (7433775627005823123244487562900000000000000)
      linear := (-403574168000143799813045857557984000000000000)
      constant := (5503997383081018292785897148257233354907286375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22961294297924633697/6250000000000000000)
  centralHi := (367380708766794139153/100000000000000000000)
  directionLo := (92691694415530977999/25000000000000000000)
  directionHi := (370766777662123911997/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree056.table
  base := (4355677020002665339624385689327745843759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (165211870567537579208433611346900000000000000)
      linear := (-9108507229632951583553324304841674000000000000)
      constant := (126240456784341284488210808112645397537906471997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree056.table
  base := (1088177153239913741768741831895476798867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (9178437253752087733801867297050000000000000)
      linear := (-507352629244219112179196497065093000000000000)
      constant := (7049890059943602600880043560639607691642894658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92691694415530977999/25000000000000000000)
  centralHi := (370766777662123911997/100000000000000000000)
  directionLo := (374122201508969047881/100000000000000000000)
  directionHi := (187061100754484523941/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree057.table
  base := (1258604778218476096325733990061312729231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-25238263567143981564363559800331707000000000000)
      constant := (356267960497656279650321514831393889812453516106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree057.table
  base := (2515847809604006073954372694128110699061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-8434773500641591034957327443373694000000000000)
      constant := (119374219525941988518422779946931616473401900781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374122201508969047881/100000000000000000000)
  centralHi := (187061100754484523941/50000000000000000000)
  directionLo := (188723898795224433259/50000000000000000000)
  directionHi := (377447797590448866519/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree058.table
  base := (2863454636116465368578695969399610729317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-231130317082584354361487630937349713000000000000)
      constant := (3321948588636328352536285308121652925334681412239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree058.table
  base := (572441125403447394781699766101321114693/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-25748362170882809712963336304052607000000000000)
      constant := (371025892999870763999738243747404559673425875795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188723898795224433259/50000000000000000000)
  centralHi := (377447797590448866519/100000000000000000000)
  directionLo := (38074434749559089443/10000000000000000000)
  directionHi := (380744347495590894431/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree059.table
  base := (1286593802994446123926213800610645507497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-470232524121745749287406447343428126000000000000)
      constant := (6879002647343800247763790048881932955370277351495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree059.table
  base := (3215339243210740058164788903375502343301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-26192403839840846321054690277984132000000000000)
      constant := (384154239056528543844241590114296585323834449463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38074434749559089443/10000000000000000000)
  centralHi := (380744347495590894431/100000000000000000000)
  directionLo := (192006299632203531017/50000000000000000000)
  directionHi := (76802519852881412407/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree060.table
  base := (1430487486869400928829335431197522956331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-53133823786480309983537514756906314000000000000)
      constant := (790904270778661855941542918607324373501943576765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree060.table
  base := (1787584441084860317428607623832198081043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-8878815169599627643048681417305219000000000000)
      constant := (132502542405992174194250516090539723037405386806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192006299632203531017/50000000000000000000)
  centralHi := (76802519852881412407/20000000000000000000)
  directionLo := (387253269370019524797/100000000000000000000)
  directionHi := (193626634685009762399/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree061.table
  base := (3942584734568664855682444864800373861367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-243088152017449915208134409140442763000000000000)
      constant := (3680651704197598946838396968938286742193611459589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree061.table
  base := (1576649057798751120919261662607090149123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-54160974355513839074474796451694364000000000000)
      constant := (822171989638720580898981095677108314308200446245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387253269370019524797/100000000000000000000)
  centralHi := (193626634685009762399/50000000000000000000)
  directionLo := (78093408910542947899/20000000000000000000)
  directionHi := (48808380569089342437/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree062.table
  base := (8631034343254121413965533586028709178327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-494148193991476870980700003749614226000000000000)
      constant := (7608496535689119042312838331568890520718311935909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree062.table
  base := (4314635729729797202494467811798509668289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-27524528846714956145328752199778707000000000000)
      constant := (424889285382994424199363015638912628482022965707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78093408910542947899/20000000000000000000)
  centralHi := (48808380569089342437/12500000000000000000)
  directionLo := (196827291759612526273/50000000000000000000)
  directionHi := (393654583519225052547/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree063.table
  base := (9389914159004570687368190150982518920147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (498036)
      previous := (249018)
      next := (249018)
      square := (6118958169168058489201244864700000000000000)
      linear := (-379531431555596305022774897368362000000000000)
      constant := (5940829096063732887121121177897281354677551563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree063.table
  base := (4694149735440871065294401391072775031757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (249018)
      previous := (124509)
      next := (124509)
      square := (3059479084584029244600622432350000000000000)
      linear := (-190262384460360494921225212066056000000000000)
      constant := (2985832979642747691982259712818976608163287253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196827291759612526273/50000000000000000000)
  centralHi := (393654583519225052547/100000000000000000000)
  directionLo := (198408259259574012443/50000000000000000000)
  directionHi := (396816518519148024887/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree064.table
  base := (10161702628885543907672886524988370634897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-510091973904630952109562374687071626000000000000)
      constant := (8114963649878500752866184709522554817480964606099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree064.table
  base := (10160224051077707348722795010834751675653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-56825224369262058723022920295283514000000000000)
      constant := (906340873634318311250621190614845864674687155639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198408259259574012443/50000000000000000000)
  centralHi := (396816518519148024887/100000000000000000000)
  directionLo := (24997091050574339969/6250000000000000000)
  directionHi := (79990691361837887901/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree065.table
  base := (10946303932263493012239419902920297066389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-518063863861207992673993560155800326000000000000)
      constant := (8374236051424195938476592557365249245848658764063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree065.table
  base := (2736237580469816528918820330780085981053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-28856653853589065969602814121573282000000000000)
      constant := (467648210465869693028589954963249995030808991678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24997091050574339969/6250000000000000000)
  centralHi := (79990691361837887901/20000000000000000000)
  directionLo := (403065982014834610217/100000000000000000000)
  directionHi := (201532991007417305109/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree066.table
  base := (5871815842321374423883246662730418198671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36015000000000000000000000000000000000000000
      center := (302526)
      previous := (151263)
      next := (151263)
      square := (3716887813502911561622243781450000000000000)
      linear := (-241522384672995883029579773014017000000000000)
      constant := (3965809651571915691663975306405144202285027213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree066.table
  base := (5871196386448375008373830793570690618147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (100842)
      previous := (50421)
      next := (50421)
      square := (1238962604500970520540747927150000000000000)
      linear := (-80718169483600833547366854257589000000000000)
      constant := (1328789894462175337864931897351262228174170947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403065982014834610217/100000000000000000000)
  centralHi := (201532991007417305109/50000000000000000000)
  directionLo := (126923329811904877/31250000000000000)
  directionHi := (406154655398095606401/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree067.table
  base := (12553608008435115829454969518564967722361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-534007643774362073802855931093257726000000000000)
      constant := (8904855148099790462192553075158212792667037082187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree067.table
  base := (3138118584151584694860956835035091410723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-29744737191505139185785522069436332000000000000)
      constant := (497277966904257887790372803743134357125407940098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126923329811904877/31250000000000000)
  centralHi := (406154655398095606401/100000000000000000000)
  directionLo := (204610008519566686143/50000000000000000000)
  directionHi := (409220017039133372287/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree068.table
  base := (1672020336904434407208099591740593899233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-270989766865469557183643558280993213000000000000)
      constant := (4588100340816618240749453844495740394661499602444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree068.table
  base := (6687562777378256670374649254743146330179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-30188778860463175793876876043367857000000000000)
      constant := (512429885840713379110238485329357251844969799777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204610008519566686143/50000000000000000000)
  centralHi := (409220017039133372287/100000000000000000000)
  directionLo := (103065646734699937609/25000000000000000000)
  directionHi := (412262586938799750437/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree069.table
  base := (14211232450592381695848837636115581387913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-61105713743057350547968700225635014000000000000)
      constant := (1050174391693116952012453562770326220461193618019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree069.table
  base := (14210283827077522216511664807800257104611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-20421880352947474934645486678199588000000000000)
      constant := (351870974146064445932117439942351641744288692331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103065646734699937609/25000000000000000000)
  centralHi := (412262586938799750437/100000000000000000000)
  directionLo := (83056573209694664749/20000000000000000000)
  directionHi := (207641433024236661873/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree070.table
  base := (15058760213149988675369739931298270518561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (165211870567537579208433611346900000000000000)
      linear := (-11386190074369248887676520153049874000000000000)
      constant := (198591045537166129622252477814022451039422800563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree070.table
  base := (15057892734167894508628383057328818810843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (18356874507504175467603734594100000000000000)
      linear := (-1268443355035887714696309550662486000000000000)
      constant := (22179904834811279798530789962278727700188464441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83056573209694664749/20000000000000000000)
  centralHi := (207641433024236661873/50000000000000000000)
  directionLo := (209140668616482296941/50000000000000000000)
  directionHi := (418281337232964593883/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree071.table
  base := (15918694540837611146034482641813486192129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-565895203600670236060580672968172526000000000000)
      constant := (10014375396367450759364163313372807833194634748643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree071.table
  base := (15917901427234324734491776716242872635373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-63041807734674571236301875930324864000000000000)
      constant := (1118466970766178035509108141242696499552703597999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209140668616482296941/50000000000000000000)
  centralHi := (418281337232964593883/100000000000000000000)
  directionLo := (210629233085865758997/50000000000000000000)
  directionHi := (84251693234346303599/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree072.table
  base := (16790989057504427160305666805272541164929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-21254336798416565800926365127292638000000000000)
      constant := (381548579874049983047107552737901919931776338009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree072.table
  base := (1049391504880270947648084225427377664507/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-10654981845431774075414097313031319000000000000)
      constant := (191761297346218732245058107965152815491761905176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210629233085865758997/50000000000000000000)
  centralHi := (84251693234346303599/20000000000000000000)
  directionLo := (84842940440633640909/20000000000000000000)
  directionHi := (212107351101584102273/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree073.table
  base := (4418900488511749393990352619029815344279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-290919491756912158594721521952814963000000000000)
      constant := (5296634842031714056825791136845849567116305085386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree073.table
  base := (17674939383422811071556242657838662833459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-64817974410506717668667291826050964000000000000)
      constant := (1183117740840731983940408543938958604245118026417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84842940440633640909/20000000000000000000)
  centralHi := (212107351101584102273/50000000000000000000)
  directionLo := (213575239558150500611/50000000000000000000)
  directionHi := (427150479116301001223/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree074.table
  base := (742899821546537340847767666271480179209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-589810873470401357753874229374358626000000000000)
      constant := (10888749183102667106466185749024963141872185075075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree074.table
  base := (18571890118090851789698861209307494354593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-65706057748422790884849999773914014000000000000)
      constant := (1216116808612365639972589308434844753702172138859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213575239558150500611/50000000000000000000)
  centralHi := (427150479116301001223/100000000000000000000)
  directionLo := (430066215893841529743/100000000000000000000)
  directionHi := (26879138493365095609/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree075.table
  base := (19481635831396471764837615391184102616119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-66420307047442044257589490538120814000000000000)
      constant := (1243138876352889454532645406637677640028412523997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree075.table
  base := (19481082732414738061470543006564305617827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-22198047028779621367010902573925688000000000000)
      constant := (416521652717186361930520223762341824882396717867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430066215893841529743/100000000000000000000)
  centralHi := (26879138493365095609/6250000000000000000)
  directionLo := (432962317410200408597/100000000000000000000)
  directionHi := (216481158705100204299/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree076.table
  base := (20402992198604111904534955782414071383089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-605754653383555438882736600311816026000000000000)
      constant := (11491771555991101761464337889998214873671732782963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree076.table
  base := (5100621747327477413548193308156694392447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-33741112212127468658607707834820057000000000000)
      constant := (641731081552394095413624324043033603069528569322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432962317410200408597/100000000000000000000)
  centralHi := (216481158705100204299/50000000000000000000)
  directionLo := (435839175087754064191/100000000000000000000)
  directionHi := (6809987110746157253/1562500000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree077.table
  base := (20836461936939404930747593657217967203/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 6615000000000000000000000000000000000000000
      center := (55566)
      previous := (27783)
      next := (27783)
      square := (682693680031147021522452939450000000000000)
      linear := (-51756328498914865866686438335347000000000000)
      constant := (995050933793173704285256773448595677752099328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree077.table
  base := (10668037818607418110669481177307812742749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 735000000000000000000000000000000000000000
      center := (6174)
      previous := (3087)
      next := (3087)
      square := (75854853336794113502494771050000000000000)
      linear := (-5765753732684349007707718301358000000000000)
      constant := (111132433776404135014862833941552123473184103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435839175087754064191/100000000000000000000)
  centralHi := (6809987110746157253/1562500000000000000)
  directionLo := (219348583757188159971/50000000000000000000)
  directionHi := (438697167514376319943/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree078.table
  base := (22282245408700537054871035907931225583361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-69077603699634391112399885694363714000000000000)
      constant := (1345652993629562070180618236118471804763110863243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree078.table
  base := (22281824115317199979347299007706238556243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-23086130366695694583193610521788738000000000000)
      constant := (450867882197566648734716899555679488131598272603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219348583757188159971/50000000000000000000)
  centralHi := (438697167514376319943/100000000000000000000)
  directionLo := (220768330512496500241/50000000000000000000)
  directionHi := (441536661024993000483/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree079.table
  base := (5810023727284533275055634552975445852629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-314835161626643280288015078359001063000000000000)
      constant := (6213230144584279880321443682613425020245788004286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree079.table
  base := (5809927571971020550307426065119524070907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-35073237219001578482881769756614632000000000000)
      constant := (693923942214200770288260189206350847890623835282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220768330512496500241/50000000000000000000)
  centralHi := (441536661024993000483/100000000000000000000)
  directionLo := (444358010249688632753/100000000000000000000)
  directionHi := (222179005124844316377/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree080.table
  base := (24210065289867951054289406638631778482061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-637642213209863601140461342186730826000000000000)
      constant := (12746063853703274977162974182860276538742444782087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree080.table
  base := (12104857102411317279122484446445300442641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-35517278887959615090973123730546157000000000000)
      constant := (711770547919971121477704924792234265389689517883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444358010249688632753/100000000000000000000)
  centralHi := (222179005124844316377/50000000000000000000)
  directionLo := (447161558630686860879/100000000000000000000)
  directionHi := (5589519482883585761/1250000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree081.table
  base := (25192138308762637599601116163181568147749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-23911633450608912655736760283535538000000000000)
      constant := (484062499747323522193737537375767500359852187229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree081.table
  base := (25191817885881425643252853704199252894871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-23974213704611767799376318469651788000000000000)
      constant := (486561088385466725009772581294606830400270817791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447161558630686860879/100000000000000000000)
  centralHi := (5589519482883585761/1250000000000000000)
  directionLo := (224973819455169059721/50000000000000000000)
  directionHi := (449947638910338119443/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree082.table
  base := (818321797506204255053452533903774790479/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-326792996561508841134661856562094113000000000000)
      constant := (6698665539295683153945875565743000737150851809488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree082.table
  base := (13093002563079175566550843954186542957899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-36405362225875688307155831678409207000000000000)
      constant := (748137189127091122024022510832736034940015326137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224973819455169059721/50000000000000000000)
  centralHi := (449947638910338119443/100000000000000000000)
  directionLo := (113179143398019350223/25000000000000000000)
  directionHi := (452716573592077400893/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree083.table
  base := (27192528098140834449804073680050696464247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-661557883079594722833754898592916926000000000000)
      constant := (13728994493647758191203923038315978484462216572549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree083.table
  base := (13596130660405724289557870656554378405519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-36849403894833724915247185652340732000000000000)
      constant := (766657211202124287346968258747914394081249356197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113179143398019350223/25000000000000000000)
  centralHi := (452716573592077400893/100000000000000000000)
  directionLo := (11386716884403995319/2500000000000000000)
  directionHi := (455468675376159812761/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree084.table
  base := (2821081667665057397738165409174470143517/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (9178437253752087733801867297050000000000000)
      linear := (-759104051061419232877762000069893000000000000)
      constant := (15946346523246700726631635774016593502213684395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree084.table
  base := (220395103961536385094038883360394749731/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (249018)
      previous := (124509)
      next := (124509)
      square := (3059479084584029244600622432350000000000000)
      linear := (-253696908597222867505704351199131000000000000)
      constant := (5342868660321159979389389214303730950153926336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11386716884403995319/2500000000000000000)
  centralHi := (455468675376159812761/100000000000000000000)
  directionLo := (229102123785920229513/50000000000000000000)
  directionHi := (458204247571840459027/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree085.table
  base := (7310287801524474560233478980141185572751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-338750831496374401981308634765187163000000000000)
      constant := (7202190201820378968666688770032625738184184436634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree085.table
  base := (5848185844376751331477908236718605605587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-75474974465499596262859787200407564000000000000)
      constant := (1608741259105286551098262337457695424037111112405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229102123785920229513/50000000000000000000)
  centralHi := (458204247571840459027/100000000000000000000)
  directionLo := (460923584487536586967/100000000000000000000)
  directionHi := (57615448060942073371/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree086.table
  base := (30283520823534862036253332699494475843691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78440670000000000000000000000000000000000000000
      center := (658901628)
      previous := (329450814)
      next := (329450814)
      square := (8095381657809341381213246955998100000000000000)
      linear := (-685473552949325844527048454999103026000000000000)
      constant := (14748102718849570380842614880952277020647793731297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree086.table
  base := (3785414796691303391460754233144591829987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-38181528901707834739521247574135307000000000000)
      constant := (823564015999176488719500867115649901556475838724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460923584487536586967/100000000000000000000)
  centralHi := (57615448060942073371/12500000000000000000)
  directionLo := (46362697180039266269/10000000000000000000)
  directionHi := (463626971800392662691/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree087.table
  base := (7834478933958358334478859246375535990693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-38524746828105715838415535581546207000000000000)
      constant := (838658027906226386035068863848958461549312726318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree087.table
  base := (1958608195376651992830294175121786764911/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-12875190190221957115870867182688944000000000000)
      constant := (280993949402541292363457594706882909026829669048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46362697180039266269/10000000000000000000)
  centralHi := (463626971800392662691/100000000000000000000)
  directionLo := (466314686906561960053/100000000000000000000)
  directionHi := (233157343453280980027/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree088.table
  base := (32404327114331629557590584117918397654437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 648270000000000000000000000000000000000000000
      center := (5445468)
      previous := (2722734)
      next := (2722734)
      square := (66903980643052408109200388066100000000000000)
      linear := (-5796837461673387815338105999475706000000000000)
      constant := (127666162684096326685318680944195823964744187399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree088.table
  base := (3240415879485695816960442433211780018271/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 36015000000000000000000000000000000000000000
      center := (302526)
      previous := (151263)
      next := (151263)
      square := (3716887813502911561622243781450000000000000)
      linear := (-322889357352263702113255830760317000000000000)
      constant := (7129124978458136766859100079119168257358030065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466314686906561960053/100000000000000000000)
  centralHi := (233157343453280980027/50000000000000000000)
  directionLo := (468986999253420374963/100000000000000000000)
  directionHi := (117246749813355093741/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree089.table
  base := (8370686749963629700444184109091308043381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-354694611409528483110171005702644563000000000000)
      constant := (7901693101904005345613255283903537940819838941054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree089.table
  base := (16741296776518834108603860936811450831461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-39513653908581944563795309495929882000000000000)
      constant := (882490835145753528629435294002202893396020643543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468986999253420374963/100000000000000000000)
  centralHi := (117246749813355093741/25000000000000000000)
  directionLo := (471644170654838623313/100000000000000000000)
  directionHi := (235822085327419311657/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree090.table
  base := (34573168217088415497036442487434380623687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-26568930102801259510547155439778438000000000000)
      constant := (598636518634277745921670862238874593693174170927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree090.table
  base := (34573028346445325713424487760893260986371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (24403764)
      previous := (12201882)
      next := (12201882)
      square := (299828950289234865970860998370300000000000000)
      linear := (-26638463718359987447924442313240938000000000000)
      constant := (601721322260349607668509282760139641075021489291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471644170654838623313/100000000000000000000)
  centralHi := (235822085327419311657/50000000000000000000)
  directionLo := (237143227795278476839/50000000000000000000)
  directionHi := (474286455590556953679/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree091.table
  base := (35675584297387208848012609176628817351363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1600830000000000000000000000000000000000000000
      center := (13446972)
      previous := (6723486)
      next := (6723486)
      square := (165211870567537579208433611346900000000000000)
      linear := (-14802714341473694843861313925362174000000000000)
      constant := (337285816979339334337370698061568104968058243129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree091.table
  base := (8918864204377047398670594828106214313353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 88935000000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (9178437253752087733801867297050000000000000)
      linear := (-824525249928530975101592192730468000000000000)
      constant := (18834644170555817300645752023166922842983219622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237143227795278476839/50000000000000000000)
  centralHi := (474286455590556953679/100000000000000000000)
  directionLo := (476914101490631296323/100000000000000000000)
  directionHi := (119228525372657824081/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree092.table
  base := (9197497352295116059695278119729958786449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-366652446344394043956817783905737613000000000000)
      constant := (8447421622325583107409117622870055183256289296166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree092.table
  base := (36789873236430787246996028636585992797147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-81691557830912108776138742835448914000000000000)
      constant := (1886875151097893143134275208778490135640259830761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476914101490631296323/100000000000000000000)
  centralHi := (119228525372657824081/25000000000000000000)
  directionLo := (119881837251462685733/25000000000000000000)
  directionHi := (479527349005850742933/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree093.table
  base := (37916378295234707511534373099321593997137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-82364086960596125386451861475578214000000000000)
      constant := (1918522288875336003423301686391305778428926715131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree093.table
  base := (18958136219604586039201222027927562685023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-13763273528138030332053575130551994000000000000)
      constant := (321400671571760532385828556481563051063815566983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119881837251462685733/25000000000000000000)
  centralHi := (479527349005850742933/100000000000000000000)
  directionLo := (241063216132481418517/50000000000000000000)
  directionHi := (96425286452992567407/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree094.table
  base := (2440921638505813725878518642311751589321/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-374624336300971084521248969374466313000000000000)
      constant := (8821288530245791606923222235133735261831923268056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree094.table
  base := (39054649771766217344146812934421117740253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-83467724506744255208504158731175014000000000000)
      constant := (1970381759656158826188333349837717488641048125439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241063216132481418517/50000000000000000000)
  centralHi := (96425286452992567407/20000000000000000000)
  directionLo := (484711579119484841683/100000000000000000000)
  directionHi := (121177894779871210421/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree095.table
  base := (20102544449542263670701057271727942261259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-378610281279259604803464562108830663000000000000)
      constant := (9011236296488363582780165794795408919869447100353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree095.table
  base := (20102500519801346705689161328659351493397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4357815000000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (449743425433852298956291497555450000000000000)
      linear := (-42177903922330164212343433339519032000000000000)
      constant := (1006404169059454853338932444414185354740639569511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484711579119484841683/100000000000000000000)
  centralHi := (121177894779871210421/25000000000000000000)
  directionLo := (97456602275365095679/20000000000000000000)
  directionHi := (121820752844206369599/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree096.table
  base := (8273480498471057933161270654330042643267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-85021383612788472241262256631821114000000000000)
      constant := (2045154129679917277590615037699402218781468581605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree096.table
  base := (10341830615604883831729777491752918046151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (12201882)
      previous := (6100941)
      next := (6100941)
      square := (149914475144617432985430499185150000000000000)
      linear := (-14207315197096066940144929104483519000000000000)
      constant := (342613960254007840305963232971168323007371669342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97456602275365095679/20000000000000000000)
  centralHi := (121820752844206369599/25000000000000000000)
  directionLo := (7653764765974877899/1562500000000000000)
  directionHi := (489840945022392185537/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree097.table
  base := (170166734093704371660946104372398550003/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39220335000000000000000000000000000000000000000
      center := (329450814)
      previous := (164725407)
      next := (164725407)
      square := (4047690828904670690606623477999050000000000000)
      linear := (-386582171235836645367895747577559363000000000000)
      constant := (9397160377840404301980658427219933383115797775125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree097.table
  base := (1701664425328819074984544749869232461751/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8715630000000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (899486850867704597912582995110900000000000000)
      linear := (-86131974520492474857052282574764164000000000000)
      constant := (2099008026902158944889925691877835448051527170325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell073.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7653764765974877899/1562500000000000000)
  centralHi := (489840945022392185537/100000000000000000000)
  directionLo := (492385590431313351899/100000000000000000000)
  directionHi := (4923855904313133519/1000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4777
  qDenominator := 9702
  table := BinomialMassData.Q4777_9702.Degree098.table
  base := (43727928861831362825336615367070622522973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32670000000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (3371670827908930187927216558100000000000000)
      linear := (-325337872731466193794345139785026000000000000)
      constant := (7990950992963683788744103215659917723782552791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4777_9702.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree098.table
  base := (21863931240726343922856379871318863955161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1815000000000000000000000000000000000000000
      center := (15246)
      previous := (7623)
      next := (7623)
      square := (187315045994940565995956475450000000000000)
      linear := (-18121628042150884646654516976807000000000000)
      constant := (446226807908593331837791709392649747615723443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell073.Kernel098
